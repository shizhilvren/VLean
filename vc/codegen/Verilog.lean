import Lean
import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules
import vc.runtime.Signals

def portTypeName (pd : VL.port_declaration) : Lean.Name :=
  match pd with
  | .input_declaration _ => ``Wire
  | .output_declaration (.output _ _) => ``Wire
  | .output_declaration (.output_reg _) => ``Reg

def portNamesWithTypes (pd : VL.port_declaration) : List (Lean.Name × Lean.Name) :=
  let ports := match pd with
    | .input_declaration declaration => declaration.list_of_port_identifiers
    | .output_declaration (.output _ ports) => ports
    | .output_declaration (.output_reg ports) => ports
  match ports with
  | .port_identifier first rest =>
    (first :: rest).map fun port =>
      match port with
      | .identifier id => (id.getName, portTypeName pd)

def oneInput (pd : VL.port_declaration) : List Lean.Name :=
  match pd with
  | .input_declaration _ => (portNamesWithTypes pd).map Prod.fst
  | .output_declaration _ => []

def oneOutput (pd : VL.port_declaration) : List (Lean.Name × Lean.Name) :=
  match pd with
  | .output_declaration _ => portNamesWithTypes pd
  | .input_declaration _ => []

def outputPorts (ports : Option VL.list_of_port_declarations) :
    List (Lean.Name × Lean.Name) :=
  match ports with
  | some (.port_declaration first rest) => (first :: rest).flatMap oneOutput
  | _ => []

def inputPorts (ports : Option VL.list_of_port_declarations) :
    List (Lean.Name × Lean.Name) :=
  match ports with
  | some (.port_declaration first rest) =>
    (first :: rest).flatMap fun pd =>
      match pd with
      | .input_declaration _ => portNamesWithTypes pd
      | .output_declaration _ => []
  | _ => []

def inputPortNames (ports : Option VL.list_of_port_declarations) : List Lean.Name :=
  (inputPorts ports).map Prod.fst

structure ModuleAssignment where
  target : Lean.Name
  dependencies : List Lean.Name
  value : VL.expression
  clock : Option VL.expression

def expressionVariables (expr : VL.expression) : List Lean.Name :=
  match expr with
  | .identifier id => [id.getName]

partial def statementAssignments (stmt : VL.statement)
    (clock : Option VL.expression := none) : Except String (List ModuleAssignment) := do
  match stmt with
  | .nonblocking_assignment assignment =>
    let target := match assignment.variable_lvalue with
      | .identifier id => id.getName
    return [ModuleAssignment.mk target (expressionVariables assignment.expression)
      assignment.expression clock]
  | .seq_block (.statements statements) =>
    return (← statements.mapM fun statement => statementAssignments statement clock).flatten
  | .procedural_timing_control_statement timing =>
    if clock.isSome then
      throw "nested event controls are not supported"
    let .event_control (.event_expression (.posedge edge)) := timing.procedural_timing_control
    let .statement body := timing.statement_or_null
    statementAssignments body (some edge)

def moduleItemAssignments (item : VL.module_item) : Except String (List ModuleAssignment) :=
  match item with
  | .module_or_generate_item (.always_construct (.always stmt)) => statementAssignments stmt

def code_gen_module_declaration (module_declaration : VL.module_declaration) : Lean.Elab.Command.CommandElabM Unit := do
  let name := module_declaration.module_identifier
  let name := match name with
  | VL.module_identifier.identifier id =>
    id.getName
  let codeA := Lean.mkIdent name

  let input_ver := inputPorts module_declaration.list_of_port_declarations
  let output_ver := outputPorts module_declaration.list_of_port_declarations
  let assignments ← match module_declaration.module_items.mapM moduleItemAssignments with
    | .ok items => pure items.flatten
    | .error message => throwError "{message}"
  let mut assigned : List Lean.Name := []
  for assignment in assignments do
    unless output_ver.any (fun port => port.1 == assignment.target && port.2 == ``Reg) do
      throwError "assignment target must be an output reg: {assignment.target}"
    if assigned.contains assignment.target then
      throwError "multiple assignments to {assignment.target} are not supported"
    assigned := assignment.target :: assigned
    unless assignment.clock.isSome do
      throwError "assignment to {assignment.target} requires a posedge event"
    let clockVariables := assignment.clock.toList.flatMap expressionVariables
    for dependency in assignment.dependencies ++ clockVariables do
      unless input_ver.any (fun port => port.1 == dependency) do
        throwError "only input signals are supported as dependencies: {dependency}"
  let inputs ← input_ver.toArray.mapM fun (portName, typeName) => do
    let port := Lean.mkIdent portName
    let portType : Lean.TSyntax `term := Lean.mkIdent typeName
    `(bracketedBinder| ($port:ident : $portType))

  let rec outputsToLean (ports : List (Lean.Name × Lean.Name)) :
      Lean.Elab.Command.CommandElabM (Lean.TSyntax `term × Lean.TSyntax `term) := do
    match ports with
    | [] => return (← `(term| Unit), ← `(term| ()))
    | (name, typeName) :: rest =>
      let portName := Lean.mkIdent name
      let portType : Lean.TSyntax `term := Lean.mkIdent typeName
      let value : Lean.TSyntax `term := portName
      match rest with
      | [] => return (portType, value)
      | _ :: _ =>
        let (restType, restValue) ← outputsToLean rest
        return (← `(term| $portType × $restType), ← `(term| ($value, $restValue)))

  let (outputs, codeB) ← outputsToLean output_ver
  let mut codeB := codeB
  for (name, typeName) in output_ver.reverse do
    let portName := Lean.mkIdent name
    let portType : Lean.TSyntax `term := Lean.mkIdent typeName
    let value ← match assignments.find? (fun assignment => assignment.target == name) with
      | none => `(term| fun _ => Bool.false)
      | some assignment =>
        match assignment.clock, assignment.value with
        | some (.identifier clock), .identifier dataSignal =>
          let clockName := Lean.mkIdent clock.getName
          let inputName := Lean.mkIdent dataSignal.getName
          `(term| posedgeSignal $clockName:ident $inputName:ident)
        | none, _ => throwError "expected a posedge event"
    codeB ← `(term| let $portName:ident : $portType := $value
                   $codeB)
  let code ← `(command| def $codeA:ident $[$inputs:bracketedBinder]* : $outputs := $codeB)
  Lean.Elab.Command.elabCommand code

def code_gen_description (description : VL.description) : Lean.Elab.Command.CommandElabM Unit := do
  match description with
  | VL.description.module_declaration md =>
    code_gen_module_declaration md

def code_gen_source_text (source : VL.source_text) : Lean.Elab.Command.CommandElabM Unit := do
  match source with
  | VL.source_text.description [] =>
    let codeB := Lean.mkNullNode #[]
    Lean.Elab.Command.elabCommand codeB
  | VL.source_text.description (h::t) =>
    code_gen_description h
    code_gen_source_text (VL.source_text.description t)

syntax (name := verilogCommand) "verilog[" source_text "]" : command

@[command_elab verilogCommand]
unsafe def elabVerilog : Lean.Elab.Command.CommandElab := fun stx => do
  match stx with
  | `(command| verilog[ $code:source_text ]) =>
    let source ← Lean.Elab.Command.liftTermElabM do
      let term ← `(term| source_text[ $code:source_text ])
      let expr ← Lean.Elab.Term.elabTermEnsuringType term (Lean.mkConst ``VL.source_text)
      let expr ← Lean.instantiateMVars expr
      if expr.hasMVar || expr.hasFVar || expr.hasLooseBVars then
        throwError "expected a closed VL.source_text"
      Lean.Meta.evalExpr VL.source_text (Lean.mkConst ``VL.source_text) expr
    code_gen_source_text source
  | _ => Lean.Elab.throwUnsupportedSyntax
