import Lean
import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules
import vc.runtime.Signals
-- set_option trace.Meta.synthInstance true

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
  event : Option VL.event_expression := none
  guards : List (VL.expression × Bool) := []

def expressionVariables (expr : VL.expression) : List Lean.Name :=
  match expr with
  | .identifier id => [id.getName]
  | .primary (.hierarchical_identifier (.identifier id)) => [id.getName]
  | .primary (.number _) => []
  | .unary_operator _ (.hierarchical_identifier (.identifier id)) => [id.getName]
  | .unary_operator _ (.number _) => []

def eventVariables : VL.event_expression → List Lean.Name
  | .posedge value | .negedge value => expressionVariables value
  | .or left right => eventVariables left ++ eventVariables right

partial def statementAssignments (stmt : VL.statement)
    (clock : Option VL.expression := none)
    (event : Option VL.event_expression := none)
    (guards : List (VL.expression × Bool) := []) : Except String (List ModuleAssignment) := do
  match stmt with
  | .nonblocking_assignment assignment =>
    let target := match assignment.variable_lvalue with
      | .identifier id => id.getName
    return [ModuleAssignment.mk target (expressionVariables assignment.expression)
      assignment.expression clock event guards]
  | .seq_block (.statements statements) =>
    return (← statements.mapM fun statement => statementAssignments statement clock event guards).flatten
  | .conditional_statement conditional =>
    let .statement thenBody := conditional.then_stmt
    let thenAssignments ← statementAssignments thenBody clock event (guards ++ [(conditional.cond, true)])
    let elseAssignments ← match conditional.else_stmt with
      | none => pure []
      | some (.statement body) =>
        statementAssignments body clock event (guards ++ [(conditional.cond, false)])
    return thenAssignments ++ elseAssignments
  | .procedural_timing_control_statement timing =>
    if event.isSome || clock.isSome then
      throw "nested event controls are not supported"
    let .event_control (.event_expression edge) := timing.procedural_timing_control
    let .statement body := timing.statement_or_null
    let clock := match edge with
      | .posedge value => some value
      | _ => none
    statementAssignments body clock (some edge) guards

def expressionTerm (value : VL.expression) : Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  let primaryTerm (value : VL.primary) : Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
    match value with
    | .hierarchical_identifier (.identifier id) => return Lean.mkIdent id.getName
    | .number (.binary_number number) =>
      if number.size.any (· != 1) || !number.binary_value.binary_digits.isEmpty then
        throwError "only single-bit binary constants are supported"
      match number.binary_value.binary_digit with
      | .char_0 => `(term| fun _ : Nat => Bool.false)
      | .char_1 => `(term| fun _ : Nat => Bool.true)
      | _ => throwError "x/z constants are not supported by the Bool runtime"
  match value with
  | .identifier id => return Lean.mkIdent id.getName
  | .primary value => primaryTerm value
  | .unary_operator .not value =>
    let signal ← primaryTerm value
    `(term| fun time : Nat => !($signal time))

partial def eventTerm (event : VL.event_expression) : Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  match event with
  | .posedge value =>
    let value ← expressionTerm value
    `(term| postedge $value)
  | .negedge value =>
    let value ← expressionTerm value
    `(term| negedge $value)
  | .or left right =>
    let left ← eventTerm left
    let right ← eventTerm right
    `(term| fun time : Nat => $left time || $right time)

def guardsTerm (guards : List (VL.expression × Bool)) :
    Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  let mut result ← `(term| fun _ : Nat => Bool.true)
  for (condition, positive) in guards do
    let condition ← expressionTerm condition
    let condition ← if positive then pure condition else `(term| fun time : Nat => !($condition time))
    result ← `(term| fun time : Nat => $result time && $condition time)
  return result

def moduleItemAssignments (item : VL.module_item) : Except String (List ModuleAssignment) :=
  match item with
  | .module_or_generate_item (.always_construct (.always stmt)) => statementAssignments stmt

structure StatementCode where
  data : Lean.TSyntax `term
  enabled : Lean.TSyntax `term
  event : Option (Lean.TSyntax `term) := none

abbrev StatementBindings := Array (Lean.TSyntax `ident × Lean.TSyntax `term)

def bindStatementTerm (value : Lean.TSyntax `term) :
    StateT StatementBindings Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  let fresh ← liftM (Lean.Elab.Command.liftCoreM (Lean.mkFreshUserName `statement))
  let name := Lean.mkIdent fresh
  modify fun bindings => bindings.push (name, value)
  return name

def closeStatementTerm (bindings : StatementBindings) (value : Lean.TSyntax `term) :
    Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  bindings.foldrM (fun (name, definition) body =>
    `(term| let $name:ident := $definition; $body)) value

partial def statementTermAux (stmt : VL.statement) (target : Lean.Name)
    (previous : StatementCode) :
    StateT StatementBindings Lean.Elab.Command.CommandElabM StatementCode := do
  let code ← match stmt with
  | .nonblocking_assignment assignment =>
    let .identifier identifier := assignment.variable_lvalue
    if identifier.getName != target then
      pure previous
    else
      pure { previous with
        data := ← expressionTerm assignment.expression
        enabled := ← `(term| fun _ : Nat => Bool.true) }
  | .seq_block (.statements statements) =>
    statements.foldlM (fun code statement => statementTermAux statement target code) previous
  | .conditional_statement conditional =>
    let condition ← bindStatementTerm (← expressionTerm conditional.cond)
    let .statement thenBody := conditional.then_stmt
    let thenCode ← statementTermAux thenBody target previous
    let elseCode ← match conditional.else_stmt with
      | none => pure previous
      | some (.statement elseBody) => statementTermAux elseBody target previous
    pure {
      data := ← `(term| «if» $condition $(thenCode.data) $(elseCode.data))
      enabled := ← `(term| «if» $condition $(thenCode.enabled) $(elseCode.enabled))
      event := thenCode.event.or elseCode.event }
  | .procedural_timing_control_statement timing =>
    if previous.event.isSome then
      throwError "nested event controls are not supported"
    let .event_control (.event_expression event) := timing.procedural_timing_control
    let .statement body := timing.statement_or_null
    let event ← bindStatementTerm (← eventTerm event)
    statementTermAux body target { previous with event := some event }
  let value ← bindStatementTerm (← `(term| ($(code.data), $(code.enabled))))
  return { code with
    data := ← `(term| $value.1)
    enabled := ← `(term| $value.2) }

def statementTerm (stmt : VL.statement) (target : Lean.Name)
    (previous : StatementCode) : Lean.Elab.Command.CommandElabM StatementCode := do
  let (code, bindings) ← (statementTermAux stmt target previous).run #[]
  return {
    data := ← closeStatementTerm bindings code.data
    enabled := ← closeStatementTerm bindings code.enabled
    event := ← code.event.mapM (closeStatementTerm bindings) }

partial def statementAlwaysWrites (stmt : VL.statement) (target : Lean.Name) : Bool :=
  match stmt with
  | .nonblocking_assignment assignment =>
    let .identifier identifier := assignment.variable_lvalue
    identifier.getName == target
  | .seq_block (.statements statements) =>
    statements.any (fun statement => statementAlwaysWrites statement target)
  | .conditional_statement conditional =>
    let .statement thenBody := conditional.then_stmt
    statementAlwaysWrites thenBody target &&
      conditional.else_stmt.any (fun (.statement body) => statementAlwaysWrites body target)
  | .procedural_timing_control_statement timing =>
    let .statement body := timing.statement_or_null
    statementAlwaysWrites body target

def code_gen_statement (stmt : VL.statement) (target : Lean.Name) :
    Lean.Elab.Command.CommandElabM (Lean.TSyntax `term) := do
  let initial ← `(term| fun _ : Nat => Bool.false)
  let (code, bindings) ← (statementTermAux stmt target
    { data := initial, enabled := initial }).run #[]
  let some event := code.event | throwError "assignment to {target} requires an edge event"
  let result ← if statementAlwaysWrites stmt target then
    `(term| «always» $(code.data) Bool.false $event)
  else
    `(term| let rec result (time : Nat) : Bool :=
      match time with
      | 0 => Bool.false
      | previous + 1 =>
        if $event (previous + 1) then
          «if» $(code.enabled) $(code.data) (fun _ => result previous) previous
        else result previous
      result)
  closeStatementTerm bindings result

def code_gen_module_declaration (module_declaration : VL.module_declaration) : Lean.Elab.Command.CommandElabM Unit := do
  let name := module_declaration.module_identifier
  let name := match name with
  | VL.module_identifier.identifier id =>
    id.getName
  let codeA := Lean.mkIdent name

  let input_ver := inputPorts module_declaration.list_of_port_declarations
  let output_ver := outputPorts module_declaration.list_of_port_declarations
  let assignmentGroups ← match module_declaration.module_items.mapM moduleItemAssignments with
    | .ok items => pure items
    | .error message => throwError "{message}"
  let assignments := assignmentGroups.flatten
  let mut assigned : List Lean.Name := []
  for group in assignmentGroups do
    let targets := (group.map (·.target)).eraseDups
    for target in targets do
      if assigned.contains target then
        throwError "multiple always blocks drive {target}"
    assigned := assigned ++ targets
  Lean.logInfo m!"Assignment groups: {assigned}"
  for assignment in assignments do
    unless output_ver.any (fun port => port.1 == assignment.target && port.2 == ``Reg) do
      throwError "assignment target must be an output reg: {assignment.target}"
    unless assignment.event.isSome do
      throwError "assignment to {assignment.target} requires an edge event"
    let clockVariables := assignment.event.toList.flatMap eventVariables
    let guardVariables := assignment.guards.flatMap (fun guard => expressionVariables guard.1)
    for dependency in assignment.dependencies ++ clockVariables ++ guardVariables do
      unless input_ver.any (fun port => port.1 == dependency) do
        throwError "only input signals are supported as dependencies: {dependency}"
  let inputs ← input_ver.toArray.mapM fun (portName, typeName) => do
    let port := Lean.mkIdent portName
    let portType : Lean.TSyntax `term := Lean.mkIdent typeName
    `(bracketedBinder| ($port:ident : $portType))
  Lean.logInfo m!"Input ports: {inputs}"


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
    let drivers := assignments.filter (fun assignment => assignment.target == name)
    let value ← match drivers with
      | [] => `(term| fun _ => Bool.false)
      | first :: _ =>
        let some item := (module_declaration.module_items.zip assignmentGroups).find?
          (fun (_, group) => group.any (fun assignment => assignment.target == first.target))
          | throwError "missing statement for {name}"
        let .module_or_generate_item (.always_construct (.always stmt)) := item.1
        code_gen_statement stmt name
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

macro "verilog[" source:term "]" : command =>
  `(command| run_cmd code_gen_source_text ($source : VL.source_text))

macro "verilog" checksum:str "[" source:asciiRaw "]" closing:str : command =>
  `(command| verilog[ascii_apply "source_text" $checksum:str [$source:asciiRaw] $closing:str])
