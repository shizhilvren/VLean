import Lean
import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules

abbrev Wire := Nat → Bool
abbrev Reg := Nat → Bool
-- set_option pp.all true in
-- set_option trace.Elab.step true
-- set_option trace.Elab.definition true
-- set_option trace.Elab.command true

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

example : outputPorts (some (list_of_port_declarations[
    (input wire x, output reg a,b, output wire c,d, output e)
  ])) = [(`a, ``Reg), (`b, ``Reg), (`c, ``Wire), (`d, ``Wire), (`e, ``Wire)] := rfl

example : outputPorts (some (list_of_port_declarations[()])) = [] := rfl
example : outputPorts none = [] := rfl
example : outputPorts (some (list_of_port_declarations[(input wire x)])) = [] := rfl

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

example : inputPorts (some (list_of_port_declarations[
    (input a,b, output reg c, input wire x)
  ])) = [(`a, ``Wire), (`b, ``Wire), (`x, ``Wire)] := rfl

example : inputPortNames (some (list_of_port_declarations[
    (input wire a,b, output reg c,d, input wire x,y)
  ])) = [`a, `b, `x, `y] := rfl

example : inputPortNames (some (list_of_port_declarations[()])) = [] := rfl
example : inputPortNames none = [] := rfl

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

def posedgeSignal (clock dataSignal : Wire) : Reg
  | 0 => Bool.false
  | time + 1 =>
    if !clock time && clock (time + 1) then
      dataSignal time
    else
      posedgeSignal clock dataSignal time



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


-- set_option pp.all true in
-- set_option trace.Elab.step true
-- set_option trace.Elab.definition true
-- set_option trace.Elab.command true
namespace portParameterTests

run_cmd do
  let item := module_item[
    always @(posedge clk) begin
      out <= «in»;
    end
  ]
  match moduleItemAssignments item with
  | .ok [assignment] =>
    unless assignment.target == `out && assignment.dependencies == [Lean.Name.mkSimple "in"] &&
        assignment.clock.toList.flatMap expressionVariables == [`clk] &&
        expressionVariables assignment.value == [Lean.Name.mkSimple "in"] do
      throwError "incorrect module assignment extraction"
  | _ => throwError "expected one module assignment"

verilog[
  module no_inputs();
  endmodule
  module multiple_inputs(input wire x,y, output wire result, input wire z);
  endmodule
  module multiple_outputs(input wire x, output reg a,b, output wire c);
  endmodule
  module D(input wire clk, input wire «in», output reg out);
    always @(posedge clk) begin
      out <= «in»;
    end
  endmodule
]

theorem Dff_posedge (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) < clock n) :
  portParameterTests.D clock dataSignal n = dataSignal (n-1) := by
    cases n with
  | zero => simp at h
  | succ time =>
    cases previous : clock time <;>
      cases current : clock (time + 1) <;>
        simp_all [D, posedgeSignal]
    exact absurd clkEdge (by decide)

  -- rw [portParameterTests.D]
  -- rw [posedgeSignal.eq_def]
  -- -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- cases n with
  -- | zero => simp at h
  -- | succ time =>
  --   simp
  --   simp at clkEdge
  --   cases pre : clock time with
  --   | true =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --       exact absurd clkEdge (by decide)
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --   | false =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --       let f_eq_f :false = false :=by rfl
  --       simp





verilog[
    module Dff(input wire clk, input wire «in»,a, output reg out, output reg out1);
    always @(posedge clk) begin
      out <= «in» ;
      out1 <= a;
    end
  endmodule
]
#print D



example : Unit := no_inputs
example : Wire → Wire → Reg := D
example (clock dataSignal : Wire) : D clock dataSignal 0 = Bool.false := rfl
example (clock dataSignal : Wire) (time : Nat) :
    D clock dataSignal (time + 1) =
      (if !clock time && clock (time + 1) then dataSignal time else D clock dataSignal time) := rfl
example (clock dataSignal : Wire) (time : Nat)
    (low : clock time = Bool.false) (high : clock (time + 1) = Bool.true) :
    D clock dataSignal (time + 1) = dataSignal time := by
  simp [D, posedgeSignal, low, high]
example (clock dataSignal : Wire) (time : Nat) (stable : clock (time + 1) = clock time) :
  D clock dataSignal (time + 1) = D clock dataSignal time := by
  cases previous : clock time <;> simp [D, posedgeSignal, stable, previous]
example : (List.range 6).map (D (fun time => time % 2 == 1) (fun _ => Bool.true)) =
    [Bool.false, Bool.true, Bool.true, Bool.true, Bool.true, Bool.true] := by decide
example : multiple_inputs = fun (_: Wire) (_: Nat->Bool) (_: Wire) =>
    (fun _ => Bool.false : Wire) := rfl
example : multiple_inputs (fun _ => Bool.false) (fun _ => Bool.true)
    (fun _ => Bool.false) 0 = Bool.false := rfl
example : Wire → Reg × Reg × Wire := multiple_outputs
example : (multiple_outputs (fun _ => Bool.true)).1 0 = Bool.false := rfl
example : (multiple_outputs (fun _ => Bool.true)).2.1 0 = Bool.false := rfl
example : (multiple_outputs (fun _ => Bool.true)).2.2 0 = Bool.false := rfl



end portParameterTests

namespace generatedFunctions

verilog[
  module generated_example(input wire x);
  endmodule
]

#check generated_example
#print generated_example



example : (Nat → Bool) → Unit := generated_example

end generatedFunctions

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (`generatedFunctions).isPrefixOf name then
      Lean.logInfo m!"{name}"

set_option pp.rawOnError true
set_option trace.Elab.step true
set_option trace.Elab.definition true
set_option trace.Elab.command true

-- list_of_port_declarations[(input p1, input p2, input p3)]
-- simple_identifier[ D ]
-- #reduce source_text[
--   module abc(input a,b,c, input wire b, input wire c);
--   endmodule
-- ]

-- set_option trace.Elab.step true in
#reduce list_of_port_declarations[
  (input a)
]

#reduce input_declaration[
  input wire a,b,  c,d
]

#reduce list_of_port_identifiers[
  a,b,c,d
]

#reduce list_of_port_declarations[
  (input wire a,b,c)
]
#reduce list_of_port_declarations[
  (input wire a, input wire f)
]

#reduce list_of_port_declarations[
  (input wire a,b, output reg c,d, output wire f, e)
]

#reduce source_text[
  module abc(input wire a,b, output reg c,d, output wire f, e);
  endmodule
]


#reduce list_of_port_declarations[
  ()
]
#reduce port_declaration[
  input wire a,b,c
]

#reduce always_construct[
    always @(posedge clk) begin
        out <= in_;
    end
]

#reduce source_text[
  module abc(input wire a,b, output reg c,d, output wire f, e);
  always @(posedge clk) begin
        out <= in_;
    end
  endmodule
]

#reduce statement[
    out <= in_;
]

#reduce identifier[
  name_d
]
def e := identifier[
  name_d
]
#print e



verilog[
  module D(input wire clk, input wire «in», output reg out);
    always @(posedge clk) begin
      out <= «in»;
    end
  endmodule
]

theorem Dff_hold (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) = clock n) :
  D clock dataSignal n = D clock dataSignal (n-1) := by
  cases n with
  | zero => simp at h
  | succ time =>
    simp at clkEdge
    rw [D,posedgeSignal.eq_def]
    simp [clkEdge]


theorem Dff_posedge (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) < clock n) :
  D clock dataSignal n = dataSignal (n-1) := by
    cases n with
  | zero => simp at h
  | succ time =>
    cases previous : clock time <;>
      cases current : clock (time + 1) <;>
        simp_all [D, posedgeSignal]
    exact absurd clkEdge (by decide)

  -- rw [portParameterTests.D]
  -- rw [posedgeSignal.eq_def]
  -- -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- cases n with
  -- | zero => simp at h
  -- | succ time =>
  --   simp
  --   simp at clkEdge
  --   cases pre : clock time with
  --   | true =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --       exact absurd clkEdge (by decide)
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --   | false =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --       let f_eq_f :false = false :=by rfl
  --       simp
