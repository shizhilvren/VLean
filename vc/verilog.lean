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

def oneVer (pd : VL.port_declaration) : List Lean.Name :=
  match pd with
  | .input_declaration declaration =>
    match declaration.list_of_port_identifiers with
    | .port_identifier first rest =>
      (first :: rest).map fun port =>
        match port with
        | .identifier id => id.getName
  | .output_declaration _ => []

def inputPortNames (ports : Option VL.list_of_port_declarations) : List Lean.Name :=
  match ports with
  | some (.port_declaration first rest) => (first :: rest).flatMap oneVer
  | _ => []

example : inputPortNames (some (list_of_port_declarations[
    (input wire a,b, output reg c,d, input wire x,y)
  ])) = [`a, `b, `x, `y] := rfl

example : inputPortNames (some (list_of_port_declarations[()])) = [] := rfl
example : inputPortNames none = [] := rfl

def code_gen_module_declaration (module_declaration : VL.module_declaration) : Lean.Elab.Command.CommandElabM Unit := do
  let name := module_declaration.module_identifier
  let name := match name with
  | VL.module_identifier.identifier id =>
    id.getName
  let codeA := Lean.mkIdent name

  let input_ver := inputPortNames module_declaration.list_of_port_declarations
  let inputs ← input_ver.toArray.mapM fun portName => do
    let port := Lean.mkIdent portName
    `(bracketedBinder| ($port:ident : Wire))

  let codeB ← `(term| 0)
  let code ← `(command| def $codeA:ident $[$inputs:bracketedBinder]* : Nat := $codeB)
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

verilog[
  module no_inputs();
  endmodule
  module multiple_inputs(input wire x,y, output wire result, input wire z);
  endmodule
]

example : Nat := no_inputs
example : multiple_inputs = fun (_: Wire)  (_: Nat->Bool) (_: Wire) => 0 := by rfl
example : multiple_inputs (fun _ => Bool.false) (fun _ => Bool.true)
    (fun _ => Bool.false) = 0 := rfl



end portParameterTests

namespace generatedFunctions

verilog[
  module generated_example(input wire x);
  endmodule
]

#check generated_example
#print generated_example



example : (Nat → Bool) → Nat := generated_example

end generatedFunctions

run_cmd do
  let env ← Lean.getEnv
  for (name, a) in env.constants.toList do
    if (`generatedFunctions).isPrefixOf name then
      Lean.logInfo m!"{name}"
#print generatedFunctions.a

example : generatedFunctions.a 3 = 4 := rfl
example : generatedFunctions.b 3 = 5 := rfl




abbrev Wire := Nat -> Bool
abbrev Reg := Nat -> Bool

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

def a1 (v: VL.source_text) : Nat :=
  1

def a :Nat:= by
  let b := generatedFunctions.a

  exact 2

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
