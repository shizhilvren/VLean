import Lean
import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules


def code_gen (_source : VL.source_text) : Lean.Elab.Command.CommandElabM Unit := do
  let nameA := Lean.mkIdent `a
  let nameB := Lean.mkIdent `b
  let codeA ← `(command| def $nameA:ident (value : Nat) : Nat := value + 1)
  let codeB ← `(command| def $nameB:ident (value : Nat) : Nat := value + 2)
  Lean.Elab.Command.elabCommand codeA
  Lean.Elab.Command.elabCommand codeB

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
    code_gen source
  | _ => Lean.Elab.throwUnsupportedSyntax

namespace generatedFunctions

verilog[
  module generated_example(input wire x);
  endmodule
]

#check a
#print b

end generatedFunctions

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (`generatedFunctions).isPrefixOf name then
      Lean.logInfo m!"{name}"
#print generatedFunctions.b

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
