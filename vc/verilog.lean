import Lean
import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules

elab "verilog[" code:source_text "]" : term => do
  let stx ← `(term| source_text[ $code:source_text ])
  let expr ← Lean.Elab.Term.elabTermEnsuringType stx (Lean.mkConst ``VL.source_text)
  Lean.Meta.reduce expr

-- set_option pp.all true in
-- set_option trace.Elab.step true in
-- set_option trace.Elab.definition true in
-- set_option trace.Elab.command true in
-- set_option pp.all true in

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
  let b := a1 (verilog[
    module abc(input wire a,b, output reg c,d, output wire f, e);
    endmodule
  ])

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
def a := identifier[
  name_d
]
#print a
