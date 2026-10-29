import Lean
-- import vc.token
-- set_option pp.all true in

-- set_option trace.Elab.step true in
-- set_option trace.Elab.definition true in
-- set_option trace.Elab.command true in
-- set_option pp.all true in

-- syntax source_text : command
-- syntax simple_identifier : command
-- syntax source_text : command
-- syntax description : command

-- syntax "source_text[" description* "]" : source_text
-- syntax "description[" module_declaration "]" : description
-- syntax "module_declaration["
--   module_keyword
--   module_identifier
--   (module_parameter_port_list)?
--   (list_of_port_declarations)?
--   ";"
--   module_item*
--   "endmodule"  "]" : module_declaration
-- syntax "module_identifier[" identifier "]": module_identifier
-- syntax "identifier[" simple_identifier "]" : identifier
-- syntax ("module" <|> "macromodule"): module_keyword

-- syntax "simple_identifier[" ident "]" : simple_identifier
-- macro_rules
--   | `(simple_identifier[ $id ]) => `( def $id := 2 )

-- macro_rules
--   | `(command|source_text[ ])
--     => `(tactic| skip )

-- macro_rules
--   | `(command|source_text[ $a:description $b:description* ])
--     => `(  $a:description  )

-- macro_rules
--   | `(command|description[ $a ]) => `(tactic| skip )

declare_syntax_cat aa
declare_syntax_cat b
declare_syntax_cat c
syntax aa : command
-- syntax b : command

syntax b  : aa
syntax c  : b
syntax ident  : c
syntax "aa[" aa "]"  : command
syntax "b[" b "]"  : command
syntax "c[" c "]"  : command
macro_rules
  | `(command|aa[ $b: b ]) => `( b[ $b ] )
  | `(command|b[ $c: c ]) => `( c[ $c ] )
  | `(command|c[ $ident: ident ]) => `( def $ident := 2 )

set_option pp.rawOnError true
set_option trace.Elab.step true
set_option trace.Elab.definition true
set_option trace.Elab.command true

simple_identifier[ D ]

source_text[
  module D (
      input wire clk,
      input wire in,
      output reg out
  );
      always @(posedge clk) begin
          out <= in;
      end
  endmodule

  module D (
      input wire clk,
      input wire in,
      output reg out
  );
      always @(posedge clk) begin
          out <= in;
      end
  endmodule
]
