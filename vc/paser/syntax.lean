import Lean
import Lean.Parser.Basic
import vc.paser.token
import vc.paser.to_char
import vc.paser.syntax_tool
open Lean Parser




-- A.1.2 Verilog source text
syntax ascii_spaces (atomic(description))* ascii_spaces : source_text
syntax module_declaration : description
syntax keyword_module : module_keyword
syntax keyword_macromodule : module_keyword
syntax ascii_spaces module_keyword ascii_spaces module_identifier ascii_spaces
  (list_of_port_declarations)? ascii_spaces char_semicolon ascii_spaces
  (atomic(module_item))* keyword_endmodule ascii_spaces : module_declaration

-- A.1.3 Module parameters and ports
syntax input_declaration : port_declaration
syntax output_declaration : port_declaration
syntax ident : output_declaration
syntax ascii_spaces char_open_paren ascii_spaces char_close_paren ascii_spaces : list_of_port_declarations
syntax ascii_spaces char_open_paren ascii_spaces port_declaration
  (atomic(ascii_spaces char_comma ascii_spaces port_declaration))*
  ascii_spaces char_close_paren ascii_spaces : list_of_port_declarations
syntax keyword_input ascii_spaces (net_type)? ascii_spaces list_of_port_identifiers : input_declaration
syntax keyword_output ascii_spaces (net_type)? ascii_spaces list_of_port_identifiers : output_declaration
syntax keyword_output ascii_spaces keyword_reg ascii_spaces list_of_port_identifiers : output_declaration
syntax keyword_wire : net_type
syntax port_identifier
  (atomic(ascii_spaces char_comma ascii_spaces
    notFollowedBy(keyword_input <|> keyword_output) port_identifier))* : list_of_port_identifiers

-- A.1.4 Module items
syntax module_or_generate_item : module_item
syntax always_construct : module_or_generate_item

-- A.6.2 Procedural blocks and assignments
syntax ascii_spaces keyword_always ascii_spaces statement ascii_spaces : always_construct
syntax variable_lvalue ascii_spaces char_less char_equal ascii_spaces expression : nonblocking_assignment

-- A.6.3 Parallel and sequential blocks
syntax ascii_spaces keyword_begin ascii_spaces (atomic(statement))* keyword_end ascii_spaces : seq_block

-- A.6.4 Statements
syntax conditional_statement : statement
syntax procedural_timing_control_statement : statement
syntax seq_block : statement
syntax ascii_spaces nonblocking_assignment ascii_spaces char_semicolon ascii_spaces : statement

syntax statement : statement_or_null

-- A.6.5 Timing control statements
syntax procedural_timing_control ascii_spaces statement_or_null : procedural_timing_control_statement
syntax event_control : procedural_timing_control
syntax ascii_spaces char_at ascii_spaces char_open_paren ascii_spaces event_expression ascii_spaces char_close_paren : event_control
syntax keyword_posedge ascii_spaces expression : event_expression
syntax keyword_negedge ascii_spaces expression : event_expression
syntax event_expression atomic(ascii_spaces keyword_or ascii_spaces event_expression) : event_expression

-- A.6.6 Conditional statements
syntax ascii_spaces keyword_if ascii_spaces char_open_paren ascii_spaces expression ascii_spaces char_close_paren ascii_spaces statement_or_null (atomic(keyword_else ascii_spaces statement_or_null))? : conditional_statement

-- A.8.3 Expressions
syntax primary : expression
syntax identifier : expression
syntax unary_operator primary : expression
syntax unary_operator ascii_spaces primary : expression
syntax char_open_paren ascii_spaces expression ascii_spaces char_close_paren : expression

-- A.8.4 Primaries
syntax number : primary
syntax hierarchical_identifier : primary

-- A.8.5 Expression left-side values
syntax identifier : variable_lvalue
syntax identifier : hierarchical_identifier

-- A.8.6 Operators
syntax char_! : unary_operator
syntax char_' (char_b <|> char_B) : binary_base

-- A.8.7 Numbers
syntax (char_x <|> char_X) : x_digit
syntax (char_z <|> char_Z <|> char_?) : z_digit

syntax (char_0 <|> char_1) : binary_digit
syntax x_digit : binary_digit
syntax z_digit : binary_digit

syntax binary_digit (binary_digit <|> char__)* : binary_value

syntax (size)? binary_base binary_value : binary_number
syntax non_zero_unsigned_number : size
syntax non_zero_decimal_digit (decimal_digit <|> char__)* : non_zero_unsigned_number

syntax char_0 : decimal_digit
syntax non_zero_decimal_digit : decimal_digit

syntax (char_1 <|> char_2 <|> char_3 <|> char_4 <|> char_5 <|> char_6 <|> char_7 <|> char_8 <|> char_9) : non_zero_decimal_digit

syntax binary_number : number

-- A.9.3 Identifiers
syntax identifier : port_identifier
syntax identifier : module_identifier
syntax ident : identifier
syntax simple_identifier : identifier
syntax
  (ascii_upper_alpha <|> ascii_lower_alpha <|> char__)
  (ascii_upper_alpha <|> ascii_lower_alpha <|>
   decimal_digit <|> char__ <|> char_dollor)* : simple_identifier
