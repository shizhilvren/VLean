import Lean
import Lean.Parser.Basic
import vc.paser.token


def char_' : Lean.Parser.Parser := Lean.Parser.rawCh '\''
def char_0 : Lean.Parser.Parser := Lean.Parser.rawCh '0'
def char_1 : Lean.Parser.Parser := Lean.Parser.rawCh '1'


-- A.1.2 Verilog source text
syntax description* : source_text
syntax module_declaration : description
syntax
  module_keyword
  module_identifier
  (list_of_port_declarations)?
  ";"
  module_item*
  "endmodule" : module_declaration
syntax ("module" <|> "macromodule"): module_keyword

-- A.1.3 Module parameters and ports
syntax "(" port_declaration (atomic("," port_declaration))* ")" : list_of_port_declarations
syntax "(" ")" : list_of_port_declarations
syntax input_declaration : port_declaration
syntax output_declaration : port_declaration
syntax ident : output_declaration
syntax "input" (net_type)? list_of_port_identifiers : input_declaration
syntax "output" (net_type)? list_of_port_identifiers : output_declaration
syntax "output" "reg" list_of_port_identifiers : output_declaration
syntax "wire" : net_type
syntax port_identifier (atomic("," port_identifier))* : list_of_port_identifiers

-- A.1.4 Module items
syntax module_or_generate_item : module_item
syntax always_construct : module_or_generate_item

-- A.6.2 Procedural blocks and assignments
syntax "always" statement : always_construct
syntax variable_lvalue "<=" expression : nonblocking_assignment

-- A.6.3 Parallel and sequential blocks
syntax "begin" statement* "end" : seq_block

-- A.6.4 Statements
syntax conditional_statement : statement
syntax procedural_timing_control_statement : statement
syntax seq_block : statement
syntax nonblocking_assignment ";" : statement

syntax statement : statement_or_null

-- A.6.5 Timing control statements
syntax procedural_timing_control statement_or_null : procedural_timing_control_statement
syntax event_control : procedural_timing_control
syntax "@" "(" event_expression ")" : event_control
syntax "posedge" expression : event_expression
syntax "negedge" expression : event_expression
syntax event_expression "or" event_expression : event_expression

-- A.6.6 Conditional statements
syntax "if" "(" expression ")" statement_or_null ("else" statement_or_null)? : conditional_statement

-- A.8.3 Expressions
syntax primary : expression
syntax identifier : expression
syntax unary_operator primary : expression
syntax "(" expression ")" : expression

-- A.8.4 Primaries
syntax number : primary

-- A.8.5 Expression left-side values
syntax identifier : variable_lvalue

-- A.8.6 Operators
syntax "!" : unary_operator

-- A.8.7 Numbers
syntax ("x" <|> "X") : x_digit
syntax ("z" <|> "Z" <|> "?") : z_digit
syntax (char_0 <|> char_1 <|> x_digit <|> z_digit) : binary_digit
syntax binary_digit (binary_digit <|> "_")* : binary_value

syntax char_' ("b" <|> "B") : binary_base
syntax binary_base binary_value : binary_number
syntax binary_number : number

-- A.9.3 Identifiers
syntax identifier : port_identifier
syntax identifier : module_identifier
syntax ident : identifier
