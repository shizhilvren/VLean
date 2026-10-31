import vc.paser.token

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
syntax procedural_timing_control_statement : statement
syntax seq_block : statement
syntax nonblocking_assignment ";" : statement

syntax statement : statement_or_null

-- A.6.5 Timing control statements
syntax procedural_timing_control statement_or_null : procedural_timing_control_statement
syntax event_control : procedural_timing_control
syntax "@" "(" event_expression ")" : event_control
syntax "posedge" expression : event_expression

-- A.8.3 Expressions
syntax identifier : expression

-- A.8.5 Expression left-side values
syntax identifier : variable_lvalue

-- A.9.3 Identifiers
syntax identifier : port_identifier
syntax identifier : module_identifier
syntax ident : identifier
