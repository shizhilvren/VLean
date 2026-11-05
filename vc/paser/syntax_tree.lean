namespace VL

mutual
inductive identifier where
  | ident ( name:Lean.Name ): identifier

inductive module_keyword where
  | module : module_keyword
  | macromodule : module_keyword

inductive module_identifier where
  | identifier : identifier -> module_identifier

inductive port_identifier where
  | identifier (id: identifier) : port_identifier

inductive net_type where
  | wire : net_type

inductive list_of_port_identifiers where
  | port_identifier (id: port_identifier) (ids: List port_identifier) : list_of_port_identifiers

structure input_declaration where
  net_type : Option net_type
  list_of_port_identifiers : list_of_port_identifiers

inductive output_declaration where
  | output (net_type: Option net_type) (list_of_port_identifiers: list_of_port_identifiers) : output_declaration
  | output_reg (list_of_port_identifiers: list_of_port_identifiers) : output_declaration

inductive port_declaration where
  | input_declaration (id: input_declaration) : port_declaration
  | output_declaration (id: output_declaration) : port_declaration

inductive list_of_port_declarations where
  | port_declaration (hd: port_declaration) (tl: List port_declaration) : list_of_port_declarations
  | empty

inductive expression where
  | identifier (id: identifier) : expression
  | unary_operator (op: unary_operator) (value: primary) : expression
  | primary (value: primary) : expression

inductive event_expression where
  | posedge (e: expression) : event_expression
  | negedge (e: expression) : event_expression
  | or (lhs: event_expression) (rhs: event_expression) : event_expression

structure conditional_statement where
  cond : expression
  then_stmt : statement_or_null
  else_stmt : Option statement_or_null


inductive event_control where
  | event_expression (ee: event_expression) : event_control

inductive procedural_timing_control where
  | event_control (ec: event_control) : procedural_timing_control

inductive statement_or_null where
  | statement (s: statement) : statement_or_null

structure procedural_timing_control_statement where
  procedural_timing_control : procedural_timing_control
  statement_or_null : statement_or_null

inductive variable_lvalue where
  | identifier (id: identifier) : variable_lvalue

structure nonblocking_assignment where
  variable_lvalue : variable_lvalue
  expression : expression

inductive seq_block where
  | statements (stmts: List statement) : seq_block

inductive statement where
  | conditional_statement (cs: conditional_statement) : statement
  | procedural_timing_control_statement (ptcs: procedural_timing_control_statement) : statement
  | seq_block (sb: seq_block) : statement
  | nonblocking_assignment (nba: nonblocking_assignment) : statement

inductive always_construct where
  | always (stmt: statement) : always_construct

inductive module_or_generate_item where
  | always_construct (ac: always_construct) : module_or_generate_item

inductive module_item where
  | module_or_generate_item (item: module_or_generate_item) : module_item

structure module_declaration where
  module_keyword : module_keyword
  module_identifier : module_identifier
  list_of_port_declarations : Option list_of_port_declarations
  module_items : List module_item

inductive description
  | module_declaration (md: module_declaration): description

inductive source_text where
  | description (ds: List description): source_text

inductive primary where
  | number (n: number) : primary

inductive number where
  | binary_number (bn: binary_number) : number

structure binary_number where
  binary_base : binary_base
  binary_value : binary_value

inductive binary_base where
  | b : binary_base

inductive binary_digit where
  | char_0 : binary_digit
  | char_1 : binary_digit
  | x_digit (xd: x_digit) : binary_digit
  | z_digit (zd: z_digit) : binary_digit

inductive x_digit where
  | x : x_digit

inductive z_digit where
  | z : z_digit

structure binary_value where
  binary_digit : binary_digit
  binary_digits : List VL.binary_digit

inductive unary_operator where
  | not : unary_operator





end
def identifier.getName (id: identifier) : Lean.Name :=
  match id with
  | identifier.ident n => n



end VL
