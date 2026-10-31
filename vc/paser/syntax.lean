import vc.paser.token

syntax description* : source_text
syntax module_declaration : description
syntax
  module_keyword
  module_identifier
  (list_of_port_declarations)?
  ";"
  module_item*
  "endmodule" : module_declaration
syntax "(" port_declaration (atomic("," port_declaration))* ")" : list_of_port_declarations
syntax "(" ")" : list_of_port_declarations
syntax ("module" <|> "macromodule"): module_keyword
syntax input_declaration  : port_declaration
syntax output_declaration : port_declaration
syntax "input" (net_type)? list_of_port_identifiers : input_declaration
syntax "output" (net_type)? list_of_port_identifiers : output_declaration
syntax "output" "reg" list_of_port_identifiers : output_declaration
syntax "wire" : net_type
syntax port_identifier (atomic(","  port_identifier ))*  : list_of_port_identifiers
syntax identifier : port_identifier
syntax identifier : module_identifier
syntax ident : identifier

syntax ident : output_declaration
syntax ident : module_item
