namespace VL

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

structure module_declaration where
  module_keyword : module_keyword
  module_identifier : module_identifier
  list_of_port_declarations : Option list_of_port_declarations
  -- module_items : List module_item

inductive description
  | module_declaration (md: module_declaration): description

inductive source_text where
  | description (ds: List description): source_text


end VL
