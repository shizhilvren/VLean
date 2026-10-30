import vc.token
import Lean

-- set_option pp.all true in

-- set_option trace.Elab.step true in
-- set_option trace.Elab.definition true in
-- set_option trace.Elab.command true in
-- set_option pp.all true in

-- syntax simple_identifier : command
-- syntax source_text : command
-- syntax description : command

abbrev Wire := Nat -> Bool
abbrev Reg := Nat -> Bool

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

declare_syntax_cat source_text
syntax "source_text[" source_text "]" : term

declare_syntax_cat description
syntax "description[" description "]" : term

declare_syntax_cat module_declaration
syntax "module_declaration[" module_declaration "]" : term

declare_syntax_cat module_keyword
syntax "module_keyword[" module_keyword "]" : term

declare_syntax_cat module_identifier
syntax "module_identifier[" module_identifier "]" : term

token list_of_port_declarations
token_term list_of_port_declarations

token port_declaration
token_term port_declaration

token module_item
token_command module_item

token input_declaration
token_term input_declaration

token output_declaration
token_term output_declaration

token net_type
token_term net_type

token list_of_port_identifiers
token_term list_of_port_identifiers

token port_identifier
token_term port_identifier

token identifier
token_term identifier


syntax description* : source_text
syntax module_declaration : description
syntax
  module_keyword
  module_identifier
  (list_of_port_declarations)?
  ";"
  module_item*
  "endmodule" : module_declaration
syntax "(" port_declaration,* ")" : list_of_port_declarations
syntax ("module" <|> "macromodule"): module_keyword
syntax (input_declaration <|> output_declaration) : port_declaration
syntax "input" (net_type)? list_of_port_identifiers : input_declaration
syntax "output" (net_type)? list_of_port_identifiers : output_declaration
syntax "output" "reg" list_of_port_identifiers : output_declaration
syntax "wire" : net_type
syntax port_identifier,* : list_of_port_identifiers
syntax identifier : port_identifier
syntax identifier : module_identifier
syntax ident : identifier

syntax ident : input_declaration
syntax ident : output_declaration
syntax ident : module_item
-- syntax "module_identifier[" identifier "]": module_identifier
-- syntax "identifier[" simple_identifier "]" : identifier


-- macro_rules
--   | `(net_type[ wire ]) => `( Syntax.mkStrLit "Wire" )
-- macro_rules
--   | `(list_of_port_identifiers[ $_ ])
--     => `( #[] )

-- macro_rules
--   | `(input_declaration[ input $[$t]? $ps ])
--     => do
--       let mut commands := #[]
--       match t with
--       | none =>
--         commands := commands.push (← `(input_declaration[ input wire $ps ]))
--       | some t =>
--         commands := commands.push (← `( ( list_of_port_identifiers[ $ps ] : net_type[ $t ] ) ))
--       return Lean.mkNullNode commands


-- macro_rules
--   | `(output_declaration[ $d:ident ])
--     => `( def $d := "output_declaration" )


-- macro_rules
--   | `(port_declaration[ $d:input_declaration ])
--     => `( input_declaration[ $d ] )
--   | `(port_declaration[ $d:output_declaration ])
--     => `( output_declaration[ $d ] )

-- macro_rules
--   | `(module_parameter_port_list[ $_:ident ])
--     => `( Lean.mkNullNode #[])


-- macro_rules
--   | `(module_declaration[
--     $d:module_keyword
--     $i:module_identifier
--     $[$p:module_parameter_port_list]?
--     $[$l:list_of_port_declarations]?
--     ;
--     $[$items:module_item]*
--     endmodule ])
--     => do
--       let mut commands := #[
--         (← `(module_keyword[ $d ])),
--         (← `(module_identifier[ $i ]))
--       ]
--       for parameterPorts in p do
--         commands := commands.push (← `(module_parameter_port_list[ $parameterPorts ]))
--       for ports in l do
--         commands := commands.push (← `(list_of_port_declarations[ $ports ]))
--       for item in items do
--         commands := commands.push (← `(module_item[ $item ]))
--       return Lean.mkNullNode commands

macro_rules
  | `(term|source_text[ $ds:description* ])
    => do
      let items ← ds.mapM fun description => `(term| description[ $description ])
      `(term| VL.source_text.description [$items,*])

macro_rules
  | `(description[ $d:module_declaration ])
    =>do
      let item ← `(term| module_declaration[ $d ])
      `(term| VL.description.module_declaration $item)

macro_rules
  | `(term|module_keyword[ module ])
    => `(term| VL.module_keyword.module)
  | `(term|module_keyword[ macromodule ])
    => `(term| VL.module_keyword.macromodule)

macro_rules
  | `(term|module_identifier[ $d:identifier ])
    => do
      let d' ← `(term| identifier[ $d ])
      `(term| VL.module_identifier.identifier $d')

macro_rules
  | `(term|identifier[ $d:ident ])
    => do
      let name := Lean.Syntax.mkStrLit d.getId.toString
      `(term| VL.identifier.ident (Lean.Name.mkSimple $name))

macro_rules
  | `(term|module_declaration[
    $d:module_keyword
    $i:module_identifier
    $[$l:list_of_port_declarations]?
    ;
    -- $[$items:module_item]*
    endmodule ])
    => do
      let d' ← `(term| module_keyword[ $d ])
      let i' ← `(term| module_identifier[ $i ])
      `(term| VL.module_declaration.mk $d' $i' none)

macro_rules
  | `(list_of_port_declarations[ () ])
    => `( term| VL.list_of_port_declarations.empty )
  | `(list_of_port_declarations[ ( $p:port_declaration,*) ])
    => do
      let p'<- p.getElems.mapM fun p => `(term| port_declaration[ $p ])
      `(term| VL.list_of_port_declarations.port_declaration[ [$p',*] ] )

macro_rules
  | `(term|port_declaration[ $d:input_declaration ])
    => do
      let d' ← `(term| input_declaration[ $d ])
      `(term| VL.port_declaration.input_declaration $d')
  | `(term|port_declaration[ $d:output_declaration ])
    => do
      let d' ← `(term| output_declaration[ $d ])
      `(term| VL.port_declaration.output_declaration $d')

macro_rules
  | `(term|input_declaration[ input $[$t]? $ps ])
    => do
      let t' ← match t with
        | none => `(term| none)
        | some t => `(term| some (net_type[ $t ]))
      let ps' ← `(term| list_of_port_identifiers[ $ps ])
      `(term| VL.input_declaration.mk $t' $ps')

macro_rules
  | `(term|list_of_port_identifiers[ $p1:port_identifier, $p2,* ])
    => do
      let p' ← `(term| port_identifier[ $p1 ])
      let p2' ← p2.getElems.mapM fun p => `(term| port_identifier[ $p ])
      `(term| VL.list_of_port_identifiers.port_identifier $p' [$p2',*])
-- macro_rules
--   | `(identifier[ $d:ident ])
--     => `( $d )

-- macro_rules
--   | `(module_keyword[ module ])
--     => `(term|def)
--   | `(module_keyword[ macromodule ])
--     => `(#[])

-- macro_rules
--   | `(module_identifier[ $d:identifier ])
--     => `( def identifier[ $d ])

-- macro_rules
--   | `(module_item[ $d:ident ])
--     => `( def $d := "module_item" )






macro_rules
  | `(module_item[ $d:ident ])
    => `( def $d := "module_item" )


-- macro_rules
--   | `(command|description[ $d:module_declaration    ]) => `( command| description[ $d ] )

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

set_option pp.rawOnError true
set_option trace.Elab.step true
set_option trace.Elab.definition true
set_option trace.Elab.command true

-- list_of_port_declarations[(input p1, input p2, input p3)]
-- simple_identifier[ D ]
#reduce source_text[
  module abc();
  endmodule
]

#reduce input_declaration[
  input wire a,b,  c
]

#reduce identifier[
  name_d
]
def a := identifier[
  name_d
]
#print a
