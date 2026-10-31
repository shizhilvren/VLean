import vc.paser.token
import vc.paser.syntax_tree
import vc.paser.syntax

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
    $[$items:module_item]*
    endmodule ])
    => do
      let d' ← `(term| module_keyword[ $d ])
      let i' ← `(term| module_identifier[ $i ])
      let l' ← match l with
        | none => `(term| none)
        | some l => `(term| some (list_of_port_declarations[ $l ]))
      let items' ← items.mapM fun item => `(term| module_item[ $item ])
      `(term| VL.module_declaration.mk $d' $i' $l' [$items',*])

macro_rules
  | `(term|list_of_port_declarations[ () ])
    => `( term| VL.list_of_port_declarations.empty )
  | `(term|list_of_port_declarations[ (  $p:port_declaration ) ])
    => do
      let p' ← `(term| port_declaration[ $p ])
      `(term| VL.list_of_port_declarations.port_declaration $p' []  )
  | `(term|list_of_port_declarations[ (  $p:port_declaration $[, $p2]*) ])
    => do
      let p' ← `(term| port_declaration[ $p ])
      let p2' ← p2.mapM fun p => `(term| port_declaration[ $p ])
      `(term| VL.list_of_port_declarations.port_declaration  $p' [$p2',*]  )

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
  | `(term|output_declaration[ output $[$t]? $ps ])
    => do
      let t' ← match t with
        | none => `(term| none)
        | some t => `(term| some (net_type[ $t ]))
      let ps' ← `(term| list_of_port_identifiers[ $ps ])
      `(term| VL.output_declaration.output $t' $ps')
  | `(term|output_declaration[ output reg $ps ])
    => do
      let ps' ← `(term| list_of_port_identifiers[ $ps ])
      `(term| VL.output_declaration.output_reg $ps')

macro_rules
  | `(term|list_of_port_identifiers[ $p1:port_identifier])
    => do
      let p' ← `(term| port_identifier[ $p1 ])
      `(term| (VL.list_of_port_identifiers.port_identifier $p' []))
  | `(term|list_of_port_identifiers[ $p1:port_identifier $[, $p2]* ])
    => do
      let p' ← `(term| port_identifier[ $p1 ])
      let p2' ← p2.mapM fun p => `(term| port_identifier[ $p ])
      `(term| (VL.list_of_port_identifiers.port_identifier $p' [$p2',*]))

macro_rules
  | `(term|net_type[ wire ])
    => `(term| VL.net_type.wire)

macro_rules
  | `(term|port_identifier[ $d:identifier ])
    => do
      let d' ← `(term| identifier[ $d ])
      `(term| VL.port_identifier.identifier $d')

macro_rules
  | `(term|module_item[ $d:module_or_generate_item ])
    => do
      let d' ← `(term| module_or_generate_item[ $d ])
      `(term| VL.module_item.module_or_generate_item $d')

macro_rules
  | `(term|module_or_generate_item[ $d:always_construct ])
    => do
      let d' ← `(term| always_construct[ $d ])
      `(term| VL.module_or_generate_item.always_construct $d')

macro_rules
  | `(term|always_construct[ always $s:statement ])
    => do
      let s' ← `(term| statement[ $s ])
      `(term| VL.always_construct.always $s')

macro_rules
  | `(term|statement[ $d:procedural_timing_control_statement ])
    => do
      let d' ← `(term| procedural_timing_control_statement[ $d ])
      `(term| VL.statement.procedural_timing_control_statement $d')
  | `(term|statement[ $d:seq_block ])
    => do
      let d' ← `(term| seq_block[ $d ])
      `(term| VL.statement.seq_block $d')
  | `(term|statement[ $d:nonblocking_assignment ; ])
    => do
      let d' ← `(term| nonblocking_assignment[ $d ])
      `(term| VL.statement.nonblocking_assignment $d')

macro_rules
  | `(term|procedural_timing_control_statement[ $d:procedural_timing_control $s:statement_or_null ])
    => do
      let d' ← `(term| procedural_timing_control[ $d ])
      let s' ← `(term| statement_or_null[ $s ])
      `(term| VL.procedural_timing_control_statement.mk $d' $s')

macro_rules
  | `(term|procedural_timing_control[ $d:event_control ])
    => do
      let d' ← `(term| event_control[ $d ])
      `(term| VL.procedural_timing_control.event_control $d')

macro_rules
  | `(term|event_control[ @ ( $d:event_expression ) ])
    => do
      let d' ← `(term| event_expression[ $d ])
      `(term| VL.event_control.event_expression $d')

macro_rules
  | `(term|event_expression[ posedge $d:expression ])
    => do
      let d' ← `(term| expression[ $d ])
      `(term| VL.event_expression.posedge $d')

macro_rules
  | `(term|statement_or_null[ $s:statement ])
    => do
      let s' ← `(term| statement[ $s ])
      `(term| VL.statement_or_null.statement $s')

macro_rules
  | `(term|seq_block[ begin $[$stmts:statement]* end ])
    => do
      let stmts' ← stmts.mapM fun stmt => `(term| statement[ $stmt ])
      `(term| VL.seq_block.statements [$stmts',*])

macro_rules
  | `(term|nonblocking_assignment[ $l:variable_lvalue <= $e:expression ])
    => do
      let l' ← `(term| variable_lvalue[ $l ])
      let e' ← `(term| expression[ $e ])
      `(term| VL.nonblocking_assignment.mk $l' $e')

macro_rules
  | `(term|variable_lvalue[ $d:identifier ])
    => do
      let d' ← `(term| identifier[ $d ])
      `(term| VL.variable_lvalue.identifier $d')

macro_rules
  | `(term|expression[ $d:identifier ])
    => do
      let d' ← `(term| identifier[ $d ])
      `(term| VL.expression.identifier $d')
