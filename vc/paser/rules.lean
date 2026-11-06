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
  | `(term|statement[ $d:conditional_statement ])
    => do
      let d' ← `(term| conditional_statement[ $d ])
      `(term| VL.statement.conditional_statement $d')

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
  | `(term|event_expression[ negedge $d:expression ])
    => do
      let d' ← `(term| expression[ $d ])
      `(term| VL.event_expression.negedge $d')
  | `(term|event_expression[ $lhs:event_expression or $rhs:event_expression ])
    => do
      let lhs' ← `(term| event_expression[ $lhs ])
      let rhs' ← `(term| event_expression[ $rhs ])
      `(term| VL.event_expression.or $lhs' $rhs')

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
  | `(term|expression[ ( $value:expression ) ])
    => `(term| expression[ $value ])
  | `(term|expression[ $primary:primary ])
    => do
      let primary ← `(term| primary[ $primary ])
      `(term| VL.expression.primary $primary)
  | `(term|expression[ $op:unary_operator $value:primary ])
    => do
      let op ← `(term| unary_operator[ $op ])
      let value ← `(term| primary[ $value ])
      `(term| VL.expression.unary_operator $op $value)

macro_rules
  | `(term|unary_operator[ ! ]) => `(term| VL.unary_operator.not)

macro_rules
  | `(term|primary[ $n:number ])
    => do
      let n' ← `(term| number[ $n ])
      `(term| VL.primary.number $n')

macro_rules
  | `(term|number[ $bn:binary_number ])
    => do
      let bn' ← `(term| binary_number[ $bn ])
      `(term| VL.number.binary_number $bn')

macro_rules
  | `(term|binary_number[ $bb:binary_base $bv:binary_value ])
    => do
      let bb' ← `(term| binary_base[ $bb ])
      let bv' ← `(term| binary_value[ $bv ])
      `(term| VL.binary_number.mk $bb' $bv')

-- macro_rules
--   | `(term|binary_number[ $bb:binary_base $bv:binary_value ])
--     => do
--       let bb' ← match bb with
--         | `(binary_base| $apostrophe:char_' b) =>
--             `(term| binary_base[ $apostrophe b ])
--         | `(binary_base| $apostrophe:char_' B) =>
--             `(term| binary_base[ $apostrophe B ])
--         | _ => Lean.Macro.throwUnsupported
--       let bv' ← `(term| binary_value[ $bv ])
--       `(term| VL.binary_number.mk $bb' $bv')

macro_rules
  | `(term|binary_base[ ' $_:binary_base_letter ])
    => `(term| VL.binary_base.b)

macro_rules
  | `(term|conditional_statement[ if ( $cond:expression ) $thenStmt:statement_or_null $[else $elseStmt:statement_or_null]? ])
    => do
      let cond' ← `(term| expression[ $cond ])
      let thenStmt' ← `(term| statement_or_null[ $thenStmt ])
      let elseStmt' ← match elseStmt with
        | none => `(term| none)
        | some stmt => `(term| some (statement_or_null[ $stmt ]))
      `(term| VL.conditional_statement.mk $cond' $thenStmt' $elseStmt')

macro_rules
  | `(term|binary_digit[ $_:char_0 ]) => `(term| VL.binary_digit.char_0)
  | `(term|binary_digit[ $_:char_1 ]) => `(term| VL.binary_digit.char_1)
  | `(term|binary_digit[ x]) => `(term| x_digit[ x ])
  | `(term|binary_digit[ X]) => `(term| x_digit[ X ])
  | `(term|binary_digit[ z]) => `(term| z_digit[ z ])
  | `(term|binary_digit[ Z]) => `(term| z_digit[ Z ])
  | `(term|binary_digit[ ?]) => `(term| z_digit[ ? ])


macro_rules
  | `(term|x_digit[ x ]) => `(term| VL.x_digit.x)
  | `(term|x_digit[ X ]) => `(term| VL.x_digit.x)

macro_rules
  | `(term|z_digit[ z ]) => `(term| VL.z_digit.z)
  | `(term|z_digit[ Z ]) => `(term| VL.z_digit.z)
  | `(term|z_digit[ ? ]) => `(term| VL.z_digit.z)

macro_rules
  | `(term| binary_value[ $first:binary_digit $[$rest ]* ]) =>
    do
      let convertDigit := fun (digit : Lean.TSyntax `binary_digit) => do
        let value := digit.raw[0]
        if value.getKind == `char_0 then
          `(term| VL.binary_digit.char_0)
        else if value.getKind == `char_1 then
          `(term| VL.binary_digit.char_1)
        else
          match (⟨value⟩ : Lean.TSyntax [`x_digit, `z_digit]) with
          | `(x_digit| x) | `(x_digit| X) =>
              `(term| VL.binary_digit.x_digit VL.x_digit.x)
          | `(z_digit| z) | `(z_digit| Z) | `(z_digit| ?) =>
              `(term| VL.binary_digit.z_digit VL.z_digit.z)
          | _ => Lean.Macro.throwUnsupported
      let firstTerm ← convertDigit first
      let mut digits := #[]
      for item in rest do
        if item.raw.isAtom && item.raw.getAtomVal == "_" then
          continue
        let digitTerm ← convertDigit ⟨item.raw⟩
        digits := digits.push digitTerm
      `(term| VL.binary_value.mk $firstTerm [$digits,*])
