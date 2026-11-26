import vc.paser.token
import vc.paser.syntax_tree
import vc.paser.syntax

private partial def asciiSyntaxText : Lean.Syntax → String
  | .atom _ value => String.singleton (Char.ofNat (value.drop 1).toString.toNat!)
  | .node _ _ arguments => String.join (arguments.toList.map asciiSyntaxText)
  | _ => ""

macro_rules
  | `(term| identifier[ $identifier:simple_identifier ]) => do
    let name := asciiSyntaxText identifier.raw
    `(term| VL.identifier.ident $(Lean.quote (Lean.Name.mkSimple name)))

macro_rules
  | `(term| statement[ $_:ascii_spaces $assignment:nonblocking_assignment $_:ascii_spaces $_:char_semicolon $_:ascii_spaces ]) => do
    let assignment ← `(term| nonblocking_assignment[ $assignment ])
    `(term| VL.statement.nonblocking_assignment $assignment)

macro_rules
  | `(term| nonblocking_assignment[ $target:variable_lvalue $_:ascii_spaces $_:char_less $_:char_equal $_:ascii_spaces $value:expression ]) => do
    let target ← `(term| variable_lvalue[ $target ])
    let value ← `(term| expression[ $value ])
    `(term| VL.nonblocking_assignment.mk $target $value)

macro_rules
  | `(term| binary_number[ $size:size $base:binary_base $value:binary_value ]) => do
    let width := (asciiSyntaxText size.raw |>.replace "_" "").toNat!
    let base ← `(term| binary_base[ $base ])
    let value ← `(term| binary_value[ $value ])
    `(term| VL.binary_number.mk $base $value (some $(Lean.quote width)))

macro_rules
  | `(term|source_text[ $_:ascii_spaces $ds:description* $_:ascii_spaces ])
    => do
      let items ← ds.mapM fun description => `(term| description[ $description ])
      `(term| VL.source_text.description [$items,*])

macro_rules
  | `(description[ $d:module_declaration ])
    =>do
      let item ← `(term| module_declaration[ $d ])
      `(term| VL.description.module_declaration $item)

macro_rules
  | `(term|module_keyword[ $_:keyword_module ]) => `(term| VL.module_keyword.module)
  | `(term|module_keyword[ $_:keyword_macromodule ]) => `(term| VL.module_keyword.macromodule)

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
  | `(term|module_declaration[ $_:ascii_spaces $kind:module_keyword $_:ascii_spaces $name:module_identifier $_:ascii_spaces $[$ports:list_of_port_declarations]? $_:ascii_spaces $_:char_semicolon $_:ascii_spaces $[$items:module_item]* $_:keyword_endmodule $_:ascii_spaces ]) => do
      let kind ← `(term| module_keyword[ $kind ])
      let name ← `(term| module_identifier[ $name ])
      let ports ← match ports with
        | none => `(term| none)
        | some ports => `(term| some (list_of_port_declarations[ $ports ]))
      let items ← items.mapM fun item => `(term| module_item[ $item ])
      `(term| VL.module_declaration.mk $kind $name $ports [$items,*])

macro_rules
  | `(term|list_of_port_declarations[ $_:ascii_spaces $_:char_open_paren $_:ascii_spaces $_:char_close_paren $_:ascii_spaces ]) =>
      `(term| VL.list_of_port_declarations.empty)
  | `(term|list_of_port_declarations[ $_:ascii_spaces $_:char_open_paren $_:ascii_spaces $first:port_declaration $[$_:ascii_spaces $_:char_comma $_:ascii_spaces $rest:port_declaration]* $_:ascii_spaces $_:char_close_paren $_:ascii_spaces ]) => do
      let first ← `(term| port_declaration[ $first ])
      let rest ← rest.mapM fun port => `(term| port_declaration[ $port ])
      `(term| VL.list_of_port_declarations.port_declaration $first [$rest,*])

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
  | `(term|input_declaration[ $_:keyword_input $_:ascii_spaces $[$kind:net_type]? $_:ascii_spaces $ports:list_of_port_identifiers ]) => do
      let kind ← match kind with
        | none => `(term| none)
        | some kind => `(term| some (net_type[ $kind ]))
      let ports ← `(term| list_of_port_identifiers[ $ports ])
      `(term| VL.input_declaration.mk $kind $ports)

macro_rules
  | `(term|output_declaration[ $_:keyword_output $_:ascii_spaces $_:keyword_reg $_:ascii_spaces $ports:list_of_port_identifiers ]) => do
      let ports ← `(term| list_of_port_identifiers[ $ports ])
      `(term| VL.output_declaration.output_reg $ports)
  | `(term|output_declaration[ $_:keyword_output $_:ascii_spaces $[$kind:net_type]? $_:ascii_spaces $ports:list_of_port_identifiers ]) => do
      let kind ← match kind with
        | none => `(term| none)
        | some kind => `(term| some (net_type[ $kind ]))
      let ports ← `(term| list_of_port_identifiers[ $ports ])
      `(term| VL.output_declaration.output $kind $ports)

macro_rules
  | `(term|list_of_port_identifiers[ $first:port_identifier $[$_:ascii_spaces $_:char_comma $_:ascii_spaces $rest:port_identifier]* ]) => do
      let first ← `(term| port_identifier[ $first ])
      let rest ← rest.mapM fun port => `(term| port_identifier[ $port ])
      `(term| VL.list_of_port_identifiers.port_identifier $first [$rest,*])

macro_rules
  | `(term|net_type[ $_:keyword_wire ]) => `(term| VL.net_type.wire)

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
  | `(term|always_construct[ $_:ascii_spaces $_:keyword_always $_:ascii_spaces $body:statement $_:ascii_spaces ]) => do
      let body ← `(term| statement[ $body ])
      `(term| VL.always_construct.always $body)

macro_rules
  | `(term|statement[ $d:procedural_timing_control_statement ])
    => do
      let d' ← `(term| procedural_timing_control_statement[ $d ])
      `(term| VL.statement.procedural_timing_control_statement $d')
  | `(term|statement[ $d:seq_block ])
    => do
      let d' ← `(term| seq_block[ $d ])
      `(term| VL.statement.seq_block $d')
  | `(term|statement[ $d:conditional_statement ])
    => do
      let d' ← `(term| conditional_statement[ $d ])
      `(term| VL.statement.conditional_statement $d')

macro_rules
  | `(term|procedural_timing_control_statement[ $control:procedural_timing_control $_:ascii_spaces $body:statement_or_null ]) => do
      let control ← `(term| procedural_timing_control[ $control ])
      let body ← `(term| statement_or_null[ $body ])
      `(term| VL.procedural_timing_control_statement.mk $control $body)

macro_rules
  | `(term|procedural_timing_control[ $d:event_control ])
    => do
      let d' ← `(term| event_control[ $d ])
      `(term| VL.procedural_timing_control.event_control $d')

macro_rules
  | `(term|event_control[ $_:ascii_spaces $_:char_at $_:ascii_spaces $_:char_open_paren $_:ascii_spaces $event:event_expression $_:ascii_spaces $_:char_close_paren ]) => do
      let event ← `(term| event_expression[ $event ])
      `(term| VL.event_control.event_expression $event)

macro_rules
  | `(term|event_expression[ $_:keyword_posedge $_:ascii_spaces $value:expression ]) => do
    let value ← `(term| expression[ $value ])
    `(term| VL.event_expression.posedge $value)
  | `(term|event_expression[ $_:keyword_negedge $_:ascii_spaces $value:expression ]) => do
    let value ← `(term| expression[ $value ])
    `(term| VL.event_expression.negedge $value)
  | `(term|event_expression[ $left:event_expression $_:ascii_spaces $_:keyword_or $_:ascii_spaces $right:event_expression ]) => do
    let left ← `(term| event_expression[ $left ])
    let right ← `(term| event_expression[ $right ])
    `(term| VL.event_expression.or $left $right)

macro_rules
  | `(term|statement_or_null[ $s:statement ])
    => do
      let s' ← `(term| statement[ $s ])
      `(term| VL.statement_or_null.statement $s')

macro_rules
  | `(term|seq_block[ $_:ascii_spaces $_:keyword_begin $_:ascii_spaces $[$statements:statement]* $_:keyword_end $_:ascii_spaces ]) => do
      let statements ← statements.mapM fun body => `(term| statement[ $body ])
      `(term| VL.seq_block.statements [$statements,*])



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
  | `(term|expression[ $_:char_open_paren $_:ascii_spaces $value:expression $_:ascii_spaces $_:char_close_paren ])
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
  | `(term|expression[ $op:unary_operator $_:ascii_spaces $value:primary ]) => do
      let op ← `(term| unary_operator[ $op ])
      let value ← `(term| primary[ $value ])
      `(term| VL.expression.unary_operator $op $value)

macro_rules
  | `(term|unary_operator[ u33 ]) => `(term| VL.unary_operator.not)

macro_rules
  | `(term|hierarchical_identifier[ $identifier:identifier ]) => do
      let identifier ← `(term| identifier[ $identifier ])
      `(term| VL.hierarchical_identifier.identifier $identifier)

macro_rules
  | `(term|primary[ $identifier:hierarchical_identifier ]) => do
      let identifier ← `(term| hierarchical_identifier[ $identifier ])
      `(term| VL.primary.hierarchical_identifier $identifier)
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
  | `(term|binary_base[ u39 u98 ])
    => `(term| VL.binary_base.b)
  | `(term|binary_base[ u39 u66 ])
    => `(term| VL.binary_base.b)
  -- | `(term|binary_base[ $_:char_' $_:char_B ])
  --   => `(term| VL.binary_base.B)

macro_rules
  | `(term|conditional_statement[ $_:ascii_spaces $_:keyword_if $_:ascii_spaces $_:char_open_paren $_:ascii_spaces $cond:expression $_:ascii_spaces $_:char_close_paren $_:ascii_spaces $thenStmt:statement_or_null $[$_:keyword_else $_:ascii_spaces $elseStmt:statement_or_null]? ])
    => do
      let cond' ← `(term| expression[ $cond ])
      let thenStmt' ← `(term| statement_or_null[ $thenStmt ])
      let elseStmt' ← match elseStmt with
        | none => `(term| none)
        | some stmt => `(term| some (statement_or_null[ $stmt ]))
      `(term| VL.conditional_statement.mk $cond' $thenStmt' $elseStmt')

macro_rules
  | `(term|x_digit[ u120 ]) => `(term| VL.x_digit.x)
  | `(term|x_digit[ u88 ]) => `(term| VL.x_digit.x)

macro_rules
  | `(term|z_digit[ u122 ]) => `(term| VL.z_digit.z)
  | `(term|z_digit[ u90 ]) => `(term| VL.z_digit.z)
  | `(term|z_digit[ u63 ]) => `(term| VL.z_digit.z)

macro_rules
  | `(term|binary_digit[ u48 ]) => `(term| VL.binary_digit.char_0)
  | `(term|binary_digit[ u49 ]) => `(term| VL.binary_digit.char_1)
  | `(term|binary_digit[ $xd:x_digit ]) =>
    `(term| VL.binary_digit.x_digit (x_digit[ $xd ]))
  | `(term|binary_digit[ $zd:z_digit ]) =>
    `(term| VL.binary_digit.z_digit (z_digit[ $zd ]))

macro_rules
  | `(term| binary_value[ $first:binary_digit $[$rest ]* ]) =>
    do
      let firstTerm ← `(term| binary_digit[ $first ])
      let mut digits : Array (Lean.TSyntax `term) := #[]
      for item in rest do
        match (⟨item.raw⟩ : Lean.TSyntax `char__) with
        | `(char__| u95) => continue
        | _ => pure ()
        let digit : Lean.TSyntax `binary_digit := ⟨item.raw⟩
        let digitTerm ← `(term| binary_digit[ $digit ])
        digits := digits.push digitTerm
      `(term| VL.binary_value.mk $firstTerm [$digits,*])
