import Lean
-- set_option pp.all true in
-- set_option trace.Elab.step true
-- set_option trace.Elab.definition true
-- set_option trace.Elab.command true
-- set_option trace.Elab.step true in
-- set_option trace.Elab.definition true in
-- set_option trace.Elab.command true in
-- set_option pp.all true in

abbrev Wire := Nat -> Bool
abbrev Reg := Nat -> Bool
partial def visualize (wire : Wire) (a : Nat) (b : Nat) : List Bool :=
  if a > b then
    []
  else
    (wire a) :: (visualize wire (a + 1) b)

open Lean Elab Command in
elab "#expand_once " cmd:command : command => do
  let expanded? ← liftMacroM (Lean.Macro.expandMacro? cmd)
  match expanded? with
  | none =>
    logInfo "该命令没有可展开的宏"
  | some expanded =>
    let text ← liftCoreM <|
      Lean.PrettyPrinter.ppCommand ⟨expanded⟩
    logInfo m!"{text}"

open Lean Elab Command in
partial def expandAllSyntax (stx : Syntax) : CommandElabM Syntax :=
  withRef stx do
    withIncRecDepth do
      match ← liftMacroM (Macro.expandMacro? stx) with
      | some expanded => expandAllSyntax expanded
      | none =>
        match stx with
        | .node info kind args =>
          return .node info kind (← args.mapM expandAllSyntax)
        | _ => return stx

open Lean Elab Command in
elab "#expand_all " cmd:command : command => do
  let expanded ← expandAllSyntax cmd
  let text ← liftCoreM <|
    Lean.PrettyPrinter.ppCommand ⟨expanded⟩
  logInfo m!"{text}"


declare_syntax_cat verilogExpr

syntax ident : verilogExpr
syntax num : verilogExpr
syntax "(" verilogExpr ")" : verilogExpr
syntax:80 "!" verilogExpr:80 : verilogExpr
syntax:80 "~" verilogExpr:80 : verilogExpr
syntax:70 verilogExpr:70 "&" verilogExpr:71 : verilogExpr
syntax:60 verilogExpr:60 "^" verilogExpr:61 : verilogExpr
syntax:50 verilogExpr:50 "|" verilogExpr:51 : verilogExpr

syntax "verilog[" verilogExpr "]" : term
syntax "verilog" "assign" ident "=" verilogExpr ";" : command

macro_rules
  | `(verilog[ $signal:ident ]) => `(($signal : Wire))
  | `(verilog[ $value:num ]) =>
    match value.getNat with
    | 0 => `((fun _ => false : Wire))
    | 1 => `((fun _ => true : Wire))
    | _ => Lean.Macro.throwErrorAt value "only single-bit constants 0 and 1 are supported"
  | `(verilog[ ($expr:verilogExpr) ]) => `(verilog[ $expr ])
  | `(verilog[ !$expr:verilogExpr ]) =>
    `((fun time => !(verilog[ $expr ] time) : Wire))
  | `(verilog[ ~$expr:verilogExpr ]) =>
    `((fun time => !(verilog[ $expr ] time) : Wire))
  | `(verilog[ $left:verilogExpr & $right:verilogExpr ]) =>
    `((fun time => verilog[ $left ] time && verilog[ $right ] time : Wire))
  | `(verilog[ $left:verilogExpr ^ $right:verilogExpr ]) =>
    `((fun time => Bool.xor (verilog[ $left ] time) (verilog[ $right ] time) : Wire))
  | `(verilog[ $left:verilogExpr | $right:verilogExpr ]) =>
    `((fun time => verilog[ $left ] time || verilog[ $right ] time : Wire))
  | `(command| verilog assign $output:ident = $expr:verilogExpr;) =>
    `(command| def $output : Wire := verilog[ $expr ] )

namespace VerilogExamples

def inputA : Wire := fun time => time % 2 == 1
def inputB : Wire := fun time => time % 4 >= 2

verilog assign sum = inputA ^ inputB;

-- #check verilog assign sum = inputA ^ inputB;

verilog assign carry = inputA & inputB;

-- #expand_once verilog assign carry = inputA & inputB;
-- #expand_once verilog [ inputA & inputB ];
-- #expand_all verilog assign carry = inputA & inputB;

#guard visualize sum 0 3 == [false, true, true, false]
#guard visualize carry 0 3 == [false, false, false, true]
#guard visualize (verilog[ 1 | 0 ^ 1 & 0 ]) 0 0 == [true]
#guard visualize (verilog[ (1 | 0) ^ 1 & 0 ]) 0 0 == [true]
#guard visualize (verilog[ (1 | 0 ^ 1) & 0 ]) 0 0 == [false]
#guard visualize (verilog[ !0 & ~1 ]) 0 0 == [false]
#guard visualize (verilog[ ~inputA ]) 0 3 == [true, false, true, false]

/-- error: only single-bit constants 0 and 1 are supported -/
#guard_msgs in
#check verilog[ 2 ]

example (signal : Wire) : verilog[ signal & 1 ] = signal := by
  funext time
  simp

-- def expandedExample : Wire := verilog assign sum = inputA ^ inputB;
-- #print expandedExample



end VerilogExamples
