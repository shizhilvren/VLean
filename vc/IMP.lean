import Lean

open Lean Elab Meta

inductive IMPLit
  | nat  : Nat  → IMPLit
  | bool : Bool → IMPLit

inductive IMPUnOp
  | not

inductive IMPBinOp
  | and | add | less

inductive IMPExpr
  | lit : IMPLit → IMPExpr
  | var : String → IMPExpr
  | un  : IMPUnOp → IMPExpr → IMPExpr
  | bin : IMPBinOp → IMPExpr → IMPExpr → IMPExpr

inductive IMPProgram
  | Skip   : IMPProgram
  | Assign : String → IMPExpr → IMPProgram
  | Seq    : IMPProgram → IMPProgram → IMPProgram
  | If     : IMPExpr → IMPProgram → IMPProgram → IMPProgram
  | While  : IMPExpr → IMPProgram → IMPProgram


declare_syntax_cat imp_lit
syntax num       : imp_lit
syntax "true"    : imp_lit
syntax "false"   : imp_lit

def elabIMPLit : Syntax → MetaM Expr
  -- `mkAppM` 由给定函数 `Name` 和参数，创建一个 `Expr.app`，
  -- `mkNatLit` 由一个 `Nat` 创建一个 `Expr`
  | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
  | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
  | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax

elab "test_elabIMPLit " l:imp_lit : term => elabIMPLit l

#reduce test_elabIMPLit 4     -- IMPLit.nat 4
#reduce test_elabIMPLit true  -- IMPLit.bool true
#reduce test_elabIMPLit false -- IMPLit.bool true

declare_syntax_cat imp_unop
syntax "not"     : imp_unop

def elabIMPUnOp : Syntax → MetaM Expr
  | `(imp_unop| not) => return .const ``IMPUnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat imp_binop
syntax "+"       : imp_binop
syntax "and"     : imp_binop
syntax "<"       : imp_binop

def elabIMPBinOp : Syntax → MetaM Expr
  | `(imp_binop| +)   => return .const ``IMPBinOp.add []
  | `(imp_binop| and) => return .const ``IMPBinOp.and []
  | `(imp_binop| <)   => return .const ``IMPBinOp.less []
  | _ => throwUnsupportedSyntax

declare_syntax_cat                   imp_expr
syntax imp_lit                     : imp_expr
syntax ident                       : imp_expr
syntax imp_unop imp_expr           : imp_expr
syntax imp_expr imp_binop imp_expr : imp_expr

syntax "(" imp_expr ")" : imp_expr

partial def elabIMPExpr : Syntax → MetaM Expr
  | `(imp_expr| $l:imp_lit) => do
    let l ← elabIMPLit l
    mkAppM ``IMPExpr.lit #[l]
  -- `mkStrLit` 由一个 `String` 创建一个 `Expr`
  | `(imp_expr| $i:ident) => mkAppM ``IMPExpr.var #[mkStrLit i.getId.toString]
  | `(imp_expr| $b:imp_unop $e:imp_expr) => do
    let b ← elabIMPUnOp b
    let e ← elabIMPExpr e -- 递归!
    mkAppM ``IMPExpr.un #[b, e]
  | `(imp_expr| $l:imp_expr $b:imp_binop $r:imp_expr) => do
    let l ← elabIMPExpr l -- 递归!
    let r ← elabIMPExpr r -- 递归!
    let b ← elabIMPBinOp b
    mkAppM ``IMPExpr.bin #[b, l, r]
  | `(imp_expr| ($e:imp_expr)) => elabIMPExpr e
  | _ => throwUnsupportedSyntax

elab "test_elabIMPExpr " e:imp_expr : term => elabIMPExpr e

#reduce test_elabIMPExpr a
-- IMPExpr.var "a"

#reduce test_elabIMPExpr a + 5
-- IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 5))

#reduce test_elabIMPExpr 1 + true
-- IMPExpr.bin IMPBinOp.add (IMPExpr.lit (IMPLit.nat 1)) (IMPExpr.lit (IMPLit.bool true))

declare_syntax_cat           imp_program
syntax "skip"              : imp_program
syntax ident ":=" imp_expr : imp_program

syntax imp_program ";;" imp_program : imp_program

syntax "if" imp_expr "then" imp_program "else" imp_program "fi" : imp_program
syntax "while" imp_expr "do" imp_program "od" : imp_program

partial def elabIMPProgram : Syntax → MetaM Expr
  | `(imp_program| skip) => return .const ``IMPProgram.Skip []
  | `(imp_program| $i:ident := $e:imp_expr) => do
    let i : Expr := mkStrLit i.getId.toString
    let e ← elabIMPExpr e
    mkAppM ``IMPProgram.Assign #[i, e]
  | `(imp_program| $p₁:imp_program ;; $p₂:imp_program) => do
    let p₁ ← elabIMPProgram p₁
    let p₂ ← elabIMPProgram p₂
    mkAppM ``IMPProgram.Seq #[p₁, p₂]
  | `(imp_program| if $e:imp_expr then $pT:imp_program else $pF:imp_program fi) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    let pF ← elabIMPProgram pF
    mkAppM ``IMPProgram.If #[e, pT, pF]
  | `(imp_program| while $e:imp_expr do $pT:imp_program od) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    mkAppM ``IMPProgram.While #[e, pT]
  | _ => throwUnsupportedSyntax

-- elab ">>" p:imp_program "<<" : term => elabIMPProgram p

elab ">>" p:imp_program "<<" : term => do
  let expr ← elabIMPProgram p
  let reduced ← Meta.reduce expr
  return reduced


def  a := >>
a := 5;;
if not a and 3 < 4 then
  c := 5
else
  a := a + 1
fi;;
b := 10
<<

#print a

namespace IMP

private def variableName (expr : Expr) : Elab.Term.TermElabM String :=
  match expr with
  | .lit (.strVal name) => return name
  | _ => throwError "expected a literal IMP variable name"

private partial def exprToLean (expr : Expr) : Elab.Term.TermElabM (TSyntax `term) := do
  match expr.getAppFn.constName?, expr.getAppArgs with
  | some ``IMPExpr.lit, #[value] =>
    match value.getAppFn.constName?, value.getAppArgs with
    | some ``IMPLit.nat, #[.lit (.natVal value)] =>
      return Syntax.mkNumLit (toString value)
    | some ``IMPLit.bool, #[value] =>
      match value.constName? with
      | some ``Bool.true => `(Bool.true)
      | some ``Bool.false => `(Bool.false)
      | _ => throwError "expected a literal IMP boolean"
    | _, _ => throwError "expected an IMP literal"
  | some ``IMPExpr.var, #[name] =>
    return mkIdent (Name.mkSimple (← variableName name))
  | some ``IMPExpr.un, #[op, value] =>
    let value ← exprToLean value
    match op.constName? with
    | some ``IMPUnOp.not => `(!$value)
    | _ => throwError "unsupported IMP unary operator"
  | some ``IMPExpr.bin, #[op, left, right] =>
    let left ← exprToLean left
    let right ← exprToLean right
    match op.constName? with
    | some ``IMPBinOp.add => `($left + $right)
    | some ``IMPBinOp.less => `(decide ($left < $right))
    | some ``IMPBinOp.and => `($left && $right)
    | _ => throwError "unsupported IMP binary operator"
  | _, _ => throwError "expected a closed IMP expression"

private partial def assignedVariables (program : Expr) : Elab.Term.TermElabM (Array String) := do
  match program.getAppFn.constName?, program.getAppArgs with
  | some ``IMPProgram.Skip, #[] => return #[]
  | some ``IMPProgram.Assign, #[name, _] => return #[← variableName name]
  | some ``IMPProgram.Seq, #[first, second] =>
    return (← assignedVariables first) ++ (← assignedVariables second)
  | some ``IMPProgram.If, #[_, onTrue, onFalse] =>
    return (← assignedVariables onTrue) ++ (← assignedVariables onFalse)
  | some ``IMPProgram.While, #[_, body] => assignedVariables body
  | _, _ => throwError "expected a closed IMPProgram"

private partial def programToLean (program : Expr) :
    Elab.Term.TermElabM (Array (TSyntax `doElem)) := do
  match program.getAppFn.constName?, program.getAppArgs with
  | some ``IMPProgram.Skip, #[] => return #[← `(doElem| pure ())]
  | some ``IMPProgram.Assign, #[name, value] =>
    let name := mkIdent (Name.mkSimple (← variableName name))
    let value ← exprToLean value
    return #[← `(doElem| $name:ident := $value)]
  | some ``IMPProgram.Seq, #[first, second] =>
    return (← programToLean first) ++ (← programToLean second)
  | some ``IMPProgram.If, #[condition, onTrue, onFalse] =>
    let condition ← exprToLean condition
    let onTrue ← programToLean onTrue
    let onFalse ← programToLean onFalse
    return #[← `(doElem| if $condition then
      $[$onTrue:doElem]*
    else
      $[$onFalse:doElem]*)]
  | some ``IMPProgram.While, #[condition, body] =>
    let condition ← exprToLean condition
    let body ← programToLean body
    return #[← `(doElem| while $condition do
      $[$body:doElem]*)]
  | _, _ => throwError "expected a closed IMPProgram"

elab "imp_codegen% " program:term : term => do
  let program ← Elab.Term.elabTermEnsuringType program (mkConst ``IMPProgram)
  let program ← Meta.reduce (← instantiateMVars program)
  let names ← assignedVariables program
  let mut seen : Array String := #[]
  let mut declarations : Array (TSyntax `doElem) := #[]
  for name in names do
    unless seen.contains name do
      seen := seen.push name
      let ident := mkIdent (Name.mkSimple name)
      declarations := declarations.push (← `(doElem| let mut $ident:ident := default))
  let body ← programToLean program
  let code ← `(term| (do
    $[$declarations:doElem]*
    $[$body:doElem]*
    pure () : IO Unit))
  Elab.Term.elabTerm code (some (← Elab.Term.elabType (← `(IO Unit))))

end IMP

syntax "imp_to_lean " term:arg : term
syntax "imp_to_lean " ident " := " term:arg : command

macro_rules
  | `(imp_to_lean $program:term) => `(imp_codegen% $program)
  | `(command| imp_to_lean $id:ident := $program:term) =>
    `(command| def $id := imp_codegen% $program)

def countToThree : IMPProgram := >>
  x := 0;;
  while x < 3 do
    x := x + 1
  od;;
  if x < 4 then
    done := true
  else
    done := false
  fi
<<

imp_to_lean countToThreeLean := countToThree

#print countToThreeLean

example : IO Unit := imp_to_lean (>> skip <<)
example : IO Unit := imp_to_lean (>> while true do skip od <<)
example : IO Unit := imp_to_lean (>> x := not false and true <<)
example : IO Unit := imp_to_lean (>> if false then x := 1 else x := 2 fi <<)

def a2 := imp_to_lean (>> x := 1 + 2 <<)
#print a2

imp_to_lean abc := (>> if false then x := 1 else x := 2 fi <<)

#check abc
#print abc

def a3 :Nat:= by
  let p := abc
  exact 2
-- IMPProgram.Seq (IMPProgram.Assign "a" (IMPExpr.lit (IMPLit.nat 5)))
--   (IMPProgram.Seq
--     (IMPProgram.If
--       (IMPExpr.un IMPUnOp.not
--         (IMPExpr.bin IMPBinOp.and (IMPExpr.var "a")
--           (IMPExpr.bin IMPBinOp.less (IMPExpr.lit (IMPLit.nat 3)) (IMPExpr.lit (IMPLit.nat 4)))))
--       (IMPProgram.Assign "c" (IMPExpr.lit (IMPLit.nat 5)))
--       (IMPProgram.Assign "a" (IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 1)))))
--     (IMPProgram.Assign "b" (IMPExpr.lit (IMPLit.nat 10))))
