import Lean

open Lean Elab Command

/-- 字节语言的终结符类别：u0、u1、……、u255。 -/
declare_syntax_cat ascii_terminal

/-- 自动注册全部 256 个终结符。 -/
elab "declare_ascii_terminals" : command => do
  for i in [:256] do
    let token : TSyntax `str := ⟨Syntax.mkStrLit s!"u{i}"⟩
    let kind := mkIdent (Name.mkSimple s!"ascii_u{i}")
    elabCommand (← `(command| syntax (name := $kind:ident) $token:str : ascii_terminal))

declare_ascii_terminals

macro "to_ascii_term " category:ident input:str : command => do
  let mut terminals : Array (TSyntax `stx) := #[]
  for character in input.getString.toList do
    let code := character.toNat
    if code > 127 then
      Macro.throwErrorAt input "to_ascii_term expects standard ASCII input"
    let token : TSyntax `str := ⟨Syntax.mkStrLit s!"u{code}"⟩
    terminals := terminals.push (← `(stx| $token:str))
  let categoryDeclaration ← `(command| declare_syntax_cat $category:ident)
  let terminalDeclaration ← `(command| syntax $[$terminals:stx]* : $category:ident)
  return ⟨mkNullNode #[categoryDeclaration.raw, terminalDeclaration.raw]⟩

/-- 字节语言的序列，解释为 Array UInt8。 -/
syntax "ascii[" ascii_terminal* "]" : term

macro_rules
  | `(ascii[$tokens:ascii_terminal*]) => do
    let values : Array (TSyntax `term) := tokens.map fun token =>
      let name := token.raw.getArg 0 |>.getAtomVal
      let value := (name.drop 1).toString.toNat!
      Syntax.mkNumLit (toString value)
    `((#[$values,*] : Array UInt8))

/-- 扫描正文，仅右方括号及紧随其后的同值校验字符串结束输入。 -/
private partial def asciiTextFn (checkSum : String) : Lean.Parser.ParserFn := fun ctx state =>
  if atEnd : ctx.atEnd state.pos then
    state.mkError s!"expected closing ] followed by {repr checkSum}"
  else
    let character := ctx.get' state.pos atEnd
    let next := ctx.next' state.pos atEnd
    if character == ']' then
      if nextAtEnd : ctx.atEnd next then
        asciiTextFn checkSum ctx (state.setPos next)
      else if ctx.get' next nextAtEnd == '"' then
        let candidate := Lean.Parser.strLitFn ctx (state.setPos next)
        if !candidate.hasError &&
          (⟨candidate.stxStack.back⟩ : TSyntax `str).getString == checkSum then
          state
        else
          asciiTextFn checkSum ctx (state.setPos next)
      else
        asciiTextFn checkSum ctx (state.setPos next)
    else asciiTextFn checkSum ctx (state.setPos next)

def asciiText : Lean.Parser.Parser :=
  { fn := fun ctx state =>
      let start := state.stxStack.back.getTailPos? |>.getD state.pos
      let checkSum := (⟨state.stxStack.pop.back⟩ : TSyntax `str).getString
      Lean.Parser.rawFn (asciiTextFn checkSum) false ctx (state.setPos start) }

@[combinator_formatter asciiText]
def asciiTextFormatter : Lean.PrettyPrinter.Formatter :=
  Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer asciiText]
def asciiTextParenthesizer : Lean.PrettyPrinter.Parenthesizer :=
  Lean.PrettyPrinter.Parenthesizer.visitToken

@[run_builtin_parser_attribute_hooks]
def asciiRaw : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "asciiRaw" `asciiRaw)
    (Lean.Parser.node `asciiRaw asciiText)

/-- 将方括号内的原始文本按标准 ASCII 转换为 uN 终结符序列。
保留引号、空白和反斜杠，不解码字符串转义。
终止条件为 `]` 紧接与起始校验串同值的字符串字面量，方括号不要求配对。
标准 ASCII 仅使用 u0 到 u127；u128 到 u255 仍可直接书写。
-/
syntax "ascii%" str "[" asciiRaw "]" str : term

macro_rules
  | `(ascii% $checkSum:str [ $text:asciiRaw ] $closing:str) => do
    unless checkSum.getString == closing.getString do
      Macro.throwErrorAt closing "closing checksum does not match opening checksum"
    let mut terminals : Array (TSyntax `ascii_terminal) := #[]
    for c in (text.raw.getArg 0).getAtomVal.toList do
      let code := c.toNat
      if code > 127 then
        Macro.throwErrorAt text
          s!"字符 '{c}' 不属于标准 ASCII，字符码为 {code}"
      let token := mkAtom s!"u{code}"
      let node := Syntax.node .none (Name.mkSimple s!"ascii_u{code}") #[token]
      terminals := terminals.push ⟨node⟩
    `(ascii[$terminals:ascii_terminal*])
