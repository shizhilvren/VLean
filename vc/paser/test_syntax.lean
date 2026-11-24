import Lean
-- set_option trace.Meta.synthInstance true
open Lean Parser


-------------------------------------------------------------------------------
-- 1. 定义底层的词法解析器 (ParserFn)
-------------------------------------------------------------------------------

-- 每次捕获一个数字，连续数字由外层 many1 收集为多个独立 Token
def dslNumFn : ParserFn :=
  rawFn (satisfyFn Char.isDigit "expected a DSL number")

-- 每次捕获一个空格，连续空格由外层 many1 收集为多个独立 Token
def dslSpaceFn : ParserFn :=
  rawFn (satisfyFn (· == ' ') "expected spaces")

-------------------------------------------------------------------------------
-- 2. 将底层函数包装为语法元素 (Parser)
-------------------------------------------------------------------------------

def dslNum : Parser := {
  fn := dslNumFn
}

def dslSpace : Parser := {
  fn := dslSpaceFn
}

@[combinator_formatter dslNum] def dslNumFormatter :=
  PrettyPrinter.Formatter.visitAtom .anonymous
@[combinator_parenthesizer dslNum] def dslNumParenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter dslSpace] def dslSpaceFormatter :=
  PrettyPrinter.Formatter.visitAtom .anonymous
@[combinator_parenthesizer dslSpace] def dslSpaceParenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

-------------------------------------------------------------------------------
-- 3. 创建 DSL 语法范畴，并允许它们交替出现
-------------------------------------------------------------------------------

declare_syntax_cat dsl_token

-- 将我们自定义的数字和空格解析器注册进 dsl_token
syntax (name := dslNumToken) dslNum : dsl_token
syntax (name := dslSpaceToken) dslSpace : dsl_token

def dslTokens : Parser :=
  many1 (node `dslNumToken dslNum <|> node `dslSpaceToken dslSpace) >>
    { fn := whitespace }

@[combinator_formatter dslTokens] def dslTokensFormatter :=
  PrettyPrinter.Formatter.manyNoAntiquot.formatter
    (PrettyPrinter.Formatter.visitAtom .anonymous)
@[combinator_parenthesizer dslTokens] def dslTokensParenthesizer :=
  PrettyPrinter.Parenthesizer.manyNoAntiquot.parenthesizer
    PrettyPrinter.Parenthesizer.visitToken

-- 定义一个 DSL 容器宏，它接收一串连续的自定义 Token
-- 自定义解析器保留 Token 之间的空格，交由 dslSpace 解析

-------------------------------------------------------------------------------
-- 4. 编写宏展开逻辑，提取并处理这些 Token
-------------------------------------------------------------------------------

open Macro

macro "run_dsl " tokens:dslTokens : term => do
    let mut numCount := 0
    let mut spaceCount := 0

    for t in tokens.raw.getArgs do
      -- 通过判断 Syntax 节点的 Kind 来区分 Token 类型
      if t.isOfKind `dslNumToken then
        numCount := numCount + 1
      else if t.isOfKind `dslSpaceToken then
        spaceCount := spaceCount + 1

    -- 构造一个返回信息，告诉我们解析到了多少个数字和多少个空格
    let resultStr := s!"[DSL 解析成功] 包含数字数量: {numCount}, 包含空格总数: {spaceCount}"
    return Syntax.mkStrLit resultStr

-------------------------------------------------------------------------------
-- 5. 测试效果
-------------------------------------------------------------------------------

set_option trace.Elab.step true
set_option trace.Elab.definition true
set_option trace.Elab.command true

-- 测试 1：正常解析数字和空格
#eval run_dsl 123   456
#reduce run_dsl 123   456
-- 输出: "[DSL 解析成功] 包含数字数量: 6, 包含空格总数: 3"

-- 测试 2：完全没有空格的情况
#eval run_dsl 999
-- 输出: "[DSL 解析成功] 包含数字数量: 3, 包含空格总数: 0"

#guard (run_dsl 123   456) ==
  "[DSL 解析成功] 包含数字数量: 6, 包含空格总数: 3"
#guard (run_dsl 999) ==
  "[DSL 解析成功] 包含数字数量: 3, 包含空格总数: 0"
#guard (run_dsl 0  12    345) ==
  "[DSL 解析成功] 包含数字数量: 6, 包含空格总数: 6"

run_cmd do
  match Parser.runParserCategory (← getEnv) `term "run_dsl 123   456" with
  | .error message => throwError "{message}"
  | .ok stx =>
    let tokens := stx[1].getArgs
    let values := tokens.map fun token => token[0].getAtomVal
    unless values == #["1", "2", "3", " ", " ", " ", "4", "5", "6"] do
      throwError "expected one token per character, got {repr values}"
    for token in tokens do
      let expectedKind := if token[0].getAtomVal == " " then `dslSpaceToken else `dslNumToken
      unless token.isOfKind expectedKind do
        throwError "unexpected token kind: {token.getKind}"

-- 测试 3：如果混入了普通标识符（如字母 a），会直接引发语法错误
-- #eval run_dsl 123 a 456
-- 编译期报错: expected a DSL number or expected spaces

partial def rawCharsBodyFn : ParserFn := fun c s =>
  if c.atEnd s.pos then
    s.mkError "expected closing }%"
  else if c.get s.pos == '}' && c.get (c.next s.pos) == '%' then
    s
  else
    rawCharsBodyFn c (s.next c s.pos)

def rawCharsBody : Parser := {
  fn := rawFn rawCharsBodyFn
}

@[combinator_formatter rawCharsBody] def rawCharsBodyFormatter :=
  PrettyPrinter.Formatter.visitAtom .anonymous
@[combinator_parenthesizer rawCharsBody] def rawCharsBodyParenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

def rawCharsBlock : Parser :=
  node `rawCharsBlock
    (rawCh '{' >> rawCharsBody >> rawCh '}' >> rawCh '%' true)

macro "chars%" body:rawCharsBlock : term => do
  let characters ← body.raw[1].getAtomVal.toList.toArray.mapM fun character =>
    `(Char.ofNat $(quote character.toNat))
  `((#[$characters,*] : Array Char))

#eval chars%{123   456
abc}%

#reduce chars%{'aaaa你好}%
#reduce chars%{abc     }%
#guard chars%{}% == (#[] : Array Char)
#guard chars%{  a  }% == #[' ', ' ', 'a', ' ', ' ']
#guard chars%{123   456
abc}% == "123   456\nabc".toList.toArray
#guard chars%{

  a
}% == "\n\n  a\n".toList.toArray
#guard chars%{你好}% == #['你', '好']
#reduce chars%{{x} -- /- "text" \n}% == "{x} -- /- \"text\" \\n".toList.toArray

run_cmd do
  match Parser.runParserCategory (← getEnv) `term "chars%{unfinished" with
  | .error _ => pure ()
  | .ok _ => throwError "expected an error for an unclosed character block"
