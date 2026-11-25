import vc.paser.to_char

syntax "ascii_count[" ascii_terminal* "]" : term

macro_rules
  | `(ascii_count[$tokens:ascii_terminal*]) =>
    return Lean.Syntax.mkNumLit (toString tokens.size)

example : ascii_apply "ascii" "END" [ABC]"END" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "END" []"END" = (#[] : Array UInt8) := rfl
example : ascii_apply "ascii_count" "END" [ABC]"END" = 3 := rfl
example : ascii_apply "ascii_count" "END" []"END" = 0 := rfl
example : ascii_apply "ascii" "END" [ A\n]"END" = ascii[u32 u65 u92 u110] := rfl
example : ascii_apply "ascii" "A" [ABC]"\x41" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "END" [A]"NO"B]"END" =
  ascii[u65 u93 u34 u78 u79 u34 u66] := rfl

run_cmd do
  for (source, expected) in #[
      ("ascii \"END\" [ABC]\"END\"", #[65, 66, 67]),
      ("ascii \"END\" []\"END\"", #[]),
      ("ascii \"END\" [ A B ]\"END\"", #[32, 65, 32, 66, 32]),
      ("ascii \"END\" [\"\\n\"]\"END\"", #[34, 92, 110, 34]),
      ("ascii \"END\" [A]\"NO\"B]\"END\"", #[65, 93, 34, 78, 79, 34, 66])] do
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term source with
      | .ok stx => pure stx
      | .error message => throwError "{message}"
    let some expanded ← Lean.Elab.liftMacroM (Lean.expandMacro? stx)
      | throwError "expected ascii macro expansion"
    unless expanded.getKind == Lean.nullKind do
      throwError "expected a terminal sequence"
    unless expanded.getArgs.size == expected.size do
      throwError "unexpected terminal count"
    for terminal in expanded.getArgs, code in expected do
      unless terminal.getKind == Lean.Name.mkSimple s!"ascii_u{code}" &&
          (terminal.getArg 0).getAtomVal == s!"u{code}" do
        throwError "unexpected terminal: {terminal}"

example : ascii_apply "ascii" "😂" ["ABC"]"😂" = ascii[u34 u65 u66 u67 u34] := rfl
example : ascii_apply "ascii" "😂" [ABC]"😂" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "😂" []"😂" = (#[] : Array UInt8) := rfl
example : ascii_apply "ascii" "😂" [""]"😂" = ascii[u34 u34] := rfl
example : ascii_apply "ascii" "😂" ["\n"]"😂" = ascii[u34 u92 u110 u34] := rfl
example : ascii_apply "ascii" "😂" [ A B ]"😂" = ascii[u32 u65 u32 u66 u32] := rfl
example : ascii_apply "ascii" "😂" [[]"😂" = ascii[u91] := rfl
example : ascii_apply "ascii" "😂" [a[0]"😂" = ascii[u97 u91 u48] := rfl
example : ascii_apply "ascii" "😂" ["[]"😂" = ascii[u34 u91] := rfl
example : ascii_apply "ascii" "😂" ["\""]"😂" = ascii[u34 u92 u34 u34] := rfl
example : ascii_apply "ascii" "😂" [-- /- !@#$]"😂" = ascii[u45 u45 u32 u47 u45 u32 u33 u64 u35 u36] := rfl
example : ascii_apply "ascii" "😂" [A
B]"😂" = ascii[u65 u10 u66] := rfl
example : ascii[u0 u127 u128 u255] = (#[0, 127, 128, 255] : Array UInt8) := rfl

/-- error: 字符 '中' 不属于标准 ASCII，字符码为 20013 -/
#guard_msgs in
#check ascii_apply "ascii" "😂" [中]"😂"

-- 检查每个终结符都可解析，且对应正确的字节值。
run_cmd do
  for i in [:256] do
    let source := s!"example : ascii[u{i}] = (#[{i}] : Array UInt8) := rfl"
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
    | .ok stx => Lean.Elab.Command.elabCommand stx
    | .error message => throwError message

example : ascii_apply "ascii" "😂" [[]]"😂" = ascii[u91 u93] := rfl
example : ascii_apply "ascii" "😂" []]"😂" = ascii[u93] := rfl
example : ascii_apply "ascii" "😂" [a[0]]"😂" = ascii[u97 u91 u48 u93] := rfl
example : ascii_apply "ascii" "😂" [] ]"😂" = ascii[u93 u32] := rfl

example : ascii_apply "ascii" "END" [ABC]"END" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "" [ABC]"" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "\n" [ABC]"\n" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "A" [ABC]"\x41" = ascii[u65 u66 u67] := rfl
example : ascii_apply "ascii" "END" [A]"NO"B]"END" =
  ascii[u65 u93 u34 u78 u79 u34 u66] := rfl
example : ascii_apply "ascii" "END" [A] "END"B]"END" =
  ascii[u65 u93 u32 u34 u69 u78 u68 u34 u66] := rfl

-- 单独的 ] 或 ] 后的空格均不能结束输入。
run_cmd do
    for source in #["ascii_apply \"ascii\" \"END\" [unfinished", "ascii_apply \"ascii\" \"END\" [ABC]",
      "ascii_apply \"ascii\" \"END\" [ABC] \"END\"", "ascii_apply \"ascii\" \"END\" [ABC]\"NO\""] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `term source with
    | .error _ => pure ()
    | .ok _ => throwError "expected missing closing delimiter error: {source}"

#reduce ascii_apply "ascii" "😂" ["ABC"]"😂"
#reduce ascii_apply "ascii" "😂" [[]]"😂"
#reduce ascii_apply "ascii" "😂" [[]"😂"
#reduce ascii_apply "ascii" "😂" []]"😂"
