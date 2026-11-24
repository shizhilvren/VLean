import vc.paser.to_char

example : ascii% "😂" ["ABC"]"😂" = ascii[u34 u65 u66 u67 u34] := rfl
example : ascii% "😂" [ABC]"😂" = ascii[u65 u66 u67] := rfl
example : ascii% "😂" []"😂" = (#[] : Array UInt8) := rfl
example : ascii% "😂" [""]"😂" = ascii[u34 u34] := rfl
example : ascii% "😂" ["\n"]"😂" = ascii[u34 u92 u110 u34] := rfl
example : ascii% "😂" [ A B ]"😂" = ascii[u32 u65 u32 u66 u32] := rfl
example : ascii% "😂" [[]"😂" = ascii[u91] := rfl
example : ascii% "😂" [a[0]"😂" = ascii[u97 u91 u48] := rfl
example : ascii% "😂" ["[]"😂" = ascii[u34 u91] := rfl
example : ascii% "😂" ["\""]"😂" = ascii[u34 u92 u34 u34] := rfl
example : ascii% "😂" [-- /- !@#$]"😂" = ascii[u45 u45 u32 u47 u45 u32 u33 u64 u35 u36] := rfl
example : ascii% "😂" [A
B]"😂" = ascii[u65 u10 u66] := rfl
example : ascii[u0 u127 u128 u255] = (#[0, 127, 128, 255] : Array UInt8) := rfl

/-- error: 字符 '中' 不属于标准 ASCII，字符码为 20013 -/
#guard_msgs in
#check ascii% "😂" [中]"😂"

-- 检查每个终结符都可解析，且对应正确的字节值。
run_cmd do
  for i in [:256] do
    let source := s!"example : ascii[u{i}] = (#[{i}] : Array UInt8) := rfl"
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
    | .ok stx => Lean.Elab.Command.elabCommand stx
    | .error message => throwError message

example : ascii% "😂" [[]]"😂" = ascii[u91 u93] := rfl
example : ascii% "😂" []]"😂" = ascii[u93] := rfl
example : ascii% "😂" [a[0]]"😂" = ascii[u97 u91 u48 u93] := rfl
example : ascii% "😂" [] ]"😂" = ascii[u93 u32] := rfl

example : ascii% "END" [ABC]"END" = ascii[u65 u66 u67] := rfl
example : ascii% "" [ABC]"" = ascii[u65 u66 u67] := rfl
example : ascii% "\n" [ABC]"\n" = ascii[u65 u66 u67] := rfl
example : ascii% "A" [ABC]"\x41" = ascii[u65 u66 u67] := rfl
example : ascii% "END" [A]"NO"B]"END" =
  ascii[u65 u93 u34 u78 u79 u34 u66] := rfl
example : ascii% "END" [A] "END"B]"END" =
  ascii[u65 u93 u32 u34 u69 u78 u68 u34 u66] := rfl

-- 单独的 ] 或 ] 后的空格均不能结束输入。
run_cmd do
  for source in #["ascii% \"END\" [unfinished", "ascii% \"END\" [ABC]",
      "ascii% \"END\" [ABC] \"END\"", "ascii% \"END\" [ABC]\"NO\""] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `term source with
    | .error _ => pure ()
    | .ok _ => throwError "expected missing closing delimiter error: {source}"

#reduce ascii% "😂" ["ABC"]"😂"
#reduce ascii% "😂" [[]]"😂"
#reduce ascii% "😂" [[]"😂"
#reduce ascii% "😂" []]"😂"
