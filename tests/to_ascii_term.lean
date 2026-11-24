import vc.paser.to_char

to_ascii_term ascii_input_keyword "input"
to_ascii_term ascii_endmodule_keyword "endmodule"
to_ascii_term num_0 "0"
to_ascii_term ascii_escaped_text " \n\""

syntax "input_bytes%[" ascii_input_keyword "]" : term
syntax "endmodule_bytes%[" ascii_endmodule_keyword "]" : term

macro_rules
  | `(input_bytes%[$_keyword:ascii_input_keyword]) =>
    `(ascii[u105 u110 u112 u117 u116])
  | `(endmodule_bytes%[$_keyword:ascii_endmodule_keyword]) =>
    `(ascii[u101 u110 u100 u109 u111 u100 u117 u108 u101])

example : input_bytes%[u105 u110 u112 u117 u116] =
    ascii[u105 u110 u112 u117 u116] := rfl
example : endmodule_bytes%[u101 u110 u100 u109 u111 u100 u117 u108 u101] =
    ascii[u101 u110 u100 u109 u111 u100 u117 u108 u101] := rfl

run_cmd do
  let env ← Lean.getEnv
  for (category, source, expected) in #[
      (`num_0, "u48", #["u48"]),
      (`ascii_escaped_text, "u32 u10 u34", #["u32", "u10", "u34"]),
      (`ascii_input_keyword, "u105 u110 u112 u117 u116", #["u105", "u110", "u112", "u117", "u116"]),
      (`ascii_endmodule_keyword, "u101 u110 u100 u109 u111 u100 u117 u108 u101",
        #["u101", "u110", "u100", "u109", "u111", "u100", "u117", "u108", "u101"])] do
    match Lean.Parser.runParserCategory env category source with
    | .error message => throwError "{message}"
    | .ok stx =>
      unless stx.getArgs.map Lean.Syntax.getAtomVal == expected do
        throwError "unexpected generated terminals: {stx}"
  for source in #["u105 u110 u112 u117", "u105 u110 u112 u117 u115"] do
    match Lean.Parser.runParserCategory env `ascii_input_keyword source with
    | .error _ => pure ()
    | .ok _ => throwError "expected rejection: {source}"

/-- error: to_ascii_term expects standard ASCII input -/
#guard_msgs in
to_ascii_term ascii_input_keyword "中"
