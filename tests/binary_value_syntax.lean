import vc.paser.syntax

run_cmd do
  let env ← Lean.getEnv
  for text in ["0", "1", "x", "X", "z", "Z", "?", "1010", "10_xZ?", "1__0_"] do
    match Lean.Parser.runParserCategory env `binary_value text with
    | .ok _ => pure ()
    | .error message => throwError "expected valid binary value {text}: {message}"
  for text in ["", "_01", "2", "102", "xg", "0 1"] do
    match Lean.Parser.runParserCategory env `binary_value text with
    | .ok _ => throwError "expected invalid binary value: {text}"
    | .error _ => pure ()
