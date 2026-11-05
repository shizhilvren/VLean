import vc.paser.syntax

run_cmd do
  let env ← Lean.getEnv
  for (category, valid, invalid) in [
      (`x_digit, ["x", "X"], ["", "z", "xX"]),
      (`z_digit, ["z", "Z", "?"], ["", "x", "zZ"]),
      (`binary_digit, ["0", "1", "x", "X", "z", "Z", "?"], ["", "2", "_"])] do
    for text in valid do
      match Lean.Parser.runParserCategory env category text with
      | .ok _ => pure ()
      | .error message => throwError "expected valid {category} {text}: {message}"
    for text in invalid do
      match Lean.Parser.runParserCategory env category text with
      | .ok _ => throwError "expected invalid {category}: {text}"
      | .error _ => pure ()
