import vc.paser.rules

run_cmd do
  let env ← Lean.getEnv
  for text in ["binary_base[ 'b ]", "binary_base[ 'B ]"] do
    let stx ← match Lean.Parser.runParserCategory env `term text with
      | .ok stx => pure stx
      | .error message => throwError "{message}"
    Lean.Elab.Command.liftTermElabM do
      let value ← Lean.Elab.Term.elabTermEnsuringType stx (Lean.mkConst ``VL.binary_base)
      unless ← Lean.Meta.isDefEq value (Lean.mkConst ``VL.binary_base.b) do
        throwError "incorrect binary base conversion: {text}"
