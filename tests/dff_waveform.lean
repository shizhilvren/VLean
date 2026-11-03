import vc.verilog

namespace DffStimulus

def clock : Wire := fun time => time % 4 >= 2

def dataBits : List Nat := [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1]

def dataSignal : Wire := fun time => dataBits[time]?.getD 0 == 1

def outputSignal : Reg := portParameterTests.D clock dataSignal

def samples (signal : Wire) : List Nat :=
  (List.range 16).map fun time => if signal time then 1 else 0

def expected : List Nat := [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0]

example : samples outputSignal = expected := by decide
example : samples (portParameterTests.D (fun _ => Bool.false) dataSignal) =
    List.replicate 16 0 := by decide
example : samples (portParameterTests.D (fun _ => Bool.true) dataSignal) =
    List.replicate 16 0 := by decide
example : samples (portParameterTests.D clock (fun _ => Bool.true)) =
    [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by decide
example : samples (portParameterTests.D clock (fun _ => Bool.false)) =
    List.replicate 16 0 := by decide
example : outputSignal 2 = dataSignal 1 := by decide
example : dataSignal 2 != outputSignal 2 := by decide
example : dataSignal 4 != dataSignal 3 ∧ outputSignal 4 = outputSignal 3 := by decide

def traceSvg (label color : String) (row : Nat) (signal : Wire) : String := Id.run do
  let baseline := 70 + row * 90
  let mut points : List String := []
  for time in List.range 16 do
    let level := if signal time then baseline else baseline + 30
    points := points ++ [s!"{100 + time * 48},{level}", s!"{100 + (time + 1) * 48},{level}"]
  return s!"<text x='16' y='{baseline + 20}'>{label}</text><polyline fill='none' stroke='{color}' stroke-width='3' points='{String.intercalate " " points}'/>"

def waveformHtml : String := Id.run do
  let mut grid := ""
  let mut cells := ""
  for time in List.range 16 do
    grid := grid ++ s!"<line x1='{100 + time * 48}' y1='42' x2='{100 + time * 48}' y2='300' stroke='#e0e4e6'/><text x='{110 + time * 48}' y='325'>{time}</text>"
    cells := cells ++ s!"<tr><td>{time}</td><td>{if clock time then 1 else 0}</td><td>{if dataSignal time then 1 else 0}</td><td>{if outputSignal time then 1 else 0}</td><td>{expected[time]?.getD 0}</td></tr>"
  let mut edges := ""
  for time in [2, 6, 10, 14] do
    edges := edges ++ s!"<line x1='{100 + time * 48}' y1='42' x2='{100 + time * 48}' y2='300' stroke='#ba3853' stroke-dasharray='4 4'/>"
  return "<!doctype html><html lang='en'><meta charset='utf-8'><meta name='viewport' content='width=device-width, initial-scale=1'><title>Generated D waveform</title><style>body{font-family:Consolas,monospace;margin:24px;color:#202629;background:#fafcfc}h1{font-size:24px}section{overflow-x:auto}svg{min-width:880px;width:100%;max-width:1100px;background:white}text{font-size:14px;fill:#202629}table{border-collapse:collapse;font-size:14px}th,td{padding:6px 18px;border-bottom:1px solid #dce3e5;text-align:right}th{background:#e8f1ef}p{max-width:900px;line-height:1.6}</style><h1>Generated D: clock, data, output</h1><p>16 samples. Initial output = 0. Rising edges: 2, 6, 10, 14 (dashed lines). At edge t, output samples data[t-1]; otherwise it holds. Data and output are computed by Lean.</p><section><svg viewBox='0 0 900 350' role='img' aria-label='Digital waveform of clock, data and generated D output'>" ++
    grid ++ edges ++ traceSvg "clk" "#246baf" 0 clock ++
    traceSvg "in" "#14855f" 1 dataSignal ++ traceSvg "out" "#ba3853" 2 outputSignal ++
    "<text x='16' y='325'>time</text></svg></section><table><thead><tr><th>time</th><th>clk</th><th>in</th><th>out</th><th>expected</th></tr></thead><tbody>" ++
    cells ++ "</tbody></table></html>"

end DffStimulus

def main : IO Unit := do
  unless DffStimulus.samples DffStimulus.outputSignal == DffStimulus.expected do
    throw (IO.userError "generated D output does not match expected samples")
  IO.println s!"clk: {DffStimulus.samples DffStimulus.clock}"
  IO.println s!"in:  {DffStimulus.samples DffStimulus.dataSignal}"
  IO.println s!"out: {DffStimulus.samples DffStimulus.outputSignal}"
  IO.FS.writeFile "tests/dff_waveform.html" DffStimulus.waveformHtml
  IO.println "Checks passed. Waveform: tests/dff_waveform.html"
