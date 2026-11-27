import vc.runtime.Signals

namespace Waveform

abbrev Trace := String × Wire

def samples (signal : Wire) (count : Nat) (start : Nat := 0) : List Bool :=
  (List.range count).map fun offset => signal (start + offset)

def renderText (traces : List Trace) (count : Nat) (start : Nat := 0) : String :=
  String.intercalate "\n" <|
    ("time: " ++ String.intercalate " " ((List.range count).map fun offset =>
      toString (start + offset))) ::
    traces.map fun (name, signal) =>
      name ++ ": " ++ String.intercalate " " ((samples signal count start).map fun value =>
        if value then "1" else "0")

def escapeHtml (value : String) : String :=
  value.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;" |>.replace "'" "&#39;"

def renderHtml (traces : List Trace) (count : Nat) (start : Nat := 0)
    (title : String := "Signal waveforms") : String := Id.run do
  let width := 180 + count * 48
  let height := 72 + traces.length * 64
  let mut drawing := ""
  let mut rows := ""
  for offset in List.range (count + 1) do
    let position := 160 + offset * 48
    drawing := drawing ++ s!"<line x1='{position}' x2='{position}' y1='32' y2='{height - 16}' stroke='#dce2e5'/>"
    if offset < count then
      drawing := drawing ++ s!"<text x='{position + 4}' y='22'>{start + offset}</text>"
  for row in List.range traces.length do
    let (name, signal) := traces[row]!
    let baseline := 48 + row * 64
    let color := if row % 2 == 0 then "#16745c" else "#b13c58"
    let mut points := []
    for offset in List.range count do
      let level := if signal (start + offset) then baseline else baseline + 28
      points := s!"{160 + (offset + 1) * 48},{level}" ::
        s!"{160 + offset * 48},{level}" :: points
    drawing := drawing ++ s!"<text x='12' y='{baseline + 18}'>{escapeHtml name}</text><polyline fill='none' stroke='{color}' stroke-width='2' points='{String.intercalate " " points.reverse}'/>"
  for offset in List.range count do
    let cells := String.join (traces.map fun (_, signal) =>
      s!"<td>{if signal (start + offset) then 1 else 0}</td>")
    rows := rows ++ s!"<tr><th>{start + offset}</th>{cells}</tr>"
  let headers := String.join (traces.map fun (name, _) => s!"<th>{escapeHtml name}</th>")
  return "<!doctype html><html lang='en'><head><meta charset='utf-8'><meta name='viewport' content='width=device-width, initial-scale=1'>" ++
    s!"<title>{escapeHtml title}</title>" ++
    "<style>body{font:14px Consolas,monospace;margin:24px;color:#202629;background:#f8fafb}h1{font-size:22px}.scroll{overflow:auto}svg{display:block;background:white}text{font-size:13px;fill:#202629}table{border-collapse:collapse;margin-top:24px}th,td{border-bottom:1px solid #dce2e5;padding:8px 16px;text-align:right}th{background:#edf3f2}</style></head><body>" ++
    s!"<h1>{escapeHtml title}</h1><div class='scroll'><svg xmlns='http://www.w3.org/2000/svg' width='{width}' height='{height}' viewBox='0 0 {width} {height}' role='img' aria-label='{escapeHtml title}'>{drawing}</svg></div>" ++
    s!"<div class='scroll'><table><thead><tr><th>time</th>{headers}</tr></thead><tbody>{rows}</tbody></table></div></body></html>"

def writeHtml (path : System.FilePath) (traces : List Trace) (count : Nat)
    (start : Nat := 0) (title : String := "Signal waveforms") : IO Unit :=
  IO.FS.writeFile path (renderHtml traces count start title)

end Waveform
