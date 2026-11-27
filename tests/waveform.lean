import vc.tool.Waveform
import tests.dff_async_reset

namespace WaveformTest

def clock : Wire := fun time => time == 1
def resetN : Wire := fun time => time < 2
def dataSignal : Wire := fun time => time >=1
def if_block : Wire := «if» (fun time => !resetN time) (fun _ => false) dataSignal
def always_block : Wire := fun time : Nat => (postedge clock) time || (negedge resetN) time

def traces : List Waveform.Trace :=
  [("clk", clock), ("rst_n", resetN), ("data", dataSignal),
   ("posedge clk", postedge clock), ("negedge rst_n", negedge resetN),
   ("result", AsyncReset.sampledDff clock resetN dataSignal),
   ("if_block", if_block),
   ("always_block", always_block)
  ]


#eval [
  Waveform.samples clock 6,
  Waveform.samples resetN 6,
  Waveform.samples dataSignal 6,
  Waveform.samples (AsyncReset.sampledDff clock resetN dataSignal) 6,
  Waveform.samples always_block 6,
  Waveform.samples if_block 6
]

example : Waveform.samples clock 4 = [false, true, false, false] := by decide
example : Waveform.samples resetN 3 1 = [true, false, false] := by decide
example : Waveform.samples clock 0 = [] := rfl
example : Waveform.samples (AsyncReset.sampledDff clock resetN dataSignal) 6 =
    [false, true, true, true, true, true] := by decide
run_cmd do
  unless Waveform.escapeHtml "<&\"'>" == "&lt;&amp;&quot;&#39;&gt;" do
    throwError "incorrect HTML escaping"
example : Waveform.renderText [("clk", clock)] 3 1 =
    "time: 1 2 3\nclk: 1 0 0" := by decide

end WaveformTest

def main : IO Unit := do
  IO.println (Waveform.renderText WaveformTest.traces 6)
  Waveform.writeHtml "tests/async_reset_waveform.html" WaveformTest.traces 6 0
    "Asynchronous reset: generated signal"
  IO.println "Waveform: tests/async_reset_waveform.html"

#eval main
