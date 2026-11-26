import vc.verilog

namespace AsyncReset

verilog "EOF" [
  module sampledDff(input wire clk, rst_n, data, output reg result);
    always @(posedge clk or negedge rst_n) begin
      if (!rst_n) result <= 1'b0;
      else result <= data;
    end
  endmodule
]"EOF"

#print sampledDff

theorem initial (clock resetN dataSignal : Wire) :
    sampledDff clock resetN dataSignal 0 = false := by
      rw [sampledDff]
      rfl

theorem step (clock resetN dataSignal : Wire) (time : Nat) :
    sampledDff clock resetN dataSignal (time + 1) =
      (if postedge clock (time + 1) || negedge resetN (time + 1) then
        if resetN time then dataSignal time else false
      else sampledDff clock resetN dataSignal time) := by
  cases resetBefore : resetN time <;>
    cases resetAfter : resetN (time + 1) <;>
      cases clockBefore : clock time <;>
        cases clockAfter : clock (time + 1) <;>
          simp [sampledDff, «always», postedge, negedge,
            resetBefore, resetAfter, clockBefore, clockAfter]

theorem reset_sampled (clock resetN dataSignal : Wire) (time : Nat)
    (active : resetN time = false)
    (event : (postedge clock (time + 1) || negedge resetN (time + 1)) = true) :
    sampledDff clock resetN dataSignal (time + 1) = false := by
  rw [step]
  simp [event, active]

theorem reset_falling (clock resetN dataSignal : Wire) (time : Nat)
    (wasHigh : resetN time = true) (nowLow : resetN (time + 1) = false) :
    sampledDff clock resetN dataSignal (time + 1) = dataSignal time := by
  rw [step]
  simp [negedge, wasHigh, nowLow]

theorem capture (clock resetN dataSignal : Wire) (time : Nat)
    (released : resetN time = true)
    (low : clock time = false) (high : clock (time + 1) = true) :
    sampledDff clock resetN dataSignal (time + 1) = dataSignal time := by
  rw [step]
  simp [postedge, released, low, high]

theorem reset_priority (clock resetN dataSignal : Wire) (time : Nat)
    (active : resetN time = false)
    (low : clock time = false) (high : clock (time + 1) = true) :
    sampledDff clock resetN dataSignal (time + 1) = false := by
  rw [step]
  simp [postedge, active, low, high]

theorem hold (clock resetN dataSignal : Wire) (time : Nat)
    (noClockEdge : postedge clock (time + 1) = false)
    (noResetEdge : negedge resetN (time + 1) = false) :
    sampledDff clock resetN dataSignal (time + 1) =
      sampledDff clock resetN dataSignal time := by
  rw [step]
  simp [noClockEdge, noResetEdge]

theorem release_without_clock (clock resetN dataSignal : Wire) (time : Nat)
    (wasLow : resetN time = false) (nowHigh : resetN (time + 1) = true)
    (noEdge : postedge clock (time + 1) = false) :
    sampledDff clock resetN dataSignal (time + 1) =
      sampledDff clock resetN dataSignal time := by
  apply hold clock resetN dataSignal time noEdge
  simp [negedge, wasLow, nowHigh]

theorem reset_always_low (clock dataSignal : Wire) :
    sampledDff clock (fun _ => false) dataSignal = (fun _ => false) := by
  funext time
  induction time with
  | zero => rfl
  | succ previous hypothesis =>
    rw [step]
    simp [hypothesis]

theorem reset_always_high (clock dataSignal : Wire) :
    sampledDff clock (fun _ => true) dataSignal =
      «always» dataSignal false (postedge clock) := by
  funext time
  induction time with
  | zero => rfl
  | succ previous hypothesis =>
    rw [step]
    simp [negedge, «always», hypothesis]

example : (List.range 6).map
    (sampledDff (fun time => time % 2 == 1) (fun time => time != 2) (fun _ => true)) =
    [false, true, true, false, false, true] := by decide

theorem generated_reset_sampling_gap :
    let clock : Wire := fun time => time == 1
    let resetN : Wire := fun time => time < 2
    let dataSignal : Wire := fun _ => true
    postedge clock 2 = false ∧
      resetN 1 = true ∧ resetN 2 = false ∧
      sampledDff clock resetN dataSignal 2 = true := by
  decide

end AsyncReset
