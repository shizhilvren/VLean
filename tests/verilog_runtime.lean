import vc.runtime.Signals

namespace RuntimeTests

example (clock dataSignal : Wire) :
    «always» dataSignal Bool.false (postedge clock) 0 = Bool.false := rfl

example (clock dataSignal : Wire) (time : Nat) :
        «always» dataSignal Bool.false (postedge clock) (time + 1) =
      (if !clock time && clock (time + 1) then dataSignal time
             else «always» dataSignal Bool.false (postedge clock) time) := by
    cases previous : clock time <;> cases current : clock (time + 1) <;>
        simp [«always», postedge, previous, current]

example : (List.range 6).map
    («always» (fun time => time == 1) Bool.false (postedge (fun time => time % 4 >= 2))) =
    [Bool.false, Bool.false, Bool.true, Bool.true, Bool.true, Bool.true] := by decide

example : (List.range 6).map
    («always» (fun _ => Bool.true) Bool.false (postedge (fun _ => Bool.true))) =
    List.replicate 6 Bool.false := by decide

example : (List.range 6).map
    («always» (fun _ => Bool.true) Bool.false (postedge (fun _ => Bool.false))) =
    List.replicate 6 Bool.false := by decide

end RuntimeTests
