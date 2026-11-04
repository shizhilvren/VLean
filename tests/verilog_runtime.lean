import vc.runtime.Signals

namespace RuntimeTests

example (clock dataSignal : Wire) : posedgeSignal clock dataSignal 0 = Bool.false := rfl

example (clock dataSignal : Wire) (time : Nat) :
    posedgeSignal clock dataSignal (time + 1) =
      (if !clock time && clock (time + 1) then dataSignal time
       else posedgeSignal clock dataSignal time) := rfl

example : (List.range 6).map
    (posedgeSignal (fun time => time % 4 >= 2) (fun time => time == 1)) =
    [Bool.false, Bool.false, Bool.true, Bool.true, Bool.true, Bool.true] := by decide

example : (List.range 6).map
    (posedgeSignal (fun _ => Bool.true) (fun _ => Bool.true)) =
    List.replicate 6 Bool.false := by decide

example : (List.range 6).map
    (posedgeSignal (fun _ => Bool.false) (fun _ => Bool.true)) =
    List.replicate 6 Bool.false := by decide

end RuntimeTests
