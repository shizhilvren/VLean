abbrev Wire := Nat → Bool
abbrev Reg := Nat → Bool

def posedgeSignal (clock dataSignal : Wire) : Reg
  | 0 => Bool.false
  | time + 1 =>
    if !clock time && clock (time + 1) then
      dataSignal time
    else
      posedgeSignal clock dataSignal time
