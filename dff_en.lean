import vc.Basic
import Std

def dff_en (in_ : Wire) (clk : Wire) (en : Wire) (reset : Wire) : Reg :=
  let rec out_1 (n : Nat) : Bool :=
    if n = 0 then
      false
    else
      if clk (n - 1) < clk n then
        if en (n - 1) then
          in_ (n-1)
        else
          out_1 (n - 1)
      else
        out_1 (n - 1)
  let rec out_2 (n : Nat) : Bool :=
    if n = 0 then
      false
    else
      if ¬ reset (n - 1)=reset n then
        if ¬ reset (n) then
          false
        else
          out_1 (n )
      else
        out_2 (n - 1)
  let rec out (n : Nat) : Bool :=
    let out_1_v := out_1 n
    let out_2_v := out_2 n
    if out_1_v = out_2_v then
      out_1_v
    else
      out_2_v
  out

def main : IO Unit := do
  let inputValues := [true, false, false, true, true, false, false, true, true, false]
  let clockValues := [false, true, false, true, false, true, false, true, false, true]
  let enableValues := [true, true, false, false, true, true, true, true, true, true]
  let resetValues := [true, true, true, true, true, true, true, true, false, false]
  let inputWire : Wire := fun time => inputValues.getD time false
  let clockWire : Wire := fun time => clockValues.getD time false
  let enableWire : Wire := fun time => enableValues.getD time false
  let resetWire : Wire := fun time => resetValues.getD time true
  let output := dff_en inputWire clockWire enableWire resetWire
  let bit : Bool -> Nat := fun value => if value then 1 else 0
  let pad := fun (width : Nat) (value : Nat) =>
    let text := toString value
    String.ofList (List.replicate (width - text.length) ' ') ++ text
  IO.println "time | in | clk | en | reset | out"
  for time in List.range inputValues.length do
    IO.println s!"{pad 4 time} | {pad 2 (bit (inputWire time))} | {pad 3 (bit (clockWire time))} | {pad 2 (bit (enableWire time))} | {pad 5 (bit (resetWire time))} | {pad 3 (bit (output time))}"

#eval main
