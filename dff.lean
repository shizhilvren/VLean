-- This module serves as the root of the `Vc` library.
-- Import modules here that should be built as part of the library.
import Vc.Basic
import Std

-- One-bit vectors provide arithmetic modulo 2 without a Mathlib dependency.

def dff (in_ : Wire) (clk : Wire) : Reg :=
  let rec out (n : Nat) : Bool :=
    if n = 0 then
      false
    else
      if clk (n - 1) < clk n then
        in_ (n - 1)
      else
        out (n - 1)
  out

theorem dff_hold (in_ : Wire) (clk : Wire) (n : Nat) (stable : n > 0) (no_rising : ¬ clk (n - 1) < clk n) : dff in_ clk n = dff in_ clk (n - 1) := by
  rw [dff]
  rw [dff.out]
  let n_neq_zero := Nat.pos_iff_ne_zero.mp stable
  have h := no_rising
  simp [n_neq_zero]
  simp [h]

theorem dff_posedge (in_ : Wire) (clk : Wire) (n : Nat) (stable : n > 0) (rising : clk (n - 1) < clk n) : dff in_ clk n = in_ (n - 1) := by
  rw [dff]
  rw [dff.out]
  let n_neq_zero := Nat.pos_iff_ne_zero.mp stable
  have h := rising
  simp [n_neq_zero]
  simp [h]

def clk (n : Nat) : Bool :=
  if n <= 5 then
    false
  else
    true

def in_ (n : Nat) : Bool := true

#eval visualize (dff in_ clk) 0 10
