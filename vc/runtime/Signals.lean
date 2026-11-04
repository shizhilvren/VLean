abbrev Wire := Nat → Bool
abbrev Reg := Nat → Bool

def postedge (clock : Wire) : Wire
  | 0 => Bool.false
  | time + 1 =>
    if clock time == false && clock (time + 1) == true then
      Bool.true
    else
      Bool.false

def negedge (clock : Wire) : Wire
  | 0 => Bool.false
  | time + 1 =>
    if clock time == true && clock (time + 1) == false then
      Bool.true
    else
      Bool.false

def always (d: Wire) (zero_value:Bool) (cond: Wire) : Reg
  | 0 => zero_value
  | time + 1 =>
    if cond (time + 1) then
      d time
    else
      always d zero_value cond time

def «if» (cond: Wire) (then_branch else_branch: Wire) : Wire
  | t =>
    if cond t then
      then_branch t
    else
      else_branch t

theorem always.zero (d: Wire) (zero_value: Bool) (cond: Wire) : always d zero_value cond 0 = zero_value := by
  simp [always]

theorem always.condition (d: Wire) (zero_value: Bool) (cond: Wire) (t: Nat) (h: 0 < t) : cond t →  always d zero_value cond t = d (t - 1) := by
  match t with
  | 0 => contradiction
  | time + 1 =>
    rw [always]
    intro h_cond
    simp [h_cond]

theorem always.hold (d: Wire) (zero_value: Bool) (cond: Wire) (t: Nat) (h: 0 < t) : ¬cond t →  always d zero_value cond t = always d zero_value cond (t - 1) := by
  match t with
  | 0 => contradiction
  | time + 1 =>
    rw [always]
    intro h_cond
    simp [h_cond]

theorem postedge.post (clk: Wire) (t: Nat) (h : 0 < t ) : clk (t - 1) == false && clk t == true ↔  postedge clk t = Bool.true := by
  cases t
  · contradiction
  · simp [postedge]

theorem postedge.not_post (clk: Wire) (t: Nat) (h : 0 < t ) : ¬(clk (t - 1) == false && clk t == true) ↔  postedge clk t = Bool.false := by
  cases t
  · contradiction
  · simp [postedge]

theorem postedge.zero (clk: Wire) : postedge clk 0 = Bool.false := by
  simp [postedge]


theorem negedge.neg (clk: Wire) (t: Nat) (h : 0 < t ) : clk (t - 1) == true && clk t == false ↔  negedge clk t = Bool.true := by
  cases t
  · contradiction
  · simp [negedge]

theorem negedge.not_neg (clk: Wire) (t: Nat) (h : 0 < t ) : ¬(clk (t - 1) == true && clk t == false) ↔  negedge clk t = Bool.false := by
  cases t
  · contradiction
  · simp [negedge]

theorem negedge.zero (clk: Wire) : negedge clk 0 = Bool.false := by
  simp [negedge]
