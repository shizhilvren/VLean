import vc.verilog

example : outputPorts (some (ascii_apply "list_of_port_declarations" "EOF" [
    (input wire x, output reg a,b, output wire c,d, output e)
  ]"EOF")) = [(`a, ``Reg), (`b, ``Reg), (`c, ``Wire), (`d, ``Wire), (`e, ``Wire)] := rfl

example : outputPorts (some (ascii_apply "list_of_port_declarations" "EOF" [()]"EOF")) = [] := rfl
example : outputPorts none = [] := rfl
example : outputPorts (some (ascii_apply "list_of_port_declarations" "EOF" [(input wire x)]"EOF")) = [] := rfl

example : inputPorts (some (ascii_apply "list_of_port_declarations" "EOF" [
    (input a,b, output reg c, input wire x)
  ]"EOF")) = [(`a, ``Wire), (`b, ``Wire), (`x, ``Wire)] := rfl

example : inputPortNames (some (ascii_apply "list_of_port_declarations" "EOF" [
    (input wire a,b, output reg c,d, input wire x,y)
  ]"EOF")) = [`a, `b, `x, `y] := rfl

example : inputPortNames (some (ascii_apply "list_of_port_declarations" "EOF" [()]"EOF")) = [] := rfl
example : inputPortNames none = [] := rfl

namespace portParameterTests

run_cmd do
  let item := ascii_apply "module_item" "EOF" [
    always @(posedge clk) begin
      out <= in;
    end
  ]"EOF"
  match moduleItemAssignments item with
  | .ok [assignment] =>
    unless assignment.target == `out && assignment.dependencies == [Lean.Name.mkSimple "in"] &&
        assignment.clock.toList.flatMap expressionVariables == [`clk] &&
        expressionVariables assignment.value == [Lean.Name.mkSimple "in"] do
      throwError "incorrect module assignment extraction"
  | _ => throwError "expected one module assignment"

verilog "EOF" [
  module no_inputs();
  endmodule
  module multiple_inputs(input wire x,y, output wire result, input wire z);
  endmodule
  module multiple_outputs(input wire x, output reg a,b, output wire c);
  endmodule
  module D(input wire clk, input wire in, output reg out);
    always @(posedge clk) begin
      out <= in;
    end
  endmodule
]"EOF"

theorem Dff_posedge (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) < clock n) :
  portParameterTests.D clock dataSignal n = dataSignal (n-1) := by
    cases n with
  | zero => simp at h
  | succ time =>
    cases previous : clock time <;>
      cases current : clock (time + 1) <;>
        simp_all [D, «always», postedge]
    exact absurd clkEdge (by decide)

  -- rw [portParameterTests.D]
  -- rw [posedgeSignal.eq_def]
  -- -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- let n_neq_0 := Nat.pos_iff_ne_zero.mp h
  -- cases n with
  -- | zero => simp at h
  -- | succ time =>
  --   simp
  --   simp at clkEdge
  --   cases pre : clock time with
  --   | true =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --       exact absurd clkEdge (by decide)
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --   | false =>
  --     cases cut : clock (time + 1) with
  --     | false =>
  --       simp [pre, cut] at clkEdge
  --     | true =>
  --       simp [pre, cut] at clkEdge
  --       let f_eq_f :false = false :=by rfl
  --       simp

verilog "EOF" [
  module Dff(input wire clk, input wire in,a, output reg out, output reg out1);
    always @(posedge clk) begin
      out <= in ;
      out1 <= a;
    end
  endmodule
]"EOF"
#print Dff

example : Unit := no_inputs
example : Wire → Wire → Reg := D
theorem D_eq_always (clock dataSignal : Wire) :
  D clock dataSignal = «always» dataSignal Bool.false (postedge clock) := rfl
example (clock first second : Wire) :
  Dff clock first second =
    («always» first Bool.false (postedge clock),
     «always» second Bool.false (postedge clock)) := rfl
example (clock dataSignal : Wire) : D clock dataSignal 0 = Bool.false := rfl
example (clock dataSignal : Wire) (time : Nat) :
    D clock dataSignal (time + 1) =
      (if !clock time && clock (time + 1) then dataSignal time else D clock dataSignal time) := by
  cases previous : clock time <;> cases current : clock (time + 1) <;>
    simp [D, «always», postedge, previous, current]
example (clock dataSignal : Wire) (time : Nat)
    (low : clock time = Bool.false) (high : clock (time + 1) = Bool.true) :
    D clock dataSignal (time + 1) = dataSignal time := by
  simp [D, «always», postedge, low, high]
example (clock dataSignal : Wire) (time : Nat) (stable : clock (time + 1) = clock time) :
  D clock dataSignal (time + 1) = D clock dataSignal time := by
  cases previous : clock time <;> simp [D, «always», postedge, stable, previous]
example : (List.range 6).map (D (fun time => time % 2 == 1) (fun _ => Bool.true)) =
    [Bool.false, Bool.true, Bool.true, Bool.true, Bool.true, Bool.true] := by decide
example : multiple_inputs = fun (_: Wire) (_: Nat->Bool) (_: Wire) =>
    (fun _ => Bool.false : Wire) := rfl
example : multiple_inputs (fun _ => Bool.false) (fun _ => Bool.true)
    (fun _ => Bool.false) 0 = Bool.false := rfl
example : Wire → Reg × Reg × Wire := multiple_outputs
example : (multiple_outputs (fun _ => Bool.true)).1 0 = Bool.false := rfl
example : (multiple_outputs (fun _ => Bool.true)).2.1 0 = Bool.false := rfl
example : (multiple_outputs (fun _ => Bool.true)).2.2 0 = Bool.false := rfl

end portParameterTests

namespace generatedFunctions

verilog[ascii_apply "source_text" "EOF" [
  module generated_example(input wire x);
  endmodule
]"EOF"]

#check generated_example
#print generated_example

example : (Nat → Bool) → Unit := generated_example

end generatedFunctions

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (`generatedFunctions).isPrefixOf name then
      Lean.logInfo m!"{name}"

-- set_option trace.Elab.step true
-- set_option trace.Elab.definition true
set_option trace.Elab.command true

verilog "EOF" [
  module D(input wire clk, input wire in, output reg out);
    always @(posedge clk) begin
      out <= in;
    end
  endmodule
]"EOF"

#print D

theorem D_eq_always (clock dataSignal : Wire) :
  D clock dataSignal = «always» dataSignal Bool.false (postedge clock) := rfl

theorem Dff_hold (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) = clock n) :
  D clock dataSignal n = D clock dataSignal (n-1) := by
  rw [D_eq_always]
  apply «always».hold dataSignal Bool.false (postedge clock) n h
  have noEdge : postedge clock n = Bool.false :=
    (postedge.not_post clock n h).mp (by
      rw [clkEdge]
      cases clock n <;> decide)
  simp [noEdge]


theorem Dff_posedge (clock dataSignal : Wire) (n:Nat) (h:n>0) (clkEdge : clock (n-1) < clock n) :
  D clock dataSignal n = dataSignal (n-1) := by
  rw [D_eq_always]
  apply «always».condition dataSignal Bool.false (postedge clock) n h
  apply (postedge.post clock n h).mp
  cases previous : clock (n - 1) <;>
    cases current : clock n <;>
      simp_all
  exact absurd clkEdge (by decide)
