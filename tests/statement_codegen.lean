import vc.verilog

namespace StatementCodegenTest

run_cmd do
  let complete := ascii_apply "statement" "EOF" [
    if (en) result <= data; else result <= 1'b0;
  ]"EOF"
  let incomplete := ascii_apply "statement" "EOF" [
    if (en) result <= data;
  ]"EOF"
  unless statementAlwaysWrites complete `result &&
      !statementAlwaysWrites incomplete `result &&
      !statementAlwaysWrites complete `other do
    throwError "incorrect unconditional-write classification"

run_cmd do
  let stmt := ascii_apply "statement" "EOF" [
    begin result <= data; result <= 1'b0; end
  ]"EOF"
  let initial ← `(term| fun _ : Nat => Bool.false)
  let (_, bindings) ← (statementTermAux stmt `result
    { data := initial, enabled := initial }).run #[]
  unless bindings.size == 3 do
    throwError "expected a binding for each assignment and the sequential block"
  let names := bindings.toList.map fun binding => binding.1.getId
  unless names.eraseDups.length == names.length do
    throwError "statement bindings must have distinct names"

run_cmd do
  let stmt := ascii_apply "statement" "EOF" [result <= data;]"EOF"
  let initial ← `(term| fun _ : Nat => Bool.false)
  let code ← statementTerm stmt `result { data := initial, enabled := initial }
  let name := Lean.mkIdent `assignmentData
  let input := Lean.mkIdent `data
  Lean.Elab.Command.elabCommand
    (← `(command| def $name:ident ($input:ident : Wire) : Wire := $(code.data)))
  unless code.event.isNone do
    throwError "a plain assignment must not introduce an event"

example (dataSignal : Wire) : assignmentData dataSignal = dataSignal := rfl

run_cmd do
  let stmt := ascii_apply "statement" "EOF" [
    @(posedge clk) begin result <= data; end
  ]"EOF"
  let code ← code_gen_statement stmt `result
  let name := Lean.mkIdent `directD
  let clock := Lean.mkIdent `clk
  let input := Lean.mkIdent `data
  Lean.Elab.Command.elabCommand
    (← `(command| def $name:ident ($clock:ident : Wire) ($input:ident : Wire) : Reg := $code))

example : (List.range 4).map
    (directD (fun time => time % 2 == 1) (fun _ => true)) =
    [false, true, true, true] := by decide

verilog "EOF" [
  module nested(input wire clk, en, choose, override, data, other, output reg result);
    always @(posedge clk) begin
      if (en) begin
        if (choose) result <= data;
        else result <= other;
      end
      if (override) result <= 1'b0;
    end
  endmodule
]"EOF"

example : (List.range 4).map
    (nested (fun time => time % 2 == 1) (fun _ => true) (fun _ => true)
      (fun _ => false) (fun _ => true) (fun _ => false)) =
    [false, true, true, true] := by decide

example : (List.range 4).map
    (nested (fun time => time % 2 == 1) (fun _ => true) (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => true)) =
    [false, true, true, true] := by decide

example : (List.range 4).map
    (nested (fun time => time % 2 == 1) (fun _ => true) (fun _ => true)
      (fun _ => true) (fun _ => true) (fun _ => true)) =
    [false, false, false, false] := by decide

example : (List.range 6).map
    (nested (fun time => time % 2 == 1) (fun time => time == 0) (fun _ => true)
      (fun _ => false) (fun time => time == 0) (fun _ => false)) =
    [false, true, true, true, true, true] := by decide

end StatementCodegenTest
