import vc.verilog

namespace CodegenAsciiTest

run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module reset_ff(input wire clk, rst, data, output reg result);
    always @(posedge clk or negedge rst) begin
      if (!rst) result <= 1'b0;
      else result <= data;
    end
  endmodule
]"EOF")

run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module enabled_ff(input wire clk, en, data, output reg result);
    always @(posedge clk) begin
      if (en) result <= data;
    end
  endmodule
]"EOF")

run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module falling_ff(input wire clk, data, output reg result);
    always @(negedge clk) begin
      result <= data;
    end
  endmodule
]"EOF")

run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module inverted_ff(input wire clk, data, output reg result);
    always @(posedge clk) begin
      result <= !data;
    end
  endmodule
]"EOF")

run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module last_wins(input wire clk, output reg result);
    always @(posedge clk) begin
      result <= 1'b0;
      result <= 1'b1;
    end
  endmodule
]"EOF")

example (clock reset data : Wire) : reset_ff clock reset data 0 = false := rfl

example : (List.range 5).map
    (reset_ff (fun time => time % 2 == 1) (fun _ => false) (fun _ => true)) =
    [false, false, false, false, false] := by decide

example : (List.range 5).map
    (reset_ff (fun time => time % 2 == 1) (fun _ => true) (fun _ => true)) =
    [false, true, true, true, true] := by decide

example : (List.range 5).map
    (enabled_ff (fun time => time % 2 == 1) (fun time => time == 0)
      (fun time => time == 0)) =
    [false, true, true, true, true] := by decide

example : (List.range 4).map
    (falling_ff (fun time => time % 2 == 0) (fun _ => true)) =
    [false, true, true, true] := by decide

example : (List.range 4).map
    (inverted_ff (fun time => time % 2 == 1) (fun _ => false)) =
    [false, true, true, true] := by decide

example : (List.range 4).map (last_wins (fun time => time % 2 == 1)) =
    [false, true, true, true] := by decide

example : reset_ff (fun _ => false) (fun time => time < 2) (fun _ => true) 2 = true := by
  decide

/-- error: x/z constants are not supported by the Bool runtime -/
#guard_msgs in
run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module unknown_value(input wire clk, output reg result);
    always @(posedge clk) begin result <= 1'bx; end
  endmodule
]"EOF")

/-- error: only single-bit binary constants are supported -/
#guard_msgs in
run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module wide_value(input wire clk, output reg result);
    always @(posedge clk) begin result <= 2'b01; end
  endmodule
]"EOF")

/-- error: multiple always blocks drive result -/
#guard_msgs in
run_cmd code_gen_source_text (ascii_apply "source_text" "EOF" [
  module multiple_drivers(input wire clk, data, output reg result);
    always @(posedge clk) begin result <= data; end
    always @(negedge clk) begin result <= data; end
  endmodule
]"EOF")

end CodegenAsciiTest
