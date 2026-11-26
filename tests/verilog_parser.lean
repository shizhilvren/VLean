import vc.paser.rules
import vc.paser.to_char

set_option pp.rawOnError true
set_option trace.Elab.step true
set_option trace.Elab.definition true
set_option trace.Elab.command true

namespace VerilogParserTest

private def identifier (name : String) : VL.identifier :=
  VL.identifier.ident (Lean.Name.mkSimple name)

private def port (name : String) : VL.port_identifier :=
  VL.port_identifier.identifier (identifier name)

private def ports (first : String) (rest : List String := []) : VL.list_of_port_identifiers :=
  VL.list_of_port_identifiers.port_identifier (port first) (rest.map port)

private def inputPort (kind : Option VL.net_type) (first : String)
    (rest : List String := []) : VL.port_declaration :=
  VL.port_declaration.input_declaration (VL.input_declaration.mk kind (ports first rest))

private def mixedPorts : VL.list_of_port_declarations :=
  VL.list_of_port_declarations.port_declaration
    (inputPort (some VL.net_type.wire) "a" ["b"])
    [VL.port_declaration.output_declaration (VL.output_declaration.output_reg (ports "c" ["d"])),
     VL.port_declaration.output_declaration (VL.output_declaration.output (some VL.net_type.wire) (ports "f")),
     VL.port_declaration.output_declaration (VL.output_declaration.output none (ports "e"))]

private def assignment (target value : String) : VL.statement :=
  VL.statement.nonblocking_assignment
    (VL.nonblocking_assignment.mk (VL.variable_lvalue.identifier (identifier target))
      (VL.expression.identifier (identifier value)))

private def clockedBlock (event : VL.event_expression) (body : VL.statement) : VL.always_construct :=
  VL.always_construct.always
    (VL.statement.procedural_timing_control_statement
      (VL.procedural_timing_control_statement.mk
        (VL.procedural_timing_control.event_control (VL.event_control.event_expression event))
        (VL.statement_or_null.statement (VL.statement.seq_block (VL.seq_block.statements [body])))))

private def source (declarations : VL.list_of_port_declarations)
    (body : List VL.always_construct := []) : VL.source_text :=
  VL.source_text.description [VL.description.module_declaration
    (VL.module_declaration.mk VL.module_keyword.module
      (VL.module_identifier.identifier (identifier "abc")) (some declarations)
      (body.map fun item => VL.module_item.module_or_generate_item
        (VL.module_or_generate_item.always_construct item)))]

private def resetBody : VL.statement :=
  VL.statement.conditional_statement
    (VL.conditional_statement.mk
      (VL.expression.unary_operator VL.unary_operator.not
        (VL.primary.hierarchical_identifier (VL.hierarchical_identifier.identifier (identifier "rst"))))
      (VL.statement_or_null.statement
        (VL.statement.nonblocking_assignment
          (VL.nonblocking_assignment.mk (VL.variable_lvalue.identifier (identifier "out"))
            (VL.expression.primary (VL.primary.number (VL.number.binary_number
              (VL.binary_number.mk VL.binary_base.b
                (VL.binary_value.mk VL.binary_digit.char_0 []) (some 1))))))))
      (some (VL.statement_or_null.statement (assignment "out" "in"))))

example : ascii_apply "list_of_port_declarations" "EOF" [(input a)]"EOF" =
    VL.list_of_port_declarations.port_declaration (inputPort none "a") [] := rfl

example : ascii_apply "input_declaration" "EOF" [input wire a,b,  c,d]"EOF" =
    VL.input_declaration.mk (some VL.net_type.wire) (ports "a" ["b", "c", "d"]) := rfl

example : ascii_apply "list_of_port_identifiers" "EOF" [a,b,c,d]"EOF" =
    ports "a" ["b", "c", "d"] := rfl

example : ascii_apply "list_of_port_declarations" "EOF" [(input wire a,b,c)]"EOF" =
    VL.list_of_port_declarations.port_declaration
      (inputPort (some VL.net_type.wire) "a" ["b", "c"]) [] := rfl

example : ascii_apply "list_of_port_declarations" "EOF" [(input wire a, input wire f)]"EOF" =
    VL.list_of_port_declarations.port_declaration
      (inputPort (some VL.net_type.wire) "a")
      [inputPort (some VL.net_type.wire) "f"] := rfl

example : ascii_apply "list_of_port_declarations" "EOF" [
  (input wire a,b, output reg c,d, output wire f, output e)
  ]"EOF" = mixedPorts := rfl

example : ascii_apply "source_text" "EOF" [
  module abc(input wire a,b, output reg c,d, output wire f, output e);
  endmodule
]"EOF" = source mixedPorts := rfl

example : ascii_apply "list_of_port_declarations" "EOF" [()]"EOF" =
    VL.list_of_port_declarations.empty := rfl

example : ascii_apply "list_of_port_declarations" "EOF" [
  ( )
  ]"EOF" = VL.list_of_port_declarations.empty := rfl

example : ascii_apply "port_declaration" "EOF" [input wire a,b,c]"EOF" =
    inputPort (some VL.net_type.wire) "a" ["b", "c"] := rfl

example : ascii_apply "always_construct" "EOF" [
  always @(posedge clk) begin
    out <= in_;
  end
]"EOF" = clockedBlock (VL.event_expression.posedge (VL.expression.identifier (identifier "clk")))
    (assignment "out" "in_") := rfl

example : ascii_apply "source_text" "EOF" [
  module abc(input wire a,b, output reg c,d, output wire f, output e);
    always @(posedge clk) begin
      out <= in_;
    end
  endmodule
]"EOF" = source mixedPorts
    [clockedBlock (VL.event_expression.posedge (VL.expression.identifier (identifier "clk")))
      (assignment "out" "in_")] := rfl

example : ascii_apply "binary_digit" "EOF" [0]"EOF" = VL.binary_digit.char_0 := rfl
example : ascii_apply "binary_digit" "EOF" [1]"EOF" = VL.binary_digit.char_1 := rfl
example : ascii_apply "x_digit" "EOF" [x]"EOF" = VL.x_digit.x := rfl
example : ascii_apply "x_digit" "EOF" [X]"EOF" = VL.x_digit.x := rfl
example : ascii_apply "z_digit" "EOF" [z]"EOF" = VL.z_digit.z := rfl
example : ascii_apply "z_digit" "EOF" [Z]"EOF" = VL.z_digit.z := rfl
example : ascii_apply "z_digit" "EOF" [?]"EOF" = VL.z_digit.z := rfl
example : ascii_apply "binary_base" "EOF" ['b]"EOF" = VL.binary_base.b := rfl

example : ascii_apply "binary_value" "EOF" [000]"EOF" =
    VL.binary_value.mk VL.binary_digit.char_0 [VL.binary_digit.char_0, VL.binary_digit.char_0] := rfl

example : ascii_apply "binary_value" "EOF" [1_0]"EOF" =
    VL.binary_value.mk VL.binary_digit.char_1 [VL.binary_digit.char_0] := rfl

example : ascii_apply "binary_value" "EOF" [1_0_____1]"EOF" =
    VL.binary_value.mk VL.binary_digit.char_1 [VL.binary_digit.char_0, VL.binary_digit.char_1] := rfl

example : ascii_apply "binary_number" "EOF" ['b1_0]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_1 [VL.binary_digit.char_0]) := rfl

example : ascii_apply "source_text" "EOF" [
  module abc (
    input wire clk, rst, in,
    output reg out
  );
    always @(posedge clk or negedge rst) begin
      if (!rst)
        out <= 1'b0;
      else
        out <= (in);
    end
  endmodule
]"EOF" = source
    (VL.list_of_port_declarations.port_declaration
      (inputPort (some VL.net_type.wire) "clk" ["rst", "in"])
      [VL.port_declaration.output_declaration (VL.output_declaration.output_reg (ports "out"))])
    [clockedBlock
      (VL.event_expression.or
        (VL.event_expression.posedge (VL.expression.identifier (identifier "clk")))
        (VL.event_expression.negedge (VL.expression.identifier (identifier "rst"))))
      resetBody] := rfl

example : ascii_apply "statement" "EOF" [out <= in_;]"EOF" = assignment "out" "in_" := rfl

example : ascii_apply "statement" "EOF" [out <= ( in );]"EOF" = assignment "out" "in" := rfl

example : ascii_apply "statement" "EOF" [out <= (( in ));]"EOF" = assignment "out" "in" := rfl

example : ascii_apply "identifier" "EOF" [name_d]"EOF" = identifier "name_d" := rfl

end VerilogParserTest
