import vc.paser.rules
import vc.paser.to_char

def resetSource : VL.source_text := ascii_apply "source_text" "EOF" [
  module abc (
      input  wire clk, rst, in ,
      output reg  out
  );
      always @(posedge clk or negedge rst) begin
          if (!rst)
              out <= 1'b0;
          else
              out <= in;
      end
  endmodule
]"EOF"

#reduce resetSource

private def port (name : String) : VL.port_identifier :=
  VL.port_identifier.identifier (VL.identifier.ident (Lean.Name.mkSimple name))

example : resetSource =
    VL.source_text.description [VL.description.module_declaration
      (VL.module_declaration.mk VL.module_keyword.module
        (VL.module_identifier.identifier (VL.identifier.ident `abc))
        (some (VL.list_of_port_declarations.port_declaration
          (VL.port_declaration.input_declaration
            (VL.input_declaration.mk (some VL.net_type.wire)
              (VL.list_of_port_identifiers.port_identifier (port "clk")
                [port "rst", port "in"])))
          [VL.port_declaration.output_declaration
            (VL.output_declaration.output_reg
              (VL.list_of_port_identifiers.port_identifier (port "out") []))]))
        [VL.module_item.module_or_generate_item
          (VL.module_or_generate_item.always_construct
            (ascii_apply "always_construct" "EOF" [
              always @(posedge clk or negedge rst) begin
                if (!rst) out <= 1'b0;
                else out <= in;
              end
            ]"EOF"))])] := rfl

example : ascii_apply "source_text" "EOF" [module empty (); endmodule]"EOF" =
    VL.source_text.description [VL.description.module_declaration
      (VL.module_declaration.mk VL.module_keyword.module
        (VL.module_identifier.identifier (VL.identifier.ident `empty))
        (some VL.list_of_port_declarations.empty) [])] := rfl

example : ascii_apply "source_text" "EOF" [module empty; endmodule]"EOF" =
    VL.source_text.description [VL.description.module_declaration
      (VL.module_declaration.mk VL.module_keyword.module
        (VL.module_identifier.identifier (VL.identifier.ident `empty)) none [])] := rfl
