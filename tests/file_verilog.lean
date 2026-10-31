import vc.paser.syntax_tree
import vc.paser.token
import vc.paser.rules
import Lean

private def testIdentifier (name : String) : VL.identifier :=
  .ident (Lean.Name.mkSimple name)

private def testPortIdentifier (name : String) : VL.port_identifier :=
  .identifier (testIdentifier name)

private def testPortIdentifiers (head : String) (tail : List String) :
    VL.list_of_port_identifiers :=
  .port_identifier (testPortIdentifier head) (tail.map testPortIdentifier)

private def testPortDeclarations : List VL.port_declaration → VL.list_of_port_declarations
  | [] => .empty
  | head :: tail => .port_declaration head tail

private def testInput (netType : Option VL.net_type) (head : String)
    (tail : List String) : VL.port_declaration :=
  .input_declaration {
    net_type := netType
    list_of_port_identifiers := testPortIdentifiers head tail
  }

private def testOutput (netType : Option VL.net_type) (head : String)
    (tail : List String) : VL.port_declaration :=
  .output_declaration (.output netType (testPortIdentifiers head tail))

private def testOutputReg (head : String) (tail : List String) :
    VL.port_declaration :=
  .output_declaration (.output_reg (testPortIdentifiers head tail))

private def testAssignment (lhs rhs : String) : VL.statement :=
  .nonblocking_assignment {
    variable_lvalue := .identifier (testIdentifier lhs)
    expression := .identifier (testIdentifier rhs)
  }

private def testClockedBlock : VL.statement :=
  .procedural_timing_control_statement {
    procedural_timing_control :=
      .event_control (.event_expression (.posedge (.identifier (testIdentifier "clk"))))
    statement_or_null :=
      .statement (.seq_block (.statements [testAssignment "out" "in_"]))
  }

private def testModule (ports : Option VL.list_of_port_declarations)
    (items : List VL.module_item) : VL.source_text :=
  .description [
    .module_declaration {
      module_keyword := .module
      module_identifier := .identifier (testIdentifier "abc")
      list_of_port_declarations := ports
      module_items := items
    }
  ]

example : identifier[name_d] = testIdentifier "name_d" := rfl

example : list_of_port_identifiers[a,b,c,d] =
    testPortIdentifiers "a" ["b", "c", "d"] := rfl

example : input_declaration[input wire a,b,c,d] =
    ({ net_type := some VL.net_type.wire
       list_of_port_identifiers := testPortIdentifiers "a" ["b", "c", "d"] } :
      VL.input_declaration) := rfl

example : list_of_port_declarations[(input a)] =
    testPortDeclarations [testInput none "a" []] := rfl

example : list_of_port_declarations[
    (input wire a,b,c, output reg c,d, output wire f,e)
  ] =
    testPortDeclarations [
      testInput (some .wire) "a" ["b", "c"],
      testOutputReg "c" ["d"],
      testOutput (some .wire) "f" ["e"]
    ] := rfl

example : list_of_port_declarations[()] = VL.list_of_port_declarations.empty := rfl

example : port_declaration[input wire a,b,c] =
    testInput (some .wire) "a" ["b", "c"] := rfl

example : statement[out <= in_;] = testAssignment "out" "in_" := rfl

example : always_construct[
    always @(posedge clk) begin
      out <= in_;
    end
  ] =
    VL.always_construct.always testClockedBlock := rfl

example : source_text[
    module abc(input wire a,b, output reg c,d, output wire f,e);
      always @(posedge clk) begin
        out <= in_;
      end
    endmodule
  ] =
    testModule
      (some (testPortDeclarations [
        testInput (some .wire) "a" ["b"],
        testOutputReg "c" ["d"],
        testOutput (some .wire) "f" ["e"]
      ]))
      [.module_or_generate_item
        (.always_construct (.always testClockedBlock))] := rfl

example : source_text[
    module abc;
    endmodule
  ] = testModule none [] := rfl
