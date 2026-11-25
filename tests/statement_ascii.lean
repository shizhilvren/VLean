import vc.paser.rules
import vc.paser.to_char

#check (ascii_apply "statement" "EOF" [out <= 1'b0;]"EOF" : VL.statement)

example : ascii_apply "statement" "EOF" [out <= 1'b0;]"EOF" =
    VL.statement.nonblocking_assignment
      (VL.nonblocking_assignment.mk
        (VL.variable_lvalue.identifier (VL.identifier.ident `out))
        (VL.expression.primary (VL.primary.number (VL.number.binary_number
          (VL.binary_number.mk VL.binary_base.b
            (VL.binary_value.mk VL.binary_digit.char_0 []) (some 1)))))) := rfl

example : ascii_apply "binary_number" "EOF" [1_0'b1]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_1 []) (some 10) := rfl

example : ascii_apply "identifier" "EOF" [_Out9$]"EOF" =
    VL.identifier.ident (Lean.Name.mkSimple "_Out9$") := rfl

run_cmd do
  let environment ← Lean.getEnv
  for (category, source) in [(`decimal_digit, "u48"), (`decimal_digit, "u57"),
      (`non_zero_decimal_digit, "u49"), (`non_zero_decimal_digit, "u57"),
      (`non_zero_unsigned_number, "u49 u95 u48"),
      (`simple_identifier, "u95 u65 u57 u36")] do
    unless (Lean.Parser.runParserCategory environment category source).isOk do
      throwError "expected {category} to accept {source}"
  for (category, source) in [(`decimal_digit, "u65"),
      (`non_zero_decimal_digit, "u48"), (`non_zero_unsigned_number, "u48 u49"),
      (`simple_identifier, "u57 u65"), (`simple_identifier, "u36 u65")] do
    if (Lean.Parser.runParserCategory environment category source).isOk then
      throwError "expected {category} to reject {source}"
