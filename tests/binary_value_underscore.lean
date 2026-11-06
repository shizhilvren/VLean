import vc.paser.rules

example : binary_value[ 1_0 ] =
    VL.binary_value.mk VL.binary_digit.char_1 [VL.binary_digit.char_0] := rfl

example : binary_value[ 1_0_____1 ] =
    VL.binary_value.mk VL.binary_digit.char_1
      [VL.binary_digit.char_0, VL.binary_digit.char_1] := rfl

example : binary_value[ 000 ] =
    VL.binary_value.mk VL.binary_digit.char_0
      [VL.binary_digit.char_0, VL.binary_digit.char_0] := rfl

example : binary_value[ x ] =
  VL.binary_value.mk (VL.binary_digit.x_digit VL.x_digit.x) [] := rfl

example : binary_value[ Z ] =
  VL.binary_value.mk (VL.binary_digit.z_digit VL.z_digit.z) [] := rfl
