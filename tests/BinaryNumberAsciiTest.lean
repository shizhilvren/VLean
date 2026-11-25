import vc.paser.rules
import vc.paser.to_char

example : ascii_apply "binary_value" "EOF" [1]"EOF" =
  VL.binary_value.mk VL.binary_digit.char_1 [] := rfl

example : ascii_apply "binary_value" "EOF" [0__1___]"EOF" =
  VL.binary_value.mk VL.binary_digit.char_0 [VL.binary_digit.char_1] := rfl

example : ascii_apply "binary_value" "EOF" [x_X_z_Z_?]"EOF" =
  VL.binary_value.mk (VL.binary_digit.x_digit VL.x_digit.x)
    [VL.binary_digit.x_digit VL.x_digit.x,
     VL.binary_digit.z_digit VL.z_digit.z,
     VL.binary_digit.z_digit VL.z_digit.z,
     VL.binary_digit.z_digit VL.z_digit.z] := rfl

example : ascii_apply "x_digit" "EOF" [x]"EOF" = VL.x_digit.x := rfl
example : ascii_apply "x_digit" "EOF" [X]"EOF" = VL.x_digit.x := rfl
example : ascii_apply "z_digit" "EOF" [z]"EOF" = VL.z_digit.z := rfl
example : ascii_apply "z_digit" "EOF" [Z]"EOF" = VL.z_digit.z := rfl
example : ascii_apply "z_digit" "EOF" [?]"EOF" = VL.z_digit.z := rfl

example : ascii_apply "binary_number" "EOF" ['b000]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_0
        [VL.binary_digit.char_0, VL.binary_digit.char_0]) := rfl

example : ascii_apply "binary_number" "EOF" ['b01]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_0
        [VL.binary_digit.char_1]) := rfl

example : ascii_apply "binary_number" "EOF" ['b1_1]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_1
        [VL.binary_digit.char_1]) := rfl

example : ascii_apply "binary_number" "EOF" ['b1]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk VL.binary_digit.char_1 []) := rfl

example : ascii_apply "binary_number" "EOF" ['bx]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk (VL.binary_digit.x_digit VL.x_digit.x) []) := rfl

example : ascii_apply "binary_number" "EOF" ['BX_x_z____1_0]"EOF" =
    VL.binary_number.mk VL.binary_base.b
      (VL.binary_value.mk (VL.binary_digit.x_digit VL.x_digit.x)
        [VL.binary_digit.x_digit VL.x_digit.x,
         VL.binary_digit.z_digit VL.z_digit.z,
         VL.binary_digit.char_1, VL.binary_digit.char_0]) := rfl
