import vc.paser.rules

example : binary_value[
  'b000
] = VL.binary_value.mk .char_0 [.char_0, .char_0] := rfl

example : binary_value[ 'b1_0 ] =
    VL.binary_value.mk .char_1 [.char_0] := rfl

example : binary_value[ 'b1_0_____1 ] =
    VL.binary_value.mk .char_1 [.char_0, .char_1] := rfl

example : binary_value[ 'B0xXzZ? ] =
    VL.binary_value.mk .char_0
      [.x_digit .x, .x_digit .x, .z_digit .z, .z_digit .z, .z_digit .z] := rfl

#reduce binary_value[
  'b000
]
