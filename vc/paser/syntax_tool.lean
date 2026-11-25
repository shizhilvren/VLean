import Lean
import Lean.Parser.Basic
import vc.paser.token
import vc.paser.to_char
open Lean Parser

to_ascii_term char_0 "0"
to_ascii_term char_1 "1"
to_ascii_term char_2 "2"
to_ascii_term char_3 "3"
to_ascii_term char_4 "4"
to_ascii_term char_5 "5"
to_ascii_term char_6 "6"
to_ascii_term char_7 "7"
to_ascii_term char_8 "8"
to_ascii_term char_9 "9"
to_ascii_term char_' "'"
-- to_ascii_term char_apostrophe "'"
to_ascii_term char__ "_"
to_ascii_term char_? "?"
to_ascii_term char_semicolon ";"
to_ascii_term char_less "<"
to_ascii_term char_equal "="
to_ascii_term char_dollor "$"

to_ascii_term char_a "a"
to_ascii_term char_b "b"
to_ascii_term char_c "c"
to_ascii_term char_d "d"
to_ascii_term char_e "e"
to_ascii_term char_f "f"
to_ascii_term char_g "g"
to_ascii_term char_h "h"
to_ascii_term char_i "i"
to_ascii_term char_j "j"
to_ascii_term char_k "k"
to_ascii_term char_l "l"
to_ascii_term char_m "m"
to_ascii_term char_n "n"
to_ascii_term char_o "o"
to_ascii_term char_p "p"
to_ascii_term char_q "q"
to_ascii_term char_r "r"
to_ascii_term char_s "s"
to_ascii_term char_t "t"
to_ascii_term char_u "u"
to_ascii_term char_v "v"
to_ascii_term char_w "w"
to_ascii_term char_x "x"
to_ascii_term char_y "y"
to_ascii_term char_z "z"

to_ascii_term char_A "A"
to_ascii_term char_B "B"
to_ascii_term char_C "C"
to_ascii_term char_D "D"
to_ascii_term char_E "E"
to_ascii_term char_F "F"
to_ascii_term char_G "G"
to_ascii_term char_H "H"
to_ascii_term char_I "I"
to_ascii_term char_J "J"
to_ascii_term char_K "K"
to_ascii_term char_L "L"
to_ascii_term char_M "M"
to_ascii_term char_N "N"
to_ascii_term char_O "O"
to_ascii_term char_P "P"
to_ascii_term char_Q "Q"
to_ascii_term char_R "R"
to_ascii_term char_S "S"
to_ascii_term char_T "T"
to_ascii_term char_U "U"
to_ascii_term char_V "V"
to_ascii_term char_W "W"
to_ascii_term char_X "X"
to_ascii_term char_Y "Y"
to_ascii_term char_Z "Z"

to_ascii_term char_space " "
to_ascii_term char_tab "\t"
to_ascii_term char_line_feed "\n"
to_ascii_term char_carriage_return "\r"

declare_syntax_cat ascii_space
syntax (char_space <|> char_tab <|> char_line_feed <|> char_carriage_return) : ascii_space
declare_syntax_cat ascii_spaces
syntax (ascii_space*) : ascii_spaces


declare_syntax_cat ascii_lower_alpha
syntax (char_a <|> char_b <|> char_c <|> char_d <|> char_e <|> char_f <|> char_g <|> char_h <|> char_i <|> char_j <|> char_k <|> char_l <|> char_m <|> char_n <|> char_o <|> char_p <|> char_q <|> char_r <|> char_s <|> char_t <|> char_u <|> char_v <|> char_w <|> char_x <|> char_y <|> char_z) : ascii_lower_alpha

declare_syntax_cat ascii_upper_alpha
syntax (char_A <|> char_B <|> char_C <|> char_D <|> char_E <|> char_F <|> char_G <|> char_H <|> char_I <|> char_J <|> char_K <|> char_L <|> char_M <|> char_N <|> char_O <|> char_P <|> char_Q <|> char_R <|> char_S <|> char_T <|> char_U <|> char_V <|> char_W <|> char_X <|> char_Y <|> char_Z) : ascii_upper_alpha
