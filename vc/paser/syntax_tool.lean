import Lean
import Lean.Parser.Basic
import vc.paser.token
import vc.paser.to_char
open Lean Parser

to_ascii_term char_' "'"
to_ascii_term char__ "_"
to_ascii_term char_? "?"
to_ascii_term char_! "!"

to_ascii_term char_open_paren "("
to_ascii_term char_close_paren ")"
to_ascii_term char_semicolon ";"
to_ascii_term char_comma ","
to_ascii_term char_less "<"
to_ascii_term char_equal "="
to_ascii_term char_dollor "$"
to_ascii_term char_at "@"

macro "declare_ascii_char_terms " characters:str : command => do
  let mut declarations : Array Lean.Syntax := #[]
  for character in characters.getString.toList do
    let category := Lean.mkIdent (Lean.Name.mkSimple s!"char_{character}")
    let value := Lean.Syntax.mkStrLit (String.singleton character)
    let declaration ← `(command| to_ascii_term $category:ident $value:str)
    declarations := declarations.push declaration.raw
  return ⟨Lean.mkNullNode declarations⟩

macro "declare_lower_ascii_terms" : command =>
  `(command| declare_ascii_char_terms "abcdefghijklmnopqrstuvwxyz")

macro "declare_upper_ascii_terms" : command =>
  `(command| declare_ascii_char_terms "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

macro "declare_digit_ascii_terms" : command =>
  `(command| declare_ascii_char_terms "0123456789")

declare_lower_ascii_terms
declare_upper_ascii_terms
declare_digit_ascii_terms

macro "declare_ascii_keyword_terms" "[" keywords:str,* "]" : command => do
  let mut declarations : Array Lean.Syntax := #[]
  for keyword in keywords.getElems do
    let category := Lean.mkIdent (Lean.Name.mkSimple s!"keyword_{keyword.getString}")
    let declaration ← `(command| to_ascii_term $category:ident $keyword:str)
    declarations := declarations.push declaration.raw
  return ⟨Lean.mkNullNode declarations⟩

declare_ascii_keyword_terms [
  "if", "else", "always", "begin", "end", "posedge", "negedge", "or",
  "module", "macromodule", "endmodule", "input", "output", "wire", "reg"
]

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
