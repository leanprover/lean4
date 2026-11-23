--
set_option pp.explicit true
-- set_option trace.compiler.boxed true

partial def contains : String → Char → String.Pos.Raw → Bool
| s, c, i =>
  if String.Pos.Raw.atEnd s i then false
  else if String.Pos.Raw.get s i == c then true
       else contains s c (String.Pos.Raw.next s i)

def main : IO Unit :=
let s1 := "hello";
IO.println (contains s1 'a' 0) *>
IO.println (contains s1 'o' 0)
