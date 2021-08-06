
set_option pp.explicit true
-- set_option trace.compiler.boxed true

partial def contains : String → Char → Nat → Bool
| s, c, i =>
  if s.atEnd i then false
  else if s.get i == c then true
       else contains s c (s.next i)

def main : IO Unit :=
let s1 := "hello";
IO.println (contains s1 'a' 0) *>
IO.println (contains s1 'o' 0)
