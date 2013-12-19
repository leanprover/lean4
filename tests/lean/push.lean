
Variable first : Bool

Push
  Variables a b c : Int
  Variable f : Int -> Int
  Eval f a
Pop

Eval f a (* should produce an error *)

Show Environment 1

Push
  Infixl 100 ++ : Int::add
  Check 10 ++ 20
Pop

Check 10 ++ 20 (* should produce an error *)

Pop (* should produce an error *)