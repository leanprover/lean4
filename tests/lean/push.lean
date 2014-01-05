import Int.

variable first : Bool

scope
  variables a b c : Int
  variable f : Int -> Int
  eval f a
pop::scope

eval f a -- should produce an error

print environment 1

scope
  infixl 100 ++ : Int::add
  check 10 ++ 20
pop::scope

check 10 ++ 20 -- should produce an error

pop::scope -- should produce an error