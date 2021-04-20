macro_rules (kind := numLit)
 | `($n:numLit) => `("world")

#check 2

macro_rules
  | `($n:numLit) => `("hello")

#check 2

macro_rules (kind := numLit)
  | n => `("boo")

#check 2
