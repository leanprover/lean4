macro_rules [numLit]
 | `($n:numLit) => `("world")

#check 2

macro_rules
  | `($n:numLit) => `("hello")

#check 2

macro_rules [numLit]
  | n => `("boo")

#check 2
