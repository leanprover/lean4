macro_rules (kind := num)
 | `($n:num) => `("world")

#check 2

macro_rules
  | `($n:num) => `("hello")

#check 2

macro_rules (kind := num)
  | n => `("boo")

#check 2
