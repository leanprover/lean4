import data.num
open num

definition foo1 a b c := a + b + (c:num)

definition foo2 (a : num) b c := a + b + c

definition foo3 a b (c : num) := a + b + c

definition foo4 (a b c : num) := a + b + c

definition foo5 (a b c) : num := a + b + c

definition foo6 {a b c} : num := a + b + c

definition foo7 a b c : num := a + b + c  -- Error

definition foo8 (a b c : num) : num := a + b + c

definition foo9 (a : num) (b : num) (c : num) : num := a + b + c

definition foo10 (a : num) b (c : num) : num := a + b + c
