import data.prod data.num
inductive list (T : Type) : Type := nil {} : list T | cons   : T → list T → list T open list notation h :: t  := cons h t notation `[` l:(foldr `, ` (h t, cons h t) nil) `]` := l
open prod num
constants a b : num
check [a, b, b]
check (a, true, a = b, b)
check (a, b)
check [(1:num), 2+2, 3]
