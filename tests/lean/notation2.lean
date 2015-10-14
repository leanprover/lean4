import data.num
inductive list (T : Type) : Type := nil {} : list T | cons   : T → list T → list T open list notation h :: t  := cons h t notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
infixr `::` := cons
check (1:num) :: 2 :: nil
check (1:num) :: 2 :: 3 :: 4 :: 5 :: nil
