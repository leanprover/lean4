--
inductive List (T : Type) : Type | nil {} : List | cons   : T → List → List open List notation h :: t  := cons h t notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
infixr `::` := cons
#check (1:num) :: 2 :: nil
#check (1:num) :: 2 :: 3 :: 4 :: 5 :: nil
