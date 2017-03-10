open bool

constant List : Type.{1}
constant nil  : List
constant cons : bool → List → List

infixr `::` := cons
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

#check []
#check [tt]
#check [tt, ff]
#check [tt, ff, ff]
#check tt :: ff :: [tt, ff, ff]
#check tt :: []
constants a b c : bool
#check a :: b :: nil
#check [a, b]
#check [a, b, c]
#check []
