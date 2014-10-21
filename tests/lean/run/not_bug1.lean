import logic
open bool

constant list : Type.{1}
constant nil  : list
constant cons : bool → list → list

infixr `::` := cons
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

check []
check [tt]
check [tt, ff]
check [tt, ff, ff]
check tt :: ff :: [tt, ff, ff]
check tt :: []
constants a b c : bool
check a :: b :: nil
check [a, b]
check [a, b, c]
check []
