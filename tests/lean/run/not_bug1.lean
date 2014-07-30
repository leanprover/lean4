import bool
using bool

variable list : Type.{1}
variable nil  : list
variable cons : bool → list → list

infixr `::`:65 := cons
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

check []
check [tt]
check [tt, ff]
check [tt, ff, ff]
check tt :: ff :: [tt, ff, ff]
check tt :: []
variables a b c : bool
check a :: b :: nil
check [a, b]
check [a, b, c]
check []

