section
variable {A : Type}
definition f (a b : A) := a
infixl ` ◀ `:65 := f
variables a b : A
#check a ◀ b
end

inductive List (T : Type) : Type
| nil {} : List
| cons   : T → List → List

namespace List
section
variable {T : Type}
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
#check [(10:nat), 20, 30]
end
end List

open List
#check [(10:nat), 20, 40]
#check (10:nat) ◀ 20
