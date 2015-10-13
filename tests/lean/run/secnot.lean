import data.num

section
variable {A : Type}
definition f (a b : A) := a
infixl `◀`:65 := f
variables a b : A
check a ◀ b
end

inductive list (T : Type) : Type :=
| nil {} : list T
| cons   : T → list T → list T

namespace list
section
variable {T : Type}
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
check [(10:num), 20, 30]
end
end list

open list
check [(10:num), 20, 40]
check (10:num) ◀ 20
