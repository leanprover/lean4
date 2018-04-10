inductive foo : bool → Type
| Z  : foo ff
| O  : foo ff → foo tt
| E  : foo tt → foo ff

open foo

definition to_nat : ∀ {b}, foo b → nat
| .(ff) Z     := 0
| .(tt) (O n) := to_nat n + 1
| .(ff) (E n) := to_nat n + 1

example : to_nat (E (O Z)) = 2 :=
rfl

example : to_nat Z = 0 :=
rfl

example (a : foo ff) : to_nat (O a) = to_nat a + 1 :=
rfl

example (a : foo tt) : to_nat (E a) = to_nat a + 1 :=
rfl
