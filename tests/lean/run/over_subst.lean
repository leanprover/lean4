import logic

namespace nat
variable nat : Type.{1}
variable add : nat → nat → nat
variable le : nat → nat → Prop
variable one : nat
infixl `+`:65 := add
infix `≤`:50 := le
axiom add_assoc (a b c : nat) : (a + b) + c = a + (b + c)
axiom add_le_left {a b : nat} (H : a ≤ b) (c : nat) : c + a ≤ c + b
end nat

namespace int
variable int : Type.{1}
variable add : int → int → int
variable le : int → int → Prop
variable one : int
infixl `+`:65 := add
infix `≤`:50  := le
axiom add_assoc (a b c : int) : (a + b) + c = a + (b + c)
axiom add_le_left {a b : int} (H : a ≤ b) (c : int) : c + a ≤ c + b
abbreviation lt (a b : int) := a + one ≤ b
infix `<`:50  := lt
end int

using int
using nat

set_option unifier.expensive true

theorem add_lt_left {a b : int} (H : a < b) (c : int) : c + a < c + b :=
subst (symm (add_assoc c a one)) (add_le_left H c)
