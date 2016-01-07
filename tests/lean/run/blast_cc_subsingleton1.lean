import data.unit
open nat unit

constant f {A : Type} (a : A) {B : Type} (b : B) : nat

constant g : unit → nat

set_option blast.strategy "cc"

example (a b : unit) : g a = g b :=
by blast

example (a c : unit) (b d : nat) : b = d → f a b = f c d :=
by blast

constant h {A B : Type} : A → B → nat

example (a b c d : unit) : h a b = h c d :=
by blast

definition C [reducible] : nat → Type₁
| nat.zero     := unit
| (nat.succ a) := nat

constant g₂ : Π {n : nat}, C n → nat → nat

example (a b : C zero) (c d : nat) : c = d → g₂ a c = g₂ b d :=
by blast
