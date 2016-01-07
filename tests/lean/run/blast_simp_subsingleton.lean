import data.unit
open nat unit

constant f {A : Type} (a : A) {B : Type} (b : B) : nat

constant g : unit → nat

example (a b : unit) : g a = g b :=
by simp

example (a c : unit) (b d : nat) : b = d → f a b = f c d :=
by simp

constant h {A B : Type} : A → B → nat

example (a b c d : unit) : h a b = h c d :=
by simp

definition C [reducible] : nat → Type₁
| nat.zero     := unit
| (nat.succ a) := nat

constant g₂ : Π {n : nat}, C n → nat → nat

example (a b : C zero) (c d : nat) : c = d → g₂ a c = g₂ b d :=
by simp

example (n : nat) (h : zero = n) (a b : C n) (c d : nat) : c = d → g₂ a c = g₂ b d :=
by simp

-- The following one cannot be solved as is
--   example (a c : nat) (b d : unit) : a = c → b = d → f a b = f c d :=
--   by simp
-- But, we can use the following trick

definition f_aux {A B : Type} (a : A) (b : B) := f a b

lemma to_f_aux [simp] {A B : Type} (a : A) (b : B) : f a b = f_aux a b :=
rfl

example (a c : nat) (b d : unit) : a = c → b = d → f a b = f c d :=
by simp
