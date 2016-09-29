constant foo.f {A B : Type} : (A → B) → (B → A)
constant bla.f {A : Type}   : (A → nat) → (A → nat)

open foo bla

noncomputable example : nat → bool :=
f (λ b, bool.cases_on b 0 1)
