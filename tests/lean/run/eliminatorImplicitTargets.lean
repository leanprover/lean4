inductive Equality {α : Type u} : α → α → Type u
| refl {a : α} : Equality a a

open Equality

@[eliminator]
def ind {α : Type u} (motive : ∀ (a b : α) (p : Equality a b), Sort v)
  {a : α} (πrefl : motive a a refl) {b : α} (p : Equality a b) : motive a b p :=
@Equality.casesOn α a (λ b p => motive a a refl → motive a b p) b p
  (λ (ε : motive a a refl) => ε) πrefl

def symm {α : Type u} {a b : α} (p : Equality a b) : Equality b a :=
by { induction p; apply refl }
