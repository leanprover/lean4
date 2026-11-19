-- Mutually recursive definitions using casesOn on indexed types should not panic.
-- https://github.com/leanprover/lean4/issues/13015

inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

mutual
def zipWithAux (f : α → β → γ) (a : α) (as : Vect α m) (bs : Vect β n) : n = m + 1 → γ × Vect γ m :=
  Vect.casesOn (motive := λ k _ ↦ k = m + 1 → γ × Vect γ m) bs
    (nil := λ h ↦ Nat.noConfusion h)
    (cons := λ (b : β) (k : Nat) (bs : Vect β k) h ↦
      Nat.noConfusion h (λ h1 : k = m ↦
        ((f a b), (zipWith f as (h1 ▸ bs) rfl)))
    )

def zipWith (f : α → β → γ) {n : Nat} (as : Vect α n) (bs : Vect β n) : n = n → Vect γ n :=
  Vect.casesOn (motive := λ m _ ↦ n = m → Vect γ m) as
    (nil := λ _ ↦ Vect.nil)
    (cons := λ (a : α) (m : Nat) (as : Vect α m) h ↦
      let p := zipWithAux f a as bs h
      Vect.cons p.1 p.2
    )
end
