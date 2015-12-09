open nat unit equiv eq

  definition code : ℕ → ℕ → Type₀
  | code 0 0 := unit
  | code (succ n) 0 := empty
  | code 0 (succ m) := empty
  | code (succ n) (succ m) := code n m

  definition refl : Πn, code n n
  | refl 0 := star
  | refl (succ n) := refl n


  definition encode (n m : ℕ) : (n = m) ≃ code n m :=
  equiv.MK (λp, p ▸ refl n)
           (match n m with
            | 0 0 := sorry
            end)
           sorry
           sorry
