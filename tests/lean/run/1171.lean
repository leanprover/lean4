def Nat.hasDecEq: (a: Nat) → (b: Nat) → Decidable (Eq a b)
|   0,   0 => isTrue rfl
| n+1,   0
|   0, n+1 => isFalse Nat.noConfusion
| n+1, m+1 =>
  match h:hasDecEq n m with -- it works without `h:`
  | ⟨true,  heq⟩ => isTrue  (heq.1 rfl ▸ rfl)
  | ⟨false, hne⟩ => isFalse (Nat.noConfusion · (λ heq  => absurd heq (nomatch hne.2 ·)))
termination_by _ a b => (a, b)

set_option pp.proofs true
#print Nat.hasDecEq
#print Nat.hasDecEq._unary
