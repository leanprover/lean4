def Nat.hasDecEq: (a: Nat) → (b: Nat) → Decidable (Eq a b)
|   0,   0 => isTrue rfl
| n+1,   0
|   0, n+1 => isFalse Nat.noConfusion
| n+1, m+1 =>
  match h:hasDecEq n m with -- it works without `h:`
  | isTrue heq => isTrue  (heq ▸ rfl)
  | isFalse hne => isFalse (Nat.noConfusion · (λ heq  => absurd heq hne))
termination_by a b => (a, b)

set_option pp.proofs true
#print Nat.hasDecEq
#print Nat.hasDecEq._unary
