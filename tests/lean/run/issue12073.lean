-- set_option trace.Meta.injective true

/-!
A mix of propositional and dependent fields
-/
structure Tricky where
  a : Nat
  a' : Nat
  b : 42 < a
  c : Fin a
  d : 23 < c.toNat
  e : a = a'
  f : Fin c.toNat


structure Tricky2 (α : Type u) where
  le : LE α
  decidableLE : DecidableLE α
  lt : let := le; LT α
  beq : let := le; let := decidableLE; BEq α
  lt_iff : let := le; let := lt; ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a
  decidableLT : let := le; let := decidableLE; let := lt; haveI := lt_iff; have := lt_iff; DecidableLT α
  beq_iff_le_and_ge : let := le; let := decidableLE; let := beq; ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a
  le_refl : let := le; ∀ a : α, a ≤ a
  le_trans : let := le; ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
