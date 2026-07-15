inductive Foo (n : Nat)

class Bar (n: Nat) (α : Type u) (β: outParam (Type u)) where
  bar: Foo n → Fin (n+1) → α → β

instance: Bar n (Foo (n+1)) (Foo n) := sorry

example  (t: Foo (n+2)) (s₁: Foo (n+1)) (s₂: Foo n) (t': Foo n) (hk: k < n + 1) (hm: m < n + 2):
  Bar.bar s₂ ⟨k, hk⟩ (Bar.bar s₁ ⟨m, ‹_›⟩ t) = t' := sorry

variable (t: Foo (n+2)) (s₁: Foo (n+1)) (s₂: Foo n) (t': Foo n) (hk: k < n + 1) (hm: m < n + 2)
example:
  Bar.bar s₂ ⟨k, hk⟩ (Bar.bar s₁ ⟨m, ‹_›⟩ t) = t' := sorry
