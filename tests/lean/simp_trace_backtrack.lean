-- As reported at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.3F.20giving.20nonsense.20lemmas/near/403082483

universe u

-- {α : Type} works as expected, as does specializing this lemma for `Nat`.
@[simp]
theorem tsub_eq_zero_of_le {α : Type u} [LE α] [Sub α] [OfNat α 0] {a b : α} :
    a ≤ b → a - b = 0 := by sorry

@[simp]
theorem ge_iff_le (x y : Nat) : x ≥ y ↔ y ≤ x := Iff.rfl

set_option tactic.simp.trace true

-- This used to report: `Try this: simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub]`
-- because we were not backtracking the "used simps" when the discharger failed.
example {n : Nat} : n = 2 - (n + 1) := by
  simp [Nat.succ_sub_succ_eq_sub]
  sorry
