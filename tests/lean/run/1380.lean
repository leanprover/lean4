theorem Nat.ne_of_gt {a b : Nat} (h : a < b) : b ≠ a := sorry
theorem Nat.lt_succ_iff {m n : Nat} : m < succ n ↔ m ≤ n := sorry

variable (n v₁ v₂) (hv₁: v₁ < n + 1) (hv₂: v₂ < n + 1)
theorem foo (_: ¬ Fin.mk v₂ hv₂ = Fin.mk v₁ hv₁ ): True := trivial
set_option trace.Meta.Tactic.simp true in
example (hv: v₁ < v₂) : True := foo n v₁ v₂ ‹_› ‹_› (by simp (config := { decide := true }) only [hv, Fin.mk.injEq, Nat.ne_of_gt, Nat.lt_succ_iff])

#check Fin.mk.injEq
