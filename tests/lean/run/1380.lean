variable (n v₁ v₂) (hv₁: v₁ < n + 1) (hv₂: v₂ < n + 1)

theorem foo (_: ¬ Fin.mk v₂ hv₂ = Fin.mk v₁ hv₁ ): True := trivial

/--
info: [Meta.Tactic.simp.unify] eq_self:1000, failed to unify
      ?a = ?a
    with
      ⟨v₂, hv₂⟩ = ⟨v₁, hv₁⟩
[Meta.Tactic.simp.rewrite] Fin.mk.injEq:1000, ⟨v₂, hv₂⟩ = ⟨v₁, hv₁⟩ ==> v₂ = v₁
[Meta.Tactic.simp.unify] eq_self:1000, failed to unify
      ?a = ?a
    with
      v₂ = v₁
[Meta.Tactic.simp.discharge] Nat.ne_of_gt discharge ✅️
      v₁ < v₂
  [Meta.Tactic.simp.rewrite] hv:1000, v₁ < v₂ ==> True
[Meta.Tactic.simp.rewrite] Nat.ne_of_gt:1000, v₂ = v₁ ==> False
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp true in
example (hv: v₁ < v₂) : True := foo n v₁ v₂ ‹_› ‹_› (by simp (config := { decide := true }) only [hv, Fin.mk.injEq, Nat.ne_of_gt, Nat.lt_succ_iff])

#check Fin.mk.injEq
