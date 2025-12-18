module
-- grind fails, but also produces a panic.

@[grind] inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ x y z, R x y → star R y z → star R x z

set_option grind.debug true
inductive com: Type where
  | SKIP
  | ASSIGN

inductive cexec : com → Prop where

@[grind] inductive red : com × Nat → com × Nat → Prop where
  | red_assign: ∀ s, red (.ASSIGN, s) (.SKIP, 0)

theorem issue3 (s s' : Nat) (c : com) :
  star red (c, s) (.SKIP, s') → cexec c := by
    intro h
    generalize heq1 : (c, s) = h1
    generalize heq2 : (com.SKIP, s') = h2
    rw [heq1, heq2] at h
    induction h
    case star_refl =>
      sorry
    case star_step r _ a_ih =>
      /-
      The following `grind` used to trigger an assertion violation:
      _private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkEqc Lean.Meta.Tactic.Grind.Inv:29:10: assertion violation: isSameExpr e ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv._hyg.31.0 )
      -/
      fail_if_success grind
      sorry
