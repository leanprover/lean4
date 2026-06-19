import Init.Data.Order.Lemmas
import Init.Data.Order.FactoriesExtra
open Std

/-!
Regression test for `backward.isDefEq.projField`.

When `projField` restricts a class-projection `self` comparison to the projected field, the `self`
argument is handled like an instance-implicit argument of `isDefEqArgs`. A bare unassigned instance
metavariable must be *unified* from the comparison (its first-pass "easy case"), not eagerly
synthesized: synthesizing it resolves it against the *ambient* context, which during type class
resolution can pin a candidate's instance metavariable to the *opposite* order. That silently turns a
viable `Refl`/`Trans` candidate into a non-matching one (its relation reduces to the flipped order),
so synthesis falls through to a dead-end candidate and fails.

This reconstructs the mid-file instance environment of `Init.Data.Order.Opposite` (which is why we do
not import that module): the dedicated opposite `Refl`/`Trans`/`Total` instances are in scope, but the
bundled `IsPreorder` one is not. Synthesizing `IsPreorder` for the opposite order then exercises the
`le_refl`/`le_trans` synthesis that previously diverged between the two settings.
-/

/-- Local copy of `LE.opposite` (defined in `Init.Data.Order.Opposite`). -/
@[instance_reducible] def LE.opp (le : LE α) : LE α where
  le a b := b ≤ a

instance instReflOpp {i : LE α} [Refl (α := α) (· ≤ ·)] :
    haveI := i.opp; Refl (α := α) (· ≤ ·) :=
  letI := i.opp; { refl a := letI := i; le_refl a }

instance instTransOpp {i : LE α} [Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop)] :
    haveI := i.opp; Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop) :=
  { trans hab hbc := by simp [LE.le] at hab hbc ⊢; exact Trans.trans hbc hab }

instance instTotalOpp {i : LE α} [Total (α := α) (· ≤ ·)] :
    haveI := i.opp; Total (α := α) (· ≤ ·) :=
  letI := i.opp; { total a b := letI := i; le_total (a := b) (b := a) }

-- With `projField` off, synthesizing `IsPreorder` for the opposite order succeeds.
set_option backward.isDefEq.projField false in
example {α : Type u} {i : LE α} [IsPreorder α] : haveI := i.opp; IsPreorder α :=
  letI := i.opp
  { le_refl a := le_refl a
    le_trans _ _ _ := le_trans }

-- With `projField` on (the default), the same synthesis must also succeed: the bare instance
-- metavariable of the `IsPreorder`-derived `Refl`/`Trans` candidate is unified to the base order
-- rather than synthesized to the ambient opposite order.
set_option backward.isDefEq.projField true in
example {α : Type u} {i : LE α} [IsPreorder α] : haveI := i.opp; IsPreorder α :=
  letI := i.opp
  { le_refl a := le_refl a
    le_trans _ _ _ := le_trans }
