import Std.WP
import Std.Tactic.Do

/-!
# `coinductive_fixpoint` beside a `vcgen` proof

`Prop` is an assertion lattice, so `Std.WP` carries a `PartialOrder Prop` instance,
re-scoped from `Std.Internal.Order`.

The monotonicity solver of `partial_fixpoint` tries `ind_impl` before `coind_impl`. On a mutual
block that mixes the two directions it must reject `ind_impl`, and it does so only because
`PartialOrder (Prop ×' Prop → Prop)` fails to synthesize. Any `PartialOrder Prop` supplies that
instance through the pointwise lift, so `ind_impl` applies and wins on order.

This test pins how far that reaches. A single coinductive definition and a `vcgen` proof coexist.
A mutual block that mixes `inductive_fixpoint` and `coinductive_fixpoint` over an implication does
not. See the `mixed3` and `mixed4` cases of `coinductive_predicates.lean`, which elaborate when
`Std.WP` is not open.
-/

open Std.WP Lean.Order

set_option mvcgen.warning false

/-! ## What works: a coinductive predicate beside a `vcgen` proof -/

def infseq {α} (R : α → α → Prop) : α → Prop :=
  fun x : α => ∃ y, R x y ∧ infseq R y
  coinductive_fixpoint

theorem cycle_infseq {R : α → α → Prop} (x : α) : R x x → infseq R x := by
  apply @infseq.coinduct α R (fun m => R m m)
  intro x _
  exact Exists.intro x (by trivial)

mutual
  def evenLoop : Prop := oddLoop
  coinductive_fixpoint

  def oddLoop : Prop := evenLoop
  coinductive_fixpoint
end

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

theorem mySum_correct (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  vcgen [mySum] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  with finish

/-! ## What does not work: a mixed mutual block over an implication

Negation is not affected, because `ind_not` names its order in the conclusion. -/

namespace mixed2
  mutual
    def tick : Prop := ¬tock
    inductive_fixpoint

    def tock : Prop := ¬tick
    coinductive_fixpoint
  end
end mixed2

namespace mixed3
/--
error: Could not prove 'mixed3.tick' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    ?f₁ ⟨tick, tock⟩
-/
#guard_msgs in
mutual
  def tick : Prop := tock → tick
  coinductive_fixpoint

  def tock : Prop := tick → tock
  inductive_fixpoint
end
end mixed3

namespace mixed4
/--
error: Could not prove 'mixed4.tock' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    ?f₁ ⟨tick, tock⟩
-/
#guard_msgs in
mutual
  def tick : Prop := tock → tick
  inductive_fixpoint

  def tock : Prop := tick → tock
  coinductive_fixpoint
end
end mixed4
