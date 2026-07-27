/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases
import Driver

set_option mvcgen.warning false

/-!
# VCGen Test Suite

Runs all VCGen test cases at small sizes (n=10) to verify correctness.
Each case exercises a different aspect of the VC generation:

- `AddSubCancel`: Basic add/sub loop in `StateM`
- `AddSubCancelDeep`: Same loop through a deep monad transformer stack
- `AddSubCancelSimp`: Like `AddSubCancel` but using simp/equational specs
- `GetThrowSet`: Exception handling with `ExceptT`/`StateM`
- `PurePrecond`: Pure hypotheses `⌜φ⌝` in preconditions
- `ReaderState`: `ReaderT`/`StateM` combination
- `DiteSplit`: Dependent if-then-else (`if h : cond then ...`)
- `MatchIota`: Pattern matching with concrete discriminants (iota-reduced, no split)
- `MatchSplit`: Pattern matching with symbolic discriminant (state), exercising match split
-/

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval do
  runBenchUsingTactic ``AddSubCancel.Goal [``AddSubCancel.loop, ``AddSubCancel.step]
    `(tactic| vcgen) `(tactic| grind) [10]
  runBenchUsingTactic ``AddSubCancelDeep.Goal [``AddSubCancelDeep.loop, ``AddSubCancelDeep.step]
    `(tactic| vcgen) `(tactic| grind) [10]
  runBenchUsingTactic ``AddSubCancelSimp.Goal [``AddSubCancelSimp.loop, ``AddSubCancelSimp.step]
    `(tactic| vcgen) `(tactic| grind) [10]
  runBenchUsingTactic ``LetBinding.Goal [``LetBinding.loop, ``LetBinding.step]
    `(tactic| vcgen) `(tactic| grind) [10]
  runBenchUsingTactic ``GetThrowSet.Goal [``GetThrowSet.loop, ``GetThrowSet.step]
    `(tactic| vcgen) `(tactic| sorry) [10]
  -- `vcgen with finish`: grind integrated into VCGen loop
  runBenchUsingTactic ``GetThrowSet.Goal [``GetThrowSet.loop, ``GetThrowSet.step]
    `(tactic| vcgen with finish) `(tactic| fail) [10]
  -- `vcgen with finish` on AddSubCancel
  runBenchUsingTactic ``AddSubCancel.Goal [``AddSubCancel.loop, ``AddSubCancel.step]
    `(tactic| vcgen with finish) `(tactic| fail) [10]
  runBenchUsingTactic ``PurePrecond.Goal [``PurePrecond.loop, ``PurePrecond.step]
    `(tactic| vcgen) `(tactic| fail) [10]
  runBenchUsingTactic ``ReaderState.Goal [``ReaderState.loop, ``ReaderState.step]
    `(tactic| vcgen) `(tactic| sorry) [10]
  runBenchUsingTactic ``DiteSplit.Goal [``DiteSplit.loop, ``DiteSplit.step]
    `(tactic| vcgen) `(tactic| sorry) [10]
  runBenchUsingTactic ``MatchIota.Goal [``MatchIota.loop, ``MatchIota.step]
    `(tactic| vcgen) `(tactic| sorry) [10]
  runBenchUsingTactic ``MatchSplit.Goal [``MatchSplit.loop, ``MatchSplit.step]
    `(tactic| vcgen) `(tactic| grind) [10]

-- Verify `simplifying_assumptions [Nat.add_assoc]` works end-to-end with `simp only` unfolding.
/--
trace: s✝ : Nat
a✝ : s✝ = 0
h✝⁹ : ¬0 < s✝
h✝⁸ : ¬1 < s✝ + 1
h✝⁷ : ¬2 < s✝ + 2
h✝⁶ : ¬3 < s✝ + 3
h✝⁵ : ¬4 < s✝ + 4
h✝⁴ : ¬5 < s✝ + 5
h✝³ : ¬6 < s✝ + 6
h✝² : ¬7 < s✝ + 7
h✝¹ : ¬8 < s✝ + 8
h✝ : ¬9 < s✝ + 9
⊢ s✝ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10
-/
#guard_msgs in
open GetThrowSet in
example : Goal 10 := by
  simp only [Goal, loop, step]
  vcgen simplifying_assumptions [Nat.add_assoc]
  case vc11 => trace_state; grind
  all_goals grind

-- Verify that the let-binding code paths are exercised.
-- `unfold` (unlike `simp only`) preserves letE nodes in the program, exercising:
-- let-hoist, let-intro (non-duplicable value), and fvar-zeta (let-bound program head).
-- Run with `set_option trace.Elab.Tactic.Do.vcgen true` to see the traces.
open LetBinding in
example : ∀ post, ⦃post⦄ step 5 ⦃fun _ => post⦄ := by
  unfold step
  intro post
  vcgen
  grind
