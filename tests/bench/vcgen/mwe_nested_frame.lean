/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

/-!
# MWE: `vcgen` cost-framing over a *2-level* (stateful-base) assertion lattice

`tests/elab/vcgenTickFrames.lean` shows `vcgen` cost-framing working for `TickM := StateM Nat`,
whose assertion lattice is the **flat** `Nat → Prop` (the single cost coordinate). The *same*
construction over a **stateful base monad** — e.g. `ComplexiT (StateM σ)` in the `loom-complexity`
project, assertion lattice `Nat → (σ → Prop)` (a cost coordinate **and** a base-state coordinate) —
*used to* fail (`vcgen [foo] with finish` reported `finish failed`). It is **now fixed** by the
`reduceFrameConj?` / `reduceFrameImp?` fallbacks in `VCGen/Solve.lean` (see "The fix" below). This
file kept the diagnosis that pinned the root cause down.

Concretely, with `foo : ComplexiT (StateM Unit) Unit := do withTick ()` and
`fooSpec : ⦃fun acc _ => acc = 0⦄ foo ⦃fun _ acc _ => acc ≤ 1⦄`, after the registered frameproc
fires the raw stuck goal is (`s✝¹` = cost, `s✝` = base `Unit` state):

    (s✝¹ = 0) ⊑ costConj s✝¹ (wp (Gadget.skipFrame foo) (fun a => (costConj s✝¹) -⋆ Q) ⊥) s✝¹ s✝
                            └──────────────────── costConj applied to TWO coords ───────────┘

The registered *direct* split `le_costConj_point_apply : pre ⊑ costConj c R n` matches `costConj`
applied to **one** coordinate. Over the 2-level lattice `vcgen` has introduced the extra base-state
arg, so the goal is `costConj c R n s` (one application deeper); the split can't unify, returns
`none`, and the raw `costConj` goal — with the un-specced inner `wp` still inside it — is dumped on
`finish`, which cannot evaluate it.

## What this file pins down (each `example` below verifies a claim)

* **§A — the built-in stateful `meet` split is NOT the culprit.** `vcgen` decomposes
  `pre ⊑ (guard ⊓ shift) coords` over a *2-level* lattice for every operand shape we tried (opaque,
  λ, cost-shifted, `⌜·⌝`-guarded — i.e. the exact `costConj` shape). In `loom-complexity` it was
  further verified to split even when an operand is `wp (Gadget.skipFrame prog) …` (reaching the
  inner `wp`, i.e. getting *past* the meet). So once the meet is exposed, the split fires fine,
  over both coordinates.

* **§B — `costConj` is NOT defeq to its `meet` form.** The pi-lattice meet is a genuinely different
  term (`meet_apply` is a *lemma*, not `rfl`). So a fix cannot reduce the *current* `costConj` with
  `Meta.unfoldDefinition?` + `MVarId.replaceTargetDefEq` (the `rfl` it relies on does not hold); the
  meet form must be exposed either by *defining* `costConj` meet-first, or by a propositional
  `replaceTargetEq`.

## The fix (implemented in `VCGen/Solve.lean`)

Two fallback steps in `solve`, run *after* `splitLatticeOp?` so flat lattices keep their direct split:

* `reduceFrameConj?` — for a registered frameproc `conj` the direct split couldn't peel, delta-unfold
  the `conj` (defined **meet-first**, §B) to expose its `meet`, then **`unfoldReducible`-normalize**.
  That last step was the real blocker: the meet split's `applyChecked` only unifies against the
  reducible-normal form (state types `StateM σ`, `Tick` sit behind reducible defs). `applyChecked`'s
  `+debug` retry diagnoses exactly this ("succeeded after `unfoldReducible`-normalization"). The next
  `solve` iteration's meet split then peels both coordinates and specs the inner `wp`. Fires every
  iteration, so it recurses at each framing level.

* `reduceFrameImp?` — for ≥2 cost calls, the residual wand `upperAdjoint (conj c) R` wraps the *next*
  call's un-specced `wp` and the direct `impSplit` can't peel the extra coord. Rewrite it via a
  registered `FrameProc.impReduce` equation (here `costConj_imp : upperAdjoint (costConj c) R =
  fun m => R (m+c)`), then beta + `unfoldReducible`, exposing the inner `wp` for the spec step.

The leftover VCs (budget guard `c ≤ n`, `WP.Frames`) close under `with finish`.
-/

open Lean Order Std Internal.Do

/-- The 2-level cost-frame operator: a guard on the cost coordinate `n`, met — on the base-state
lattice `σ → Prop` — with the body run on the remaining cost `n - r`. The analog of the flat
`costConj` of `vcgenTickFrames.lean`, but over `Nat → (σ → Prop)`. -/
def costConj {σ : Type} (r : Nat) (b : Nat → (σ → Prop)) : Nat → (σ → Prop) :=
  fun n => ⌜r ≤ n⌝ ⊓ b (n - r)

/-! ## §A — the built-in stateful `meet` split decomposes 2-level meets

Each goal is a bare lattice entailment whose RHS is a `meet` of two `Nat → (Unit → Prop)` functions;
`vcgen` introduces the cost arg *and* the base-state arg and fires the meet split across **both**
coordinates, leaving one obligation per operand, which `finish` discharges. -/

/-- Two `⊤` operands over the 2-level lattice `Nat → Unit → Prop`: the split introduces the cost arg
`n` *and* the base-state arg `s`, then closes `pre ⊑ ⊤` on each side. -/
example (pre : Nat → Unit → Prop) :
    pre ⊑ (fun _ => (⊤ : Unit → Prop)) ⊓ (fun _ => (⊤ : Unit → Prop)) := by
  vcgen with finish [top_apply]

-- The exact `costConj` shape — `⌜·⌝`-guard ⊓ cost-shift — over the 2-level lattice. The split peels
-- **both** coordinates (`s✝¹` the cost, `s✝` the base state), leaving the guard obligation (`vc1`)
-- and the shifted-body obligation (`vc2`), each trivially true. (In `vcgenTickFrames.lean` the
-- analogous split has only the single cost coordinate; here it must — and does — recurse into base.)
/--
error: unsolved goals
case vc1
b : Nat → PUnit → Prop
c s✝¹ : Nat
s✝ : PUnit
⊢ (c ≤ s✝¹ ∧ b (s✝¹ - c) s✝) ⊑ ⌜c ≤ s✝¹⌝ s✝

case vc2
b : Nat → PUnit → Prop
c s✝¹ : Nat
s✝ : PUnit
⊢ (c ≤ s✝¹ ∧ b (s✝¹ - c) s✝) ⊑ b (s✝¹ - c) s✝
-/
#guard_msgs in
example (b : Nat → Unit → Prop) (c : Nat) :
    (fun n s => c ≤ n ∧ b (n - c) s) ⊑ (fun n => ⌜c ≤ n⌝) ⊓ (fun n => b (n - c)) := by
  vcgen

/-! ## §B — `costConj` is not definitionally its `meet` form -/

/-- The `rfl` that an `unfoldDefinition?` + `replaceTargetDefEq` reduction would rely on **fails**;
the equation holds only *propositionally* (`meet_apply` is a lemma, not `rfl`). -/
example {σ : Type} (c : Nat) (b : Nat → σ → Prop) :
    costConj c b = (fun n => ⌜c ≤ n⌝) ⊓ (fun n => b (n - c)) := by
  fail_if_success rfl
  funext n; simp only [costConj, meet_apply]
