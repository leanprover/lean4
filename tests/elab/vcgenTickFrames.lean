/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

/-!
# A frame-internalizing cost weakest precondition

This file demonstrates a *residuated* frame operator that is **not** the lattice meet, and a cost
weakest precondition that **bakes the frame rule in**. The monad is `TickM`, Cslib's cost-counting
monad: `tick` incurs one unit of cost. Assertions are `Nat → Prop`, predicates on the accumulated
cost.

The frame operator takes a plain **cost** as its resource: `costConj r b = fun n => r ≤ n ∧ b (n - r)`
holds the budget `r` aside and runs `b` on the remaining cost `n - r`. This is the separation-logic
`⋆` for the resource type `R = Nat`, and its residual `PreservesSup.upperAdjoint (costConj r) b = fun m => b (m + r)`
is the corresponding magic wand `-⋆`, a plain cost shift.

Part 1 is the reusable core, `instance (r) : PreservesSup (costConj r)`, together with the
additive action law `costConj_add` that composes two budgets.

Part 2 builds the cost monad `TickM := StateM Nat` and the frame-internalizing wp `TickM.wp` as the
`PreservesSup.frameClosure` of `costConj`. Its point characterization is
`TickM.wp x Q n ↔ ∀ r, WP.wp x.run (fun a m => r ≤ m ∧ Q a (m - r)) (n + r)`: every program must
thread the held budget `r` through untouched, so `TickM.wp tick Q n = Q () (n + 1)` while a
cost-discarding program has `TickM.wp _ Q n = False` for every postcondition.

Part 3 is the payoff: since `TickM.wp` is a `frameClosure`, *every* program frames *every* budget
`F : Nat` with respect to `costConj`, with no cost-additivity hypothesis (`frames_costConj`).

Part 5 registers a `@[frameproc]` so plain `vcgen` infers the budget from the current cost and frames
`TickM` calls automatically; Part 6 chains two loops and frames the second by the cost the first
accrued.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do

/-! ## Part 1: the cost `PreservesSup` instance (reusable core) -/

/-- `⨆` over a `Prop`-valued predicate is the existential `∃ p, c p ∧ p`. -/
theorem sup_prop_eq (c : Prop → Prop) : ((CompleteLattice.sup c) : Prop) = ∃ p, c p ∧ p :=
  Lean.Order.is_sup_unique (CompleteLattice.sup_spec c) (propSup_is_sup c)

/-- Pointwise membership in `CompleteLattice.sup s` on the `Nat → Prop` lattice. -/
theorem sup_fun_apply (s : (Nat → Prop) → Prop) (n : Nat) :
    (CompleteLattice.sup s) n = ∃ f, s f ∧ f n := by
  rw [sup_apply, sup_prop_eq]
  apply propext
  constructor
  · rintro ⟨p, ⟨f, hf, rfl⟩, hp⟩; exact ⟨f, hf, hp⟩
  · rintro ⟨f, hf, hfn⟩; exact ⟨f n, ⟨f, hf, rfl⟩, hfn⟩

/-- The cost frame operator: hold the budget `r` aside and run `b` on the remaining cost. `costConj r b n`
holds iff there is at least `r` cost available and `b` holds of the rest. This is separating
conjunction for the `Nat` resource. -/
def costConj (r : Nat) (b : Nat → Prop) : Nat → Prop := fun n => r ≤ n ∧ b (n - r)

@[inherit_doc costConj] local infixr:67 " ⋆ " => costConj

/-- The cost magic wand: the upper adjoint of the slice `costConj r`, a plain shift
`r -⋆ b = fun m => b (m + r)`. -/
local notation:60 lhs:61 " -⋆ " rhs:61 => Lean.Order.PreservesSup.upperAdjoint (costConj lhs) rhs

instance (r : Nat) : PreservesSup (costConj r) where
  map_sup s := by
    funext n
    apply propext
    constructor
    · rintro ⟨hle, hsup⟩
      rw [sup_fun_apply] at hsup
      obtain ⟨f, hf, hfn⟩ := hsup
      rw [sup_fun_apply]
      exact ⟨costConj r f, ⟨f, hf, rfl⟩, hle, hfn⟩
    · rintro hrhs
      rw [sup_fun_apply] at hrhs
      obtain ⟨g, ⟨x, hx, rfl⟩, hle, hxnr⟩ := hrhs
      show r ≤ n ∧ (CompleteLattice.sup s) (n - r)
      rw [sup_fun_apply]
      exact ⟨hle, x, hx, hxnr⟩

/-- Sanity check: the upper adjoint of `costConj r` is the cost magic wand `fun m => b (m + r)`, a
plain shift of the budget back onto the counter. -/
@[grind =]
theorem costConj_imp (r : Nat) (b : Nat → Prop) :
    r -⋆ b = (fun m => b (m + r)) := by
  apply PartialOrder.rel_antisymm
  · -- `imp ⊑ shift`: every `x` with `costConj r x ⊑ b` is below the shift.
    unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx m hxm
    refine hx (m + r) ?_
    exact ⟨by omega, by simpa using hxm⟩
  · -- `shift ⊑ imp`: the shift is in the set `{x | costConj r x ⊑ b}`.
    refine PreservesSup.le_upperAdjoint (costConj r) (b := b) (x := fun m => b (m + r)) ?_
    intro n
    rintro ⟨hle, hb⟩
    simpa [show n - r + r = n by omega] using hb

/-- The additive action law of `costConj`: composing two budgets `r` and `r'` is the same as holding
them one after the other. -/
theorem costConj_add (r r' : Nat) (a : Nat → Prop) :
    costConj (r + r') a = costConj r (costConj r' a) := by
  funext n
  show (r + r' ≤ n ∧ a (n - (r + r'))) = (r ≤ n ∧ r' ≤ n - r ∧ a (n - r - r'))
  rw [Nat.sub_sub]
  apply propext
  constructor
  · rintro ⟨h, ha⟩; exact ⟨by omega, by omega, ha⟩
  · rintro ⟨h1, h2, ha⟩; exact ⟨by omega, ha⟩

/-! ## Part 2: the cost monad `TickM` and the frame-internalizing `TickM.wp` -/

/-- A cost-tracking monad: a state monad whose state is the accumulated cost counter. A `def` wrapper
(not an `abbrev`) so it carries its own frame-internalizing `WP` interpretation, distinct from the
`StateM` one it is built from, and so `vcgen` reasons about `TickM.wp`. -/
def TickM (α : Type) : Type := StateM Nat α

instance : Monad TickM := inferInstanceAs (Monad (StateM Nat))

/-- A `TickM` program as the underlying `StateM` program, whose `WP` is the base (non-framed) wp. -/
@[reducible] def TickM.run {α : Type} (x : TickM α) : StateM Nat α := x

/-- The cost primitive: incur one unit of cost by incrementing the counter. -/
def tick : TickM Unit := show StateM Nat Unit from modify (· + 1)

/-- The **frame-internalizing** cost weakest precondition: the `PreservesSup.frameClosure` of `costConj`
over the base `StateM` wp `WP.wp x.run · E`. The frame rule is internal by construction (`tickFrames`).
The point characterization is `TickM.wp_eq_forall`. -/
def TickM.wp {α : Type} (x : TickM α) (Q : α → Nat → Prop) (E : EPost.Nil) : Nat → Prop :=
  PreservesSup.frameClosure costConj (WP.wp x.run · E) Q

/-- The point characterization: the meet over *all* budgets collapses to running the base wp under the
held-budget postcondition `r ≤ m ∧ Q a (m - r)`, offset by `r`. -/
theorem TickM.wp_eq_forall {α : Type} (x : TickM α) (Q : α → Nat → Prop) (E : EPost.Nil) (n : Nat) :
    TickM.wp x Q E n ↔ ∀ r, WP.wp x.run (fun a m => r ≤ m ∧ Q a (m - r)) E (n + r) := by
  simp only [TickM.wp, PreservesSup.frameClosure, iInf_apply, iInf_prop_eq_forall, costConj_imp]
  rfl

/-- Point evaluation of the base wp on `tick`: `tick` scores the post on the incremented counter. -/
theorem wp_tick_apply_eq (Q : Unit → Nat → Prop) (E : EPost.Nil) (n : Nat) :
    WP.wp tick.run Q E n = Q () (n + 1) := by
  simp only [TickM.run, tick, StateT.wp_apply_eq, StateT.run_modify]; rfl

/-- `TickM.wp tick` scores the post on the incremented counter, independent of the held budget. -/
theorem TickM.wp_tick_apply_eq (Q : Unit → Nat → Prop) (E : EPost.Nil) (n : Nat) :
    TickM.wp tick Q E n = Q () (n + 1) := by
  apply propext
  rw [TickM.wp_eq_forall]
  constructor
  · intro h
    have h0 := h 0
    rw [_root_.wp_tick_apply_eq] at h0
    simpa using h0.2
  · intro hQ r
    rw [_root_.wp_tick_apply_eq]
    exact ⟨by omega, by simpa [show n + r + 1 - r = n + 1 by omega] using hQ⟩

/-! ### A cost-discarding program has an unsatisfiable `TickM.wp` -/

/-- A cost-*discarding* program: it throws away the accumulated cost, resetting the counter to `0`. -/
def dropCost : TickM Unit := show StateM Nat Unit from set 0

theorem wp_dropCost_apply_eq (Q : Unit → Nat → Prop) (E : EPost.Nil) (n : Nat) :
    WP.wp dropCost.run Q E n = Q () 0 := by
  simp only [TickM.run, dropCost, StateT.wp_apply_eq, StateT.run_set]; rfl

/-- The cost-discarding program `dropCost` has `TickM.wp _ Q n = False` for **every** postcondition
`Q`: holding a budget of `1` leaves `1 ≤ 0`, unsatisfiable. `TickM.wp` rejects programs that lose
held cost. -/
example (Q : Unit → Nat → Prop) (E : EPost.Nil) (n : Nat) : TickM.wp dropCost Q E n = False := by
  apply propext
  rw [TickM.wp_eq_forall]
  constructor
  · intro h
    have := h 1
    rw [wp_dropCost_apply_eq] at this
    exact absurd this.1 (by omega)
  · exact False.elim

/-! ## Part 3: the internalized frame rule for `TickM.wp` -/

/-- Consequence rule for `TickM.wp`: weakening the postcondition weakens the precondition. -/
theorem TickM.wp_consequence {α : Type} (x : TickM α) {Q Q' : α → Nat → Prop} (E : EPost.Nil) (n : Nat)
    (h : ∀ a n', Q a n' → Q' a n') (hx : TickM.wp x Q E n) : TickM.wp x Q' E n := by
  rw [TickM.wp_eq_forall] at hx ⊢
  intro r
  refine WP.wp_consequence x.run _ _ E (fun a m => ?_) (n + r) (hx r)
  rintro ⟨hle, hQ⟩
  exact ⟨hle, h a (m - r) hQ⟩

/-- The `WP` interpretation of `TickM` is the frame-internalizing `TickM.wp`. Kept a `def` (the `WP`
instance is derived from the `WPMonad` instance below) so there is a single `WP (TickM α)`, letting
the generic `bind`/`pure` specs unify against `TickM` goals. -/
@[reducible] def TickM.instWP {α : Type} : WP (TickM α) α (Nat → Prop) EPost.Nil where
  wpTrans x := ⟨fun Q E => TickM.wp x Q E⟩
  wp_trans_monotone x post post' epost epost' _ hpost := by
    intro n hn
    exact TickM.wp_consequence x epost n (fun a n' => hpost a n') hn

instance : LawfulMonad TickM := inferInstanceAs (LawfulMonad (StateM Nat))

/-- `TickM` is a `WPMonad`: `pure`/`bind` are sound for `TickM.wp`. The held budget `r` threads
through both: `pure` keeps it, and `bind` passes the same `r` to the continuation. -/
instance TickM.instWPMonad : WPMonad TickM (Nat → Prop) EPost.Nil where
  toWP _ := TickM.instWP
  pure_le_wp_pure x post E := by
    intro n h
    show TickM.wp (pure x) post E n
    rw [TickM.wp_eq_forall]
    intro r
    refine WPMonad.pure_le_wp_pure (m := StateM Nat) x _ E (n + r) ?_
    exact ⟨by omega, by simpa [show n + r - r = n by omega] using h⟩
  bind_le_wp_bind x f post E := by
    intro n hn
    have hn' := (TickM.wp_eq_forall x (fun a => TickM.wp (f a) post E) E n).mp hn
    show TickM.wp (x >>= f) post E n
    rw [TickM.wp_eq_forall]
    intro r
    refine WPMonad.bind_le_wp_bind (m := StateM Nat) x.run (fun a => (f a).run)
      (fun b m => r ≤ m ∧ post b (m - r)) E (n + r) ?_
    refine WP.wp_consequence x.run _ _ E (fun a m => ?_) (n + r) (hn' r)
    rintro ⟨hle, hk⟩
    rw [TickM.wp_eq_forall] at hk
    have := hk r
    rwa [show m - r + r = m by omega] at this

/-- **The frame rule, internalized**, as a corollary of `WP.Frames.of_frameClosure`: since `TickM.wp`
is a `PreservesSup.frameClosure`, *every* program `x` frames *every* budget `F` with respect to
`costConj`. No cost-additivity hypothesis is required. -/
@[grind .]
theorem frames_costConj {α : Type} (x : TickM α) (F : Nat) : WP.Frames costConj x F :=
  WP.Frames.of_frameClosure costConj (· + ·) costConj_add
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

theorem tickFrames {α : Type} (x : TickM α) (F : Nat) (Q : α → Nat → Prop) :
    F ⋆ TickM.wp x Q EPost.Nil.mk ⊑ TickM.wp x (fun a => F ⋆ Q a) EPost.Nil.mk :=
  (frames_costConj x F).conj_wp_le_wp_conj Q EPost.Nil.mk

/-- The framed-spec corollary, mirroring `WP.Frames.op_wp_upperAdjoint_le_wp`: running `x` under the magic
wand `F -⋆ Q` and re-conjoining the budget `F` is a precondition for running `x` under `Q`. -/
theorem tickFrames_imp {α : Type} (x : TickM α) (F : Nat) (Q : α → Nat → Prop) :
    F ⋆ TickM.wp x (fun a => F -⋆ Q a) EPost.Nil.mk ⊑ TickM.wp x Q EPost.Nil.mk := by
  refine PartialOrder.rel_trans (tickFrames x F _) ?_
  intro n hn
  refine TickM.wp_consequence x EPost.Nil.mk n (fun a n' => ?_) hn
  exact PreservesSup.upperAdjoint_le (costConj F) (Q a) n'

/-- A *lossy* cost spec for `tick`: from any input it only asserts the post at the incremented
counter, dropping the bound relating the output cost to the input. -/
theorem tick_spec_lossy (Q : Unit → Nat → Prop) (n : Nat)
    (h : ∀ m, Q () (m + 1)) : TickM.wp tick Q EPost.Nil.mk n := by
  rw [TickM.wp_tick_apply_eq]
  exact h n

/-- The budget `F = n` ("hold the whole input cost") recovers the sharp output cost `m = n + 1` that
the lossy spec drops. `tickFrames_imp` reduces it to running `tick` under the wand `n -⋆ Q`: the
budget holds the input cost, the wand discharges the residual. -/
theorem recovers_cost (n : Nat) :
    (fun m => m = n) ⊑ TickM.wp tick (fun _ m => m = n + 1) EPost.Nil.mk := by
  refine PartialOrder.rel_trans ?_ (tickFrames_imp tick n (fun _ m => m = n + 1))
  intro m hm
  refine ⟨by omega, ?_⟩
  rw [show m - n = 0 by omega, TickM.wp_tick_apply_eq, costConj_imp]
  omega

-- The lossy spec is genuinely lossy: dropping the budget and applying `tick_spec_lossy` directly
-- leaves the false obligation `∀ m, m + 1 = n + 1`. The budget `tickFrames_imp` carries the input
-- cost into the post.
example (n : Nat) : (fun m => m = n) ⊑ TickM.wp tick (fun _ m => m = n + 1) EPost.Nil.mk := by
  fail_if_success
    (refine PartialOrder.rel_trans (le_top _) ?_
     intro m _
     exact tick_spec_lossy _ _ (by intro k; omega))
  exact recovers_cost n

/-! ## Part 5: end-to-end `vcgen` via a registered `@[frameproc]`

`tickFrameProc` infers the budget from the current cost (the first excess state argument). Registered
with `@[frameproc]`, it drives `vcgen` framing on `TickM` programs with no `frames` clause: `vcgen`
applies the `costConj` gadget, the registered `costSplit` decomposes `pre ⊑ costConj c R n` into a
budget side goal and a cost-shifted residual, and the meet machinery finishes. -/

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- The applied (`Prop`-level) budget split, used as a direct (`applyLemma := none`) lattice split: to
prove `pre ⊑ costConj c R n`, prove `pre ⊑ (c ≤ n) ⊓ R (n - c)`. The residual `R` runs with the
budget `c` removed; the leftover meet is decomposed by the meet machinery. -/
theorem le_costConj_point_apply {pre : Prop} (c n : Nat) (R : Nat → Prop)
    (h : pre ⊑ ((c ≤ n) ⊓ R (n - c))) :
    pre ⊑ costConj c R n := by
  intro hpre
  have hm := h hpre
  rw [meet_prop_eq_and] at hm
  exact hm

/-- The applied budget split for the cost magic wand, the `costConj` *residual* backward rule: to
prove `pre ⊑ (c -⋆ R) n`, prove `pre ⊑ R (n + c)`. The framed continuation runs with the budget `c`
added back. -/
theorem le_imp_costConj_point_apply {pre : Prop} (c n : Nat) (R : Nat → Prop)
    (h : pre ⊑ R (n + c)) :
    pre ⊑ PreservesSup.upperAdjoint (costConj c) R n := by
  intro hpre
  rw [costConj_imp]
  exact h hpre

/-- Exact spec for `tick`, registered so `vcgen` can decompose `tick` calls. -/
@[spec] theorem tick_spec (post : Unit → Nat → Prop) :
    ⦃ fun n => post () (n + 1) ⦄ tick ⦃ post ⦄ := by
  constructor
  intro n h
  show TickM.wp tick post _ n
  rw [TickM.wp_tick_apply_eq]
  exact h

/-- The frame inference procedure for `TickM`: hold the budget given by the current cost (the first
excess state argument). -/
def tickFrameProc : FrameInferenceProc := fun _R _pre info => do
  let some cost := info.excessArgs[0]? | return none
  return some cost

/-- The direct lattice split for `costConj`, decomposing `pre ⊑ costConj c R n` via
`le_costConj_point_apply` (no pointwise distribution). -/
def costSplit : LatticeSplit := { relLemma := ``le_costConj_point_apply }

/-- The direct lattice split for the `costConj` residual wand, decomposing
`pre ⊑ PreservesSup.upperAdjoint (costConj c) R n` via `le_imp_costConj_point_apply`. -/
def costImpSplit : LatticeSplit := { relLemma := ``le_imp_costConj_point_apply }

/-- Register the cost frame inference procedure for `vcgen`, indexed by the `TickM` program type. -/
@[frameproc] def tickFP : FrameProc where
  prog := ``TickM
  proc := tickFrameProc
  conj := ``costConj
  op := fun _ => pure (mkConst ``costConj)
  split := costSplit
  impSplit := costImpSplit

/-- End-to-end: plain `vcgen` infers the budget, applies the `costConj` gadget, fires the registered
`costSplit`, and the meet machinery closes the residual. -/
example : ⦃ (⊤ : Nat → Prop) ⦄ tick ⦃ fun _ => (⊤ : Nat → Prop) ⦄ := by
  vcgen with finish [top_apply]

/-! ## Part 6: a loop over a list, framed automatically across calls -/

/-- Tick once per list element. -/
def tickList {α : Type} (xs : List α) : TickM Unit := do
  for _ in xs do
    tick

/-- A *stopwatch* spec: from zero accumulated cost, `prog` ends at cost `n`. -/
local syntax:60 term:61 " ⏱ " term:61 : term
local macro_rules
  | `($prog:term ⏱ $n:term) => `(⦃ (· = 0) ⦄ $prog ⦃ fun _ m => m = $n ⦄)

/-- The stopwatch spec for `tickList`: timed from zero, it costs exactly `xs.length`. Concrete (not
schematic in the post), so `vcgen` only frames it where the start cost is not zero. -/
@[spec] theorem tickList_spec {α : Type} (xs : List α) : tickList xs ⏱ xs.length := by
  unfold tickList
  vcgen invariants
  | inv1 => fun cursor _ n => n = cursor.pos
  with finish

/-- Two loops in sequence, timed from zero: plain `vcgen` frames the second call by the cost the first
accrued (the first starts at zero, so it is not framed), with no `frames` annotation. -/
example {α : Type} (xs ys : List α) :
    (do tickList xs; tickList ys : TickM Unit) ⏱ (xs.length + ys.length) := by
  vcgen with finish

/-- The same goal, framed **explicitly**: the `frames` clause names the budget for each call. The
registered `@[frameproc]` supplies the `costConj` operator, so these are `costConj` frames, not meet. -/
example {α : Type} (xs ys : List α) :
    (do tickList xs; tickList ys : TickM Unit) ⏱ (xs.length + ys.length) := by
  vcgen frames
  | tickList xs => 0
  | tickList ys => xs.length
  with finish
