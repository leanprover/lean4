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

A cost transformer `TickT m := StateT Nat m` whose weakest precondition bakes in a *residuated* frame
rule for a resource that is **not** the lattice meet. The resource is a `Nat` cost budget with
separating conjunction `costConj r b = fun n => ⌜r ≤ n⌝ ⊓ b (n - r)` (hold `r` aside, run `b` on the
rest) and magic wand `r -⋆ b = fun m => b (m + r)`. `TickT.wp` is the `PreservesSup.frameClosure` of
the base wp over `costConj`, so every program frames every budget by construction, and a registered
`@[frameproc]` lets plain `vcgen` infer and frame the budget across calls.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do Std.Internal.Do.CompleteLattice

/-! ## The cost separating conjunction -/

variable {L : Type u} [CompleteLattice L]

/-- The cost frame operator: hold the budget `r` aside and run `b` on the remaining cost.
`costConj r b n` is `⌜r ≤ n⌝ ⊓ b (n - r)`: at least `r` cost available and `b` holds of the rest.
This is separating conjunction for the `Nat` resource, over any assertion lattice. -/
noncomputable def costConj (r : Nat) (b : Nat → L) : Nat → L := fun n => ⌜r ≤ n⌝ ⊓ b (n - r)

@[inherit_doc costConj] local infixr:67 " ⋆ " => costConj

/-- Pointwise unfolding of `costConj`. As a `grind` normalization rule it eliminates `costConj`
during preprocessing, so the applied form `costConj r b n s` reduces under any base state argument.
Also builds the frame split rule. -/
@[grind norm] theorem costConj_apply (r : Nat) (b : Nat → L) (n : Nat) :
    costConj r b n = ⌜r ≤ n⌝ ⊓ b (n - r) := rfl

/-- The guard `⌜p⌝ ⊓ ·` preserves arbitrary sups, for any complete lattice, because `⌜p⌝` is `⊤`/`⊥`. -/
theorem ofProp_meet_sup (p : Prop) (X : L → Prop) :
    ⌜p⌝ ⊓ CompleteLattice.sup X
      = CompleteLattice.sup (fun y => ∃ x, X x ∧ y = ⌜p⌝ ⊓ x) := by
  apply PartialOrder.rel_antisymm
  · by_cases hp : p
    · apply PartialOrder.rel_trans (meet_le_right _ _)
      apply sup_le
      intro x hx
      refine PartialOrder.rel_trans ?_ (le_sup _ (y := ⌜p⌝ ⊓ x) ⟨x, hx, rfl⟩)
      exact le_meet _ _ _ (le_ofProp x p hp) PartialOrder.rel_refl
    · refine PartialOrder.rel_trans (meet_le_left _ _) ?_
      simp only [CompleteLattice.ofProp, hp, ↓reduceIte]
      exact bot_le _
  · apply sup_le
    rintro y ⟨x, hx, rfl⟩
    exact le_meet _ _ _ (meet_le_left _ _) (PartialOrder.rel_trans (meet_le_right _ _) (le_sup _ hx))

instance (r : Nat) : PreservesSup (costConj (L := L) r) where
  map_sup s := by
    funext n
    show ⌜r ≤ n⌝ ⊓ (CompleteLattice.sup s) (n - r)
      = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = costConj r x) n
    simp only [sup_apply]
    rw [ofProp_meet_sup]
    congr 1
    funext z
    apply propext
    constructor
    · rintro ⟨w, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨costConj r f, ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f (n - r), ⟨f, hf, rfl⟩, rfl⟩

/-- The cost magic wand: the upper adjoint of the slice `costConj r`, a plain shift
`r -⋆ b = fun m => b (m + r)`. -/
local notation:60 lhs:61 " -⋆ " rhs:61 => Lean.Order.PreservesSup.upperAdjoint (costConj lhs) rhs

/-- The upper adjoint of `costConj r` is the cost magic wand `fun m => b (m + r)`, a shift of the
budget back onto the counter. -/
@[grind =]
theorem costConj_imp (r : Nat) (b : Nat → L) :
    r -⋆ b = (fun m => b (m + r)) := by
  apply PartialOrder.rel_antisymm
  · unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx m
    have := hx (m + r)
    simp only [costConj, show m + r - r = m by omega] at this
    exact PartialOrder.rel_trans (le_meet _ _ _ (le_ofProp _ _ (by omega)) PartialOrder.rel_refl) this
  · refine PreservesSup.le_upperAdjoint (costConj r) (b := b) (x := fun m => b (m + r)) ?_
    intro n
    show (⌜r ≤ n⌝ ⊓ b (n - r + r)) ⊑ b n
    rw [CompleteLattice.ofProp_intro_r]
    intro hle
    rw [show n - r + r = n by omega]

/-- The additive action law of `costConj`: composing two budgets `r` and `r'` is the same as holding
them one after the other. -/
theorem costConj_add (r r' : Nat) (a : Nat → L) :
    costConj (r + r') a = costConj r (costConj r' a) := by
  funext n
  show ⌜r + r' ≤ n⌝ ⊓ a (n - (r + r')) = ⌜r ≤ n⌝ ⊓ (⌜r' ≤ n - r⌝ ⊓ a (n - r - r'))
  rw [Nat.sub_sub, ← meet_assoc, ofProp_and,
    show (r ≤ n ∧ r' ≤ n - r) = (r + r' ≤ n) from
      propext ⟨fun ⟨_, _⟩ => by omega, fun h => ⟨by omega, by omega⟩⟩]

/-- The unit of the `costConj` action: holding a zero budget is the identity. -/
theorem costConj_zero (a : Nat → L) : costConj 0 a = a := by
  funext n
  rw [costConj_apply, Nat.sub_zero,
    show (⌜0 ≤ n⌝ : L) = ⊤ from PartialOrder.rel_antisymm (le_top _) (top_le_ofProp _ (Nat.zero_le n)),
    top_meet]

/-! ## The cost transformer `TickT` and its weakest precondition -/

/-- A cost-tracking monad transformer over a base monad. A `def` so `TickT` carries its own
frame-internalizing `WP` interpretation and `@[frameproc]` keys on its head. -/
def TickT (m : Type → Type) (α : Type) : Type := StateT Nat m α

abbrev TickM := TickT Id

instance [Monad m] : Monad (TickT m) := inferInstanceAs (Monad (StateT Nat m))
instance [Monad m] [LawfulMonad m] : LawfulMonad (TickT m) :=
  inferInstanceAs (LawfulMonad (StateT Nat m))
/-- State effects reach the base monad through this lift; the cost counter is threaded only by `tick`
and the frame machinery. -/
instance [Monad m] : MonadLift m (TickT m) := inferInstanceAs (MonadLift m (StateT Nat m))

/-- A `TickT` program as the underlying `StateT` program, carrying the base (non-framed) wp. -/
def TickT.run [Monad m] {α : Type} (x : TickT m α) : StateT Nat m α := x

/-- The cost primitive: incur one unit of cost by incrementing the counter. -/
def tick [Monad m] : TickT m Unit := show StateT Nat m Unit from modify (· + 1)

/-- The frame-internalizing cost weakest precondition: the `PreservesSup.frameClosure` of the base
`StateT` wp over `costConj`. -/
noncomputable def TickT.wp [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (Q : α → Nat → Pred) (E : EPred) : Nat → Pred :=
  PreservesSup.frameClosure costConj (WP.wp x.run · E) Q

/-- The simp normal form for `TickT.wp`: the meet over all held budgets `r` of the base wp under the
held-budget postcondition `⌜r ≤ m⌝ ⊓ Q a (m - r)`, offset by `r`. -/
@[simp, grind =]
theorem TickT.wp_apply_eq [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (Q : α → Nat → Pred) (E : EPred) (n : Nat) :
    TickT.wp x Q E n = ⨅ r, WP.wp x.run (fun a m => ⌜r ≤ m⌝ ⊓ Q a (m - r)) E (n + r) := by
  simp only [TickT.wp, PreservesSup.frameClosure, iInf_apply, costConj_imp]
  rfl

theorem TickT.le_wp_tick [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (Q : Unit → Nat → Pred) (E : EPred) (n : Nat) :
    Q () (n + 1) ⊑ WP.wp (tick (m := m)).run Q E n := by
  apply WPMonad.pure_le_wp_pure (post := Function.uncurry Q) (x := (PUnit.unit, n + 1))

/-! ### A cost-discarding program has an unsatisfiable `wp` -/

/-- A cost-*discarding* program: it throws away the accumulated cost, resetting the counter to `0`. -/
def dropCost : TickM Unit := show StateM Nat Unit from set 0

/-- `dropCost` resets the counter, so `TickT.wp dropCost Q n = False` for every `Q`: holding a budget
of `1` leaves the unsatisfiable `1 ≤ 0`. The frame closure rejects programs that lose held cost. -/
example (Q : Unit → Nat → Prop) (E : EPost.Nil) (n : Nat) : TickT.wp dropCost Q E n = False := by
  rw [TickT.wp_apply_eq, iInf_prop_eq_forall]
  refine propext ⟨fun h => ?_, False.elim⟩
  -- `h 1` is the `r = 1` conjunct, which reduces to `⌜1 ≤ 0⌝ ⊓ Q () 0`.
  have h1 : (⌜(1 : Nat) ≤ 0⌝ ⊓ Q () 0 : Prop) := h 1
  rw [meet_prop_eq_and, ofProp_prop_eq] at h1
  exact absurd h1.1 (by omega)

/-! ## The internalized frame rule -/

variable {m : Type → Type} [Monad m]

/-- The `WPMonad` of `TickT m` is the `costConj`-frame closure of the base `StateT` wp, so the
`costConj`-frame rule holds by construction. -/
noncomputable instance TickT.instWPMonad [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (TickT m) (Nat → Pred) EPred :=
  WPMonad.of_frameClosure (m := StateT Nat m) costConj costConj_add costConj_zero StateT.instWPMonad

/-- The internalized frame rule: every program frames every budget `F` with respect to `costConj`. -/
@[grind .]
theorem frames_costConj [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (F : Nat) : WP.Frames costConj x F :=
  WP.Frames.of_frameClosure costConj (· + ·) costConj_add
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

/-- The frame rule, pointwise: holding `F` commutes into the postcondition of any `TickT` program. -/
theorem tickFrames [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (F : Nat) (Q : α → Nat → Pred) (E : EPred) :
    F ⋆ TickT.wp x Q E ⊑ TickT.wp x (fun a => F ⋆ Q a) E :=
  (frames_costConj (Pred := Pred) (EPred := EPred) x F).conj_wp_le_wp_conj Q E

/-- The sharp cost spec for `tick`: it costs exactly one unit. Threads the held budget `r` through the
base `tick` spec. -/
theorem TickT.le_wp_tick' [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (Q : Unit → Nat → Pred) (E : EPred) (n : Nat) :
    Q () (n + 1) ⊑ TickT.wp (tick (m := m)) Q E n := by
  rw [TickT.wp_apply_eq]
  apply le_iInf
  intro r
  refine PartialOrder.rel_trans ?_ (TickT.le_wp_tick (fun a k => ⌜r ≤ k⌝ ⊓ Q a (k - r)) E (n + r))
  show Q () (n + 1) ⊑ ⌜r ≤ n + r + 1⌝ ⊓ Q () (n + r + 1 - r)
  exact le_meet _ _ _ (le_ofProp _ _ (by omega))
    (PartialOrder.rel_of_eq (by rw [show n + r + 1 - r = n + 1 by omega]))

/-! ## End-to-end `vcgen` via a registered `@[frameproc]`

`tickFrameProc` holds the current cost as the budget; the registered `costSplit` decomposes a
`costConj` goal into a budget side goal and a cost-shifted residual. -/

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Exact spec for `tick`, registered so `vcgen` can decompose `tick` calls. -/
@[spec] theorem tick_spec [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun n => Q () (n + 1) ⦄ (tick : TickT m Unit) ⦃ Q; E ⦄ := by
  constructor
  intro n
  exact TickT.le_wp_tick' Q E n

/-- The frame inference procedure: hold the budget given by the current cost, the first excess state
argument of the `Nat → L` cost assertion. -/
def tickFrameProc : FrameInferenceProc := fun _R _pre info _specPre => do
  unless info.Pred.isArrow && info.Pred.bindingDomain!.isConstOf ``Nat do return none
  let some cost := info.excessArgs[0]? | return none
  -- Framing the whole cost leaves the residual budget `cost - cost`; skip when that normalizes to
  -- `0` so the proc does not re-fire on its own residual.
  let cost ← instantiateMVars cost
  let thms := ({} : Lean.Meta.Sym.Simp.Theorems).insert
    (← Lean.Meta.Sym.Simp.mkTheoremFromDecl ``Nat.sub_self)
  let post := Lean.Meta.Sym.Simp.evalGround >> thms.rewrite
  let cost := (← Lean.Meta.Sym.simp cost { post }).getResultExpr cost
  if cost.nat? == some 0 then return none
  return some cost

/-- Register the cost frame inference procedure for `vcgen`, indexed by the `TickT` program type. The
frame operator `costConj` is built at the base lattice `L` read off the assertion type `Nat → L`, so it
frames the cost over any base monad. Its `costConj_apply` rewrite unfolds `costConj r b n` to
`⌜r ≤ n⌝ ⊓ b (n - r)`, inheriting the built-in meet terminal. -/
@[frameproc] def tickFP : FrameProc where
  prog := ``TickT
  mkOpAppM := fun info => Meta.mkAppOptM ``costConj #[some info.Pred.bindingBody!, none]
  resourceTy := fun _ => pure (mkConst ``Nat)
  op := { head := ``costConj, rewrites := #[``costConj_apply] }
  proc := some tickFrameProc

/-- End-to-end: plain `vcgen` infers the budget, applies the `costConj` gadget, fires the registered
`costSplit`, and the meet machinery closes the residual. -/
example : ⦃ (⊤ : Nat → Prop) ⦄ (tick : TickM Unit) ⦃ fun _ => (⊤ : Nat → Prop) ⦄ := by
  vcgen with finish [top_apply]

/-! ## The default terminal

An operator whose rewrites reduce it to a head with no registered `⊑`-introduction lemma still yields
a rule: the saturated residual entailment is handed back as the sole subgoal. `keepFrame r b = b`
frames nothing, reducing to the bare `b`. -/

/-- A frame operator that holds nothing: it reduces to its second argument. -/
def keepFrame (r : Nat) (b : Nat → Prop) : Nat → Prop := b
@[simp] theorem keepFrame_apply (r : Nat) (b : Nat → Prop) : keepFrame r b = b := rfl
private def keepPred : Nat → Prop := fun n => n = 0

-- `keepFrame` saturates to a non-connective head, so the default terminal produces a rule.
run_meta do
  let rhs ← Meta.mkAppM ``keepFrame #[mkNatLit 3, mkConst ``keepPred]
  let _ ← SymM.run <| mkLatticeOpRule rhs { head := ``keepFrame, rewrites := #[``keepFrame_apply] }

-- Stripped of its rewrite the operator neither reduces nor closes, so its split would be the identity.
/-- error: frame operator `keepFrame` neither reduces nor has a registered terminal; its lattice split rule would be the identity -/
#guard_msgs in
run_meta do
  let rhs ← Meta.mkAppM ``keepFrame #[mkNatLit 3, mkConst ``keepPred]
  let _ ← SymM.run <| mkLatticeOpRule rhs { head := ``keepFrame }

/-! ## Looping and automatic framing across calls -/

/-- Tick once per list element. -/
def tickList {α : Type} (xs : List α) : TickT (StateM Nat) Unit := do
  for _ in xs do
    tick

/-- A *stopwatch* spec: from zero accumulated cost, `prog` ends at cost `n`. -/
local syntax:60 term:61 " ⏱ " term:61 : term
local macro_rules
  | `($prog:term ⏱ $n:term) => `(⦃ (⌜· = 0⌝) ⦄ $prog ⦃ fun _ m => ⌜m = $n⌝ ⦄)

/-- The stopwatch spec for `tickList`: timed from zero, it costs exactly `xs.length`. -/
@[spec] theorem tickList_spec {α : Type} (xs : List α) : tickList xs ⏱ xs.length := by
  unfold tickList
  vcgen invariants
  | inv1 => fun cursor _ n _ => n = cursor.pos
  with finish

/-- Two loops in sequence: `vcgen` infers and frames the second call by the cost the first accrued,
with no `frames` clause. -/
example {α : Type} (xs ys : List α) :
    (do tickList xs; tickList ys : TickT (StateM Nat) Unit) ⏱ (xs.length + ys.length) := by
  vcgen with finish

/-- The same goal with an explicit `frames` clause naming each call's budget. -/
example {α : Type} (xs ys : List α) :
    (do tickList xs; tickList ys : TickT (StateM Nat) Unit) ⏱ (xs.length + ys.length) := by
  vcgen frames
  | tickList xs => 0
  | tickList ys => xs.length
  with finish

/-! ## Over a non-`Id` base

`TickT` forwards state effects to its base monad, threading the cost counter only through `tick` and
the frame machinery, so `vcgen` handles base effects through the base spec while the cost is left
untouched. -/

/-- Lifting a base-monad program into `TickT` leaves the cost untouched: its wp is the base wp with the
cost `n` held fixed. -/
@[spec] theorem Spec.monadLift_TickT [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] {α : Type} (x : m α) (Q : α → Nat → Pred) (E : EPred) :
    ⦃fun n => WP.wp x (fun a => Q a n) E⦄ (MonadLift.monadLift x : TickT m α) ⦃Q; E⦄ := by
  constructor
  intro n
  show WP.wp x (fun a => Q a n) E ⊑ TickT.wp (MonadLift.monadLift x) Q E n
  rw [TickT.wp_apply_eq]
  apply le_iInf
  intro r
  refine PartialOrder.rel_trans ?_
    ((WPMonad.le_wp_monadLift_StateT_apply x (fun a m => ⌜r ≤ m⌝ ⊓ Q a (m - r))) (n + r))
  refine WP.wp_consequence x (fun a => Q a n) _ E (fun a => ?_)
  rw [show n + r - r = n by omega]
  exact le_meet _ _ _ (le_ofProp _ _ (by omega)) PartialOrder.rel_refl

/-- A base-state effect lifted into `TickT`: it bumps the `StateM Nat` state and never ticks. -/
def bumpBase : TickT (StateM Nat) Unit := modify (fun x => x + 1)

/-- The base-state postcondition threads through the lift. -/
example : ⦃ fun _ base => base = 0 ⦄ bumpBase ⦃ fun _ _ base => base = 1 ⦄ := by
  vcgen [bumpBase] with finish

/-- The cost is untouched by a pure base-state effect. -/
example : bumpBase ⏱ 0 := by vcgen [bumpBase] with finish

/-- A program that both ticks and mutates the base state: the cost frame and the base-state spec
compose, one over the cost counter and one over the base `StateM Nat`. -/
def tickAndBump : TickT (StateM Nat) Unit := do tick; modify (fun x => x + 1)

example : ⦃ fun cost base => cost = 0 ∧ base = 0 ⦄ (tickAndBump)
    ⦃ fun _ cost base => cost = 1 ∧ base = 1 ⦄ := by
  vcgen [tickAndBump] with finish

/-! ## Over a base with exceptions -/

/-- The specs thread the exception postcondition `E` unchanged: over a base with exceptions
(`ExceptT String Id`), `tick` still costs one and leaves the exception branch untouched. -/
example : ⦃ fun cost => ⌜cost = 0⌝ ⦄ (tick : TickT (ExceptT String Id) Unit)
    ⦃ fun _ cost => ⌜cost = 1⌝; epost⟨fun _ => (⊤ : Prop)⟩ ⦄ := by
  vcgen with finish
