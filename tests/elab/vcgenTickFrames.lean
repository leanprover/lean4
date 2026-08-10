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
rule for a resource that is **not** the lattice meet. The resource is a `Nat` tick counter with
separating conjunction `costConj shift b = fun ticks => ⌜shift ≤ ticks⌝ ⊓ b (ticks - shift)`
(Day convolution with a point mass: translate `b` by `shift`) and magic wand
`shift -⋆ b = fun ticks => b (ticks + shift)`. `TickT.wp` is the `PreservesSup.frameClosure` of the
base wp over `costConj`, so every program frames every shift by construction, and a registered
`@[frameproc]` lets plain `vcgen` infer and frame the shift across calls.
-/

open Lean Order Meta Elab Tactic Sym Sym.Internal Std Internal.Do Std.Internal.Do.CompleteLattice

/-! ## The cost separating conjunction -/

variable {L : Type u} [CompleteLattice L]

/-- The cost separating conjunction: convolve `b` with a point mass at `shift`, translating `b` by
`shift` ticks. `costConj shift b ticks` is `⌜shift ≤ ticks⌝ ⊓ b (ticks - shift)`: at least `shift`
ticks available, and `b` holds of the rest. This is `∗` for the `Nat` resource. -/
noncomputable def costConj (shift : Nat) (b : Nat → L) : Nat → L :=
  fun ticks => ⌜shift ≤ ticks⌝ ⊓ b (ticks - shift)

@[inherit_doc costConj] local infixr:67 " ⋆ " => costConj

/-- Pointwise unfolding of `costConj`. As a `grind` normalization rule it eliminates `costConj`
during preprocessing, so the applied form `costConj shift b ticks s` reduces under any base state
argument. Also builds the frame split rule. -/
@[grind norm] theorem costConj_apply (shift : Nat) (b : Nat → L) (ticks : Nat) :
    costConj shift b ticks = ⌜shift ≤ ticks⌝ ⊓ b (ticks - shift) := rfl

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

instance (shift : Nat) : PreservesSup (costConj (L := L) shift) where
  map_sup s := by
    funext ticks
    show ⌜shift ≤ ticks⌝ ⊓ (CompleteLattice.sup s) (ticks - shift)
      = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = costConj shift x) ticks
    simp only [sup_apply]
    rw [ofProp_meet_sup]
    congr 1
    funext z
    apply propext
    constructor
    · rintro ⟨w, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨costConj shift f, ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f (ticks - shift), ⟨f, hf, rfl⟩, rfl⟩

/-- The cost magic wand: the upper adjoint of `costConj shift`, the correlation
`shift -⋆ b = fun ticks => b (ticks + shift)` translating `b` back up the counter. -/
local notation:60 lhs:61 " -⋆ " rhs:61 => Lean.Order.PreservesSup.upperAdjoint (costConj lhs) rhs

/-- The upper adjoint of `costConj shift` is the cost magic wand `fun ticks => b (ticks + shift)`,
translating `b` back up the counter. -/
@[grind =]
theorem costConj_imp (shift : Nat) (b : Nat → L) :
    shift -⋆ b = (fun ticks => b (ticks + shift)) := by
  apply PartialOrder.rel_antisymm
  · unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx ticks
    have := hx (ticks + shift)
    simp only [costConj, show ticks + shift - shift = ticks by omega] at this
    exact PartialOrder.rel_trans (le_meet _ _ _ (le_ofProp _ _ (by omega)) PartialOrder.rel_refl) this
  · refine PreservesSup.le_upperAdjoint (costConj shift) (b := b)
      (x := fun ticks => b (ticks + shift)) ?_
    intro ticks
    show (⌜shift ≤ ticks⌝ ⊓ b (ticks - shift + shift)) ⊑ b ticks
    rw [CompleteLattice.ofProp_intro_r]
    intro hle
    rw [show ticks - shift + shift = ticks by omega]

/-- The additive action law of `costConj`: composing two shifts `shift` and `shift'` is the same as
translating one after the other. -/
theorem costConj_add (shift shift' : Nat) (a : Nat → L) :
    costConj (shift + shift') a = costConj shift (costConj shift' a) := by
  funext ticks
  show ⌜shift + shift' ≤ ticks⌝ ⊓ a (ticks - (shift + shift'))
    = ⌜shift ≤ ticks⌝ ⊓ (⌜shift' ≤ ticks - shift⌝ ⊓ a (ticks - shift - shift'))
  rw [Nat.sub_sub, ← meet_assoc, ofProp_and,
    show (shift ≤ ticks ∧ shift' ≤ ticks - shift) = (shift + shift' ≤ ticks) from
      propext ⟨fun ⟨_, _⟩ => by omega, fun h => ⟨by omega, by omega⟩⟩]

/-- The unit of the `costConj` action: a zero shift is the identity. -/
theorem costConj_zero (a : Nat → L) : costConj 0 a = a := by
  funext ticks
  rw [costConj_apply, Nat.sub_zero,
    show (⌜0 ≤ ticks⌝ : L) = ⊤ from
      PartialOrder.rel_antisymm (le_top _) (top_le_ofProp _ (Nat.zero_le ticks)),
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

/-- The simp normal form for `TickT.wp`: the meet over all shifts `r` of the base wp under the
shifted postcondition `⌜r ≤ m⌝ ⊓ Q a (m - r)`, offset by `r`. -/
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

/-- `dropCost` resets the counter, so `TickT.wp dropCost Q n = False` for every `Q`: a shift
of `1` leaves the unsatisfiable `1 ≤ 0`. The frame closure rejects programs that lose held ticks. -/
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

/-- The internalized frame rule: every program frames every shift `F` with respect to `costConj`. -/
@[grind .]
theorem frames_costConj [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (F : Nat) : WP.Frames costConj x F :=
  WP.Frames.of_frameClosure costConj (· + ·) costConj_add
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

/-- The frame rule, pointwise: holding `F` commutes into the postcondition of any `TickT` program. -/
theorem tickFrames [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {α : Type} (x : TickT m α) (F : Nat) (Q : α → Nat → Pred) (E : EPred) :
    F ⋆ TickT.wp x Q E ⊑ TickT.wp x (fun a => F ⋆ Q a) E :=
  (frames_costConj (Pred := Pred) (EPred := EPred) x F).op_wp_le_wp_op Q E

/-- The sharp cost spec for `tick`: it costs exactly one unit. Threads the shift `r` through the
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

`tickFrameProc` shifts by the current tick count and emits the split VC in its `costConj_apply`
meet form, so the built-in meet split yields the tick guard and the shifted residual. -/

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Exact spec for `tick`, registered so `vcgen` can decompose `tick` calls. -/
@[spec] theorem tick_spec [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun n => Q () (n + 1) ⦄ (tick : TickT m Unit) ⦃ Q; E ⦄ := by
  constructor
  intro n
  exact TickT.le_wp_tick' Q E n

/-- The frame inference procedure: shift by the pinned frame's amount, or by the whole current tick
count (`i.excessArgs[0]`, the first excess state argument of the `Nat → L` cost assertion). It emits
the split VC in the meet form `pre ⊑ (⌜shift ≤ ticks⌝ ⊓ residualPre (ticks - shift)) s⃗`; the built-in
meet split turns this into the tick guard (closed by `grind`) and the shifted residual
`pre ⊑ residualPre (ticks - shift) s⃗`. -/
def tickFrameProc : FrameInferenceProc := fun i => do
  unless i.Pred.isArrow && i.Pred.bindingDomain!.isConstOf ``Nat do return none
  let some ticks := i.excessArgs[0]? | return none
  let shift ← match i.providedFrame? with
    | some r => pure r
    | none => do
      -- Shifting by the whole tick count leaves `ticks - ticks`; skip when that normalizes to `0` so
      -- the proc does not re-fire on its own residual.
      let ticks ← instantiateMVarsS ticks
      let thms := ({} : Lean.Meta.Sym.Simp.Theorems).insert
        (← Lean.Meta.Sym.Simp.mkTheoremFromDecl ``Nat.sub_self)
      let post := Lean.Meta.Sym.Simp.evalGround >> thms.rewrite
      pure ((← Lean.Meta.Sym.simp ticks { post }).getResultExpr ticks)
  if shift.nat? == some 0 then return none
  -- Emit the split VC `pre ⊑ (costConj shift residualPre ticks) s⃗` in its `costConj_apply`-reduced
  -- meet form `pre ⊑ (⌜shift ≤ ticks⌝ ⊓ residualPre (ticks - shift)) s⃗` (definitionally equal), so the
  -- built-in meet split decomposes it: the tick guard closes by `grind`, the residual re-applies.
  let op ← i.mkOpApp
  let costL := op.getAppArgs[0]!
  let costInst := op.getAppArgs[1]!
  let us := op.getAppFn.constLevels!
  let residualPre ← i.mkResidualPre
  let guard ← mkAppNS (← mkConstS ``CompleteLattice.ofProp us)
    #[costL, costInst, ← mkAppNS (← mkConstS ``Nat.le) #[shift, ticks]]
  let residual ← mkAppNS (mkMVar residualPre) #[← mkAppNS (← mkConstS ``Nat.sub) #[ticks, shift]]
  let meet ← mkAppNS (← mkConstS ``Lean.Order.meet us) #[costL, costInst, guard, residual]
  let rhs ← mkAppNS meet (i.excessArgs.extract 1 i.excessArgs.size)
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS (← i.le) #[← i.pre, rhs])
  return some (FrameSplit.withDischargedSplitVC shift residualPre m [m.mvarId!])

/-- Register the cost frame inference procedure for `vcgen`, indexed by the `TickT` program type. The
frame operator `costConj` is built at the base lattice `L` read off the assertion type `Nat → L`, so it
frames the cost over any base monad. `costConj_apply` unfolds `costConj r b n` to
`⌜r ≤ n⌝ ⊓ b (n - r)` when discharging the split VC. -/
@[frameproc] def tickFP : FrameProc where
  prog := ``TickT
  mkOpAppM := fun info => Meta.mkAppOptM ``costConj #[some info.Pred.bindingBody!, none]
  mkResourceTy := fun _ => pure (mkConst ``Nat)
  opHead := ``costConj
  proc := tickFrameProc

/-- End-to-end: plain `vcgen` infers the shift, applies the `costConj` gadget, fires the registered
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
/-- error: lattice operator `keepFrame` neither reduces nor has a registered terminal; its split rule would be the identity -/
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
  | inv1 => fun pref _ _ n _ => n = pref.length
  with finish

/-- Two loops in sequence: `vcgen` infers and frames the second call by the cost the first accrued,
with no `frames` clause. -/
example {α : Type} (xs ys : List α) :
    (do tickList xs; tickList ys : TickT (StateM Nat) Unit) ⏱ (xs.length + ys.length) := by
  vcgen with finish

/-- The same goal with an explicit `frames` clause naming each call's shift. -/
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
