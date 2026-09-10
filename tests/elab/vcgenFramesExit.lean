import Lean
import Std.WP
import Std.Tactic.Do

/-!
Tests for framing the exception channel.

The first part works on a two-constructor program type over a toy heap. `exit_spec` shows the
specification `⦃ l ↦ v ⦄ exit ⦃ ⊥; l ↦ v ⦄`: an exit owns exactly what it held. The companion
`opE := sepConj` at `EPred = Pred` pushes the frame into the exception postcondition. The framed
obligation is `∀ F, F ∗ P ⊑ F ∗ P`. `exit_frames_via_vcgen` runs the same scenario through
`vcgen`: a lossy spec drops a framed cell and a `frames` clause recovers it. The separation
algebra facts are axioms. Only the framing theorems carry proofs.

The second part frames by `meet` through a `throw` in `ExceptT Unit (StateM σ)`.
-/

set_option experimental.vcgen true
set_option grind.warning false

open Lean Order Meta Elab Tactic Sym Std WP

/-! ## A toy heap and its assertions -/

abbrev Addr := Nat

/-- A heap maps addresses to optionally-present values. -/
abbrev Heap := Addr → Option Nat

/-- Two heaps are disjoint when no location is present in both. -/
def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ n, h₁ n = none ∨ h₂ n = none

/-- Union of heaps, preferring the left value. -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun n => (h₁ n).or (h₂ n)

/-- The singleton heap holding `v` at `l`. -/
def Heap.single (l : Addr) (v : Nat) : Heap := fun n => if n = l then some v else none

/-- Heap assertions. A `def`, so the wp pipeline treats assertions as atoms. -/
def HProp : Type := Heap → Prop

instance : Lean.Order.CompleteLattice HProp :=
  inferInstanceAs (Lean.Order.CompleteLattice (Heap → Prop))

instance : Std.WP.Assertion HProp := inferInstanceAs (Std.WP.Assertion (Heap → Prop))

/-- The cell `l` holds `v`, and nothing else is owned. -/
def pointsTo (l : Addr) (v : Nat) : HProp := fun h => h = Heap.single l v

local notation:70 l:max " ↦ " v:max => pointsTo l v

/-- Separating conjunction. -/
def sepConj (P Q : HProp) : HProp :=
  fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

local infixr:65 " ∗ " => sepConj

axiom sepConj_comm (a b : HProp) : (a ∗ b) = (b ∗ a)

axiom sepConj_assoc (a b c : HProp) : ((a ∗ b) ∗ c) = (a ∗ (b ∗ c))

/-- `(F ∗ ·)` preserves suprema, so it has an upper adjoint (the magic wand). -/
axiom preservesSup_sepConj (F : HProp) : PreservesSup (sepConj F)

instance (F : HProp) : PreservesSup (sepConj F) := preservesSup_sepConj F

/-- Monotonicity of `∗` in its right argument. -/
axiom sepConj_mono_right (a : HProp) {b b' : HProp} (h : b ⊑ b') : a ∗ b ⊑ a ∗ b'

/-! ## A program type with an exit

`skip` falls through. `exit` leaves through the exception channel, carrying the heap. The base wp
is the evident one. -/

inductive Prog | skip | exit

/-- The base wp: `skip` hands the heap to the postcondition, `exit` to the exception
postcondition. -/
@[instance_reducible] def baseWP : WP Prog Unit HProp HProp where
  wpTrans x := ⟨fun Q E => match x with | .skip => Q () | .exit => E⟩
  wp_trans_monotone x := by
    intro Q Q' E E' hE hQ
    cases x
    · exact hQ ()
    · exact hE

/-- The interpretation that frames both channels by `sepConj`. -/
@[instance_reducible] noncomputable def framedWPE : WP Prog Unit HProp HProp :=
  WP.withFrameClosure sepConj baseWP

noncomputable instance : WP Prog Unit HProp HProp := framedWPE

/-- Landing below the closure at the transformer level: the framed obligation is
`∀ F, F ∗ P ⊑ F ∗ P`. -/
theorem exit_spec_frameClosure :
    ((0 ↦ 1) : HProp) ⊑
      ((baseWP.wpTrans .exit).frameClosure sepConj).apply (fun _ => ⊥) (0 ↦ 1) := by
  rw [PredTrans.le_frameClosure_iff]
  intro F
  exact PartialOrder.rel_refl

/-- The exit specification, at the `wp` layer. -/
theorem exit_spec :
    ((0 ↦ 1) : HProp) ⊑ framedWPE.wp .exit (fun _ => ⊥) (0 ↦ 1) :=
  WP.le_wp_of_withFrameClosure_eq (base := baseWP) rfl fun _ => PartialOrder.rel_refl

/-! ## `vcgen`: framing through the exit

A lossy spec owns only `0 ↦ 1`. The `frames` clause pins `5 ↦ 7`, and `vcgen` carries it into the
exception postcondition through the frame rule. -/

/-- Every `Prog` frames every heap assertion `F` on both channels. -/
@[grind .]
theorem frames_exit (x : Prog) (F : HProp) :
    PredTrans.Frames sepConj (WP.wpTrans x) F :=
  WP.frames_of_frameClosure sepConj sepConj sepConj_assoc sepConj_assoc
    ⟨fun y => baseWP.wpTrans y, fun _ => rfl⟩

/-- Lossy spec: owns `0 ↦ 1` and says nothing about the rest of the heap. -/
@[spec]
theorem exit_spec_lossy :
    ⦃ ((0 : Addr) ↦ 1) ⦄ Prog.exit ⦃ fun _ => (⊥ : HProp); ((0 : Addr) ↦ 1) ⦄ :=
  ⟨WP.le_wp_of_withFrameClosure_eq (base := baseWP) rfl fun _ => PartialOrder.rel_refl⟩

open Lean.Elab.Tactic.VCGen

/-- Pin-only frame inference for `Prog`: the goal precondition is `footprint ∗ frame` with the
pinned frame on the right. Commuting it and framing the spec proof discharges the split VC. -/
def exitFrameProc : FrameInferenceProc := fun i => do
  let some frame := i.providedFrame? | return .decline
  return .commit #[] fun goal => do
    let frame ← shareCommon frame
    let specPre ← shareCommon (← instantiateMVars goal.specPre)
    goal.frame.assign frame
    goal.footprint.assign specPre
    let prf ← mkAppM ``PartialOrder.rel_trans
      #[← mkAppM ``PartialOrder.rel_of_eq #[← mkAppM ``sepConj_comm #[specPre, frame]],
        ← mkAppM ``sepConj_mono_right #[frame, goal.specProof]]
    return { splitVCProof := prf, subgoals := [] }

@[frameproc] def progFP : FrameProc where
  prog := ``Prog
  mkOpAppM := fun _ => pure (mkConst ``sepConj)
  mkResourceTy := fun _ => pure (mkConst ``HProp)
  opHead := ``sepConj
  proc := exitFrameProc

/-- `vcgen` recovers the framed `5 ↦ 7` through the exit: `exit_spec_lossy` drops it, the `frames`
clause carries it into the exception postcondition. -/
theorem exit_frames_via_vcgen :
    ⦃ ((0 : Addr) ↦ 1) ∗ ((5 : Addr) ↦ 7) ⦄ Prog.exit
    ⦃ fun _ => (⊥ : HProp); ((0 : Addr) ↦ 1) ∗ ((5 : Addr) ↦ 7) ⦄ := by
  vcgen frames | Prog.exit => ((5 : Addr) ↦ 7)
  case vc1 => exact frames_exit _ _
  case vc2 => exact PartialOrder.rel_of_eq (sepConj_comm _ _)
  case vc3 =>
    rintro h ⟨_, h₂, _, _, _, hbot⟩
    exact bot_le (fun _ => (⊥ : HProp) h) h₂ hbot

abbrev AppState := Nat × Nat

/-! ## Meet framing through a `throw`

`ExceptT ε (StateM σ)` keeps the state on `throw`, so its exception layer `Unit → σ → Prop`
carries the assertion type `σ → Prop` and the derived `FrameOp` companion frames it pointwise. A
`frames` clause recovers a state fact on the normal exit and through the `throw` alike. -/

abbrev MEx := ExceptT Unit (StateM AppState)

/-- Bump `fst`, or throw when it is spent. The state survives the throw. -/
@[irreducible] def bumpOrThrow : MEx Nat := do
  let s ← get
  if s.1 > 9 then throw ()
  set ((s.1 + 1 : Nat), s.2)
  pure s.1

/-- Lossy spec: says nothing about `s.2` on either exit. -/
@[spec] theorem bumpOrThrow_spec :
    ⦃ fun s => ⌜s.1 = n⌝ ⦄ (bumpOrThrow : MEx Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + 1⌝; estack⟨fun _ s => ⌜s.1 = n⌝⟩ ⦄ := by
  unfold bumpOrThrow
  vcgen <;> simp_all

/-- `bumpOrThrow` frames any `P` outside its `fst` footprint, on both channels: the derived
companion is the pointwise meet on the exception layer and the ignoring companion on the empty
tail. -/
@[grind .]
theorem frames_bumpOrThrow {P : AppState → Prop}
    (h : ∀ s a, P { s with fst := a } = P s) :
    PredTrans.Frames meet (WP.wpTrans (bumpOrThrow : MEx Nat)) P := by
  refine WP.frames_of_conjunctive ?_ ?_
  · vcgen [bumpOrThrow] with finish
  · intro E
    refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (Prod.mk_meet _ _).symm) ?_
    refine Prod.mk_le _ _ _ ?_ ?_
    · intro e s hs
      simp only [FrameOp.prod_fst, FrameOp.pointwise_apply, meet_apply, meet_prop_eq_and] at hs ⊢
      exact ⟨hs.1.1, hs.2⟩
    · simp only [FrameOp.prod_snd, FrameOp.ignore_apply]
      exact meet_le_right _ _

/-- The frame recovers `s.2 = 7`, which the lossy spec dropped, on the normal exit and through
the `throw`. -/
theorem recovers_through_throw :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (bumpOrThrow : MEx Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = 7⌝; estack⟨fun _ s => ⌜s.2 = 7⌝⟩ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | bumpOrThrow => fun s => ⌜s.2 = 7⌝ with finish
