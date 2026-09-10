import Lean
import Std.WP
import Std.Tactic.Do

/-!
The frame closure frames both channels: `frameClosure op` hands the framed exception postcondition
`opE r E` to the base transformer. On a two-constructor program type over a toy heap, `exit_spec`
shows the specification `⦃ l ↦ v ⦄ exit ⦃ ⊥; l ↦ v ⦄`: an exit owns exactly what it held, with the
frame pushed into the exception postcondition by the companion `opE := sepConj` at `EPred = Pred`.
The framed obligation is `∀ F, F ∗ P ⊑ F ∗ P`. `exit_frames_via_vcgen` runs the same scenario
through `vcgen`: a lossy spec drops a framed cell and a `frames` clause recovers it through the
exception channel.
-/

set_option experimental.vcgen true
set_option grind.warning false

open Lean.Order Std.WP Std.Internal.Order

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

@[simp] theorem Heap.union_none_iff (h₁ h₂ : Heap) (n : Addr) :
    h₁.union h₂ n = none ↔ h₁ n = none ∧ h₂ n = none := by
  simp only [Heap.union]; cases h₁ n <;> simp

theorem Heap.disjoint_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₂.disjoint h₁ :=
  fun n => (h n).symm

theorem Heap.union_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₁.union h₂ = h₂.union h₁ := by
  funext n; simp only [Heap.union]; rcases h n with hn | hn <;> simp [hn]

theorem Heap.union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  funext n; simp only [Heap.union]; cases h₁ n <;> rfl

theorem Heap.disjoint_union_left {h₁ h₂ h₃ : Heap} :
    (h₁.union h₂).disjoint h₃ ↔ h₁.disjoint h₃ ∧ h₂.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_left (·.1), fun n => (h n).imp_left (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

theorem Heap.disjoint_union_right {h₁ h₂ h₃ : Heap} :
    h₁.disjoint (h₂.union h₃) ↔ h₁.disjoint h₂ ∧ h₁.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_right (·.1), fun n => (h n).imp_right (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

/-- Heap assertions. A `def`, so the wp pipeline treats assertions as atoms instead of
introducing the heap argument. -/
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

@[grind =] theorem sepConj_comm (a b : HProp) : (a ∗ b) = (b ∗ a) := by
  funext h; apply propext
  constructor <;>
    · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
      exact ⟨h₂, h₁, Heap.disjoint_comm hd, Heap.union_comm hd, hq, hp⟩

theorem sepConj_assoc (a b c : HProp) : ((a ∗ b) ∗ c) = (a ∗ (b ∗ c)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨_, h₃, hd, rfl, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩
    obtain ⟨hd13, hd23⟩ := Heap.disjoint_union_left.mp hd
    exact ⟨h₁, h₂.union h₃, Heap.disjoint_union_right.mpr ⟨hd12, hd13⟩,
      Heap.union_assoc h₁ h₂ h₃, ha, h₂, h₃, hd23, rfl, hb, hc⟩
  · rintro ⟨h₁, _, hd, rfl, ha, ⟨h₂, h₃, hd23, rfl, hb, hc⟩⟩
    obtain ⟨hd12, hd13⟩ := Heap.disjoint_union_right.mp hd
    exact ⟨h₁.union h₂, h₃, Heap.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩

/-- The generic sup on `HProp`, pointwise (via the lattice axioms alone). -/
theorem hprop_sup_apply (s : HProp → Prop) (h : Heap) :
    (CompleteLattice.sup s : HProp) h ↔ ∃ f, s f ∧ f h := by
  constructor
  · exact fun hh => sup_le s (x := fun h => ∃ f, s f ∧ f h)
      (fun f hf h' hfh' => ⟨f, hf, hfh'⟩) h hh
  · rintro ⟨f, hf, hfh⟩; exact le_sup (c := s) hf h hfh

/-- `(F ∗ ·)` preserves suprema, so it has an upper adjoint (the magic wand). -/
instance (F : HProp) : PreservesSup (sepConj F) where
  map_sup s := by
    funext h
    apply propext
    rw [hprop_sup_apply]
    constructor
    · rintro ⟨h₁, h₂, hd, rfl, hF, hsup⟩
      obtain ⟨f, hf, hfh⟩ := (hprop_sup_apply s h₂).mp hsup
      exact ⟨F ∗ f, ⟨f, hf, rfl⟩, h₁, h₂, hd, rfl, hF, hfh⟩
    · rintro ⟨g, ⟨f, hf, rfl⟩, h₁, h₂, hd, rfl, hF, hfh⟩
      exact ⟨h₁, h₂, hd, rfl, hF, (hprop_sup_apply s h₂).mpr ⟨f, hf, hfh⟩⟩

/-- Monotonicity of `∗` in its right argument. -/
theorem sepConj_mono_right (a : HProp) {b b' : HProp} (h : b ⊑ b') : a ∗ b ⊑ a ∗ b' :=
  PreservesSup.map_mono (sepConj a) h

/-! ## A program type with an exit

`skip` falls through; `exit` leaves through the exception channel, carrying the heap. The base wp
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

A lossy spec owns only `0 ↦ 1`; the `frames` clause pins `5 ↦ 7` and `vcgen` carries it into the
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

open Lean Meta Sym Lean.Elab.Tactic.VCGen

/-- Pin-only frame inference for `Prog`: the goal precondition is `footprint ∗ frame` with the
pinned frame on the right, so commuting it and framing the spec proof discharges the split VC. -/
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
