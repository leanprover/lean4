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
# A minimal separation logic for `vcgen` frame inference

A heap `Heap := Nat → Option Nat` with separating conjunction `∗` (disjoint union), magic wand `-∗`,
and points-to `↦`. Unlike the lattice meet, `∗` is not cartesian: `l ↦ v ∗ l ↦ v = ⊥`. The frame
operator is `∗` itself; its upper adjoint is the wand. `HeapM.wp` is the `frameClosure` of the base
`StateM Heap` wp over `∗`, so every program frames every heap assertion by construction. The `iFrame`
step is proved by hand, exposing where the frame-inference path does and does not fit `∗`.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do Std.Internal.Do.CompleteLattice

/-! ## Heaps and the separation algebra -/

/-- A heap maps locations to optionally-present values. -/
abbrev Heap := Nat → Option Nat

/-- Two heaps are disjoint when no location is present in both. -/
def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ n, h₁ n = none ∨ h₂ n = none

/-- Union of heaps, preferring the left value on overlap (agreeing with disjointness). -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun n => (h₁ n).or (h₂ n)

/-- The singleton heap holding `v` at `l`. -/
def Heap.single (l v : Nat) : Heap := fun n => if n = l then some v else none

/-- Overwrite location `l` with `w`. -/
def Heap.update (h : Heap) (l w : Nat) : Heap := fun n => if n = l then some w else h n

@[simp] theorem Heap.union_none_iff (h₁ h₂ : Heap) (n : Nat) :
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

/-! ## Heap assertions

`HProp` is an opaque `def`, not `Heap → Prop`, so `vcgen` treats the heap as a resource dimension
rather than a state to introduce pointwise (which would destroy `∗`). The lattice is the pointwise
order transported from `Heap → Prop`. -/
def HProp : Type := Heap → Prop

instance : CompleteLattice HProp := inferInstanceAs (CompleteLattice (Heap → Prop))

/-! ## The separation-logic connectives -/

/-- The empty heap assertion. -/
def emp : HProp := fun h => ∀ n, h n = none

/-- The singleton heap assertion: the heap is exactly `l ↦ v`. -/
def pointsTo (l v : Nat) : HProp := fun h => h = Heap.single l v

/-- Separating conjunction: the heap splits into disjoint parts satisfying each side. -/
def sepConj (P Q : HProp) : HProp :=
  fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

/-- Magic wand: extending by any disjoint `P` heap yields a `Q` heap. -/
def wand (P Q : HProp) : HProp :=
  fun h => ∀ h', h.disjoint h' → P h' → Q (h.union h')

@[inherit_doc pointsTo] local notation:70 l:max " ↦ " v:max => pointsTo l v
@[inherit_doc sepConj] local infixr:65 " ∗ " => sepConj
@[inherit_doc wand] local infixr:60 " -∗ " => wand

/-! ## The separation algebra laws -/

theorem emp_sepConj (a : HProp) : (emp ∗ a) = a := by
  funext h
  apply propext
  constructor
  · rintro ⟨h₁, h₂, _, rfl, he, ha⟩
    have : h₁.union h₂ = h₂ := by funext n; simp only [Heap.union, he n, Option.none_or]
    rwa [this]
  · intro ha
    exact ⟨fun _ => none, h, fun _ => Or.inl rfl,
      by funext n; simp only [Heap.union, Option.none_or], fun _ => rfl, ha⟩

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

theorem sepConj_comm (a b : HProp) : (a ∗ b) = (b ∗ a) := by
  funext h; apply propext
  constructor <;>
    · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
      exact ⟨h₂, h₁, Heap.disjoint_comm hd, Heap.union_comm hd, hq, hp⟩

/-! ## `∗` preserves sups and its upper adjoint is the wand -/

/-- Pointwise characterization of the sup on `HProp`. -/
theorem hprop_sup_apply (s : HProp → Prop) (h : Heap) :
    CompleteLattice.sup s h = ∃ f, s f ∧ f h := by
  apply propext
  constructor
  · exact fun hh => sup_le s (x := fun h => ∃ f, s f ∧ f h)
      (fun f hf h' hfh' => ⟨f, hf, hfh'⟩) h hh
  · rintro ⟨f, hf, hfh⟩; exact le_sup (c := s) hf h hfh

instance (F : HProp) : PreservesSup (sepConj F) where
  map_sup s := by
    funext h
    apply propext
    simp only [sepConj, hprop_sup_apply]
    constructor
    · rintro ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩
      exact ⟨sepConj F x, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
    · rintro ⟨f, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
      exact ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩

/-- The counit of the adjunction `F ∗ · ⊣ F -∗ ·`. -/
theorem sepConj_wand_le (F b : HProp) : (F ∗ (F -∗ b)) ⊑ b := by
  rintro h ⟨h₁, h₂, hd, rfl, hF, hw⟩
  have := hw h₁ (Heap.disjoint_comm hd) hF
  rwa [Heap.union_comm (Heap.disjoint_comm hd)] at this

/-- The upper adjoint of `F ∗ ·` is the magic wand `F -∗ ·`. -/
theorem sepConj_upperAdjoint (F b : HProp) :
    PreservesSup.upperAdjoint (sepConj F) b = (F -∗ b) := by
  apply PartialOrder.rel_antisymm
  · unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx h hxh h' hdisj hF
    apply hx (h.union h')
    exact ⟨h', h, Heap.disjoint_comm hdisj, Heap.union_comm hdisj, hF, hxh⟩
  · exact PreservesSup.le_upperAdjoint (sepConj F) (sepConj_wand_le F b)

/-! ## The heap monad and its frame-internalizing weakest precondition -/

/-- The heap state monad. A `def` so it carries its own frame-internalizing `WP`. -/
def HeapM (α : Type) : Type := StateM Heap α

instance : Monad HeapM := inferInstanceAs (Monad (StateM Heap))
instance : LawfulMonad HeapM := inferInstanceAs (LawfulMonad (StateM Heap))

/-- A `HeapM` program as its underlying `StateM Heap` program, carrying the base wp. -/
def HeapM.run {α : Type} (x : HeapM α) : StateM Heap α := x

/-- The frame-internalizing weakest precondition: the `frameClosure` of the base `StateM Heap` wp
over separating conjunction. -/
noncomputable instance HeapM.instWPMonad : WPMonad HeapM HProp EPost.Nil :=
  WPMonad.of_frameClosure (m := StateM Heap) sepConj sepConj_assoc emp_sepConj StateT.instWPMonad

/-- Every `HeapM` program frames every heap assertion `F`. -/
@[grind .]
theorem frames_sepConj {α : Type} (x : HeapM α) (F : HProp) : WP.Frames sepConj x F :=
  WP.Frames.of_frameClosure sepConj sepConj sepConj_assoc
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

/-! ## A heap operation and its spec -/

/-- Store `w` at location `l`. -/
def store (l w : Nat) : HeapM Unit :=
  show StateM Heap Unit from modifyGet (fun h => ((), h.update l w))

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Storing overwrites the cell, framing every disjoint heap by construction. -/
@[spec] theorem store_spec (l v w : Nat) :
    ⦃ pointsTo l v ⦄ (store l w) ⦃ fun _ => pointsTo l w ⦄ := by
  constructor
  show (pointsTo l v) ⊑ PreservesSup.frameClosure sepConj
    (fun Q' => WP.wp (store l w).run Q' ⊥) (fun _ => pointsTo l w)
  refine (PreservesSup.le_frameClosure_iff sepConj _).mpr fun F => ?_
  refine PartialOrder.rel_trans ?_
    (WPMonad.le_wp_modifyGet_StateT_apply (m := Id) (fun h : Heap => ((), h.update l w)) _ _)
  rintro h ⟨hF, _, hd, rfl, hFh, rfl⟩
  refine ⟨hF, Heap.single l w, ?_, ?_, hFh, rfl⟩
  · intro n; rcases hd n with h' | h'
    · exact Or.inl h'
    · right; simp only [Heap.single] at h' ⊢; grind
  · funext n
    simp only [Heap.update, Heap.union, Heap.single]
    by_cases hn : n = l
    · subst hn; have := hd n; simp only [Heap.single] at this; grind
    · simp [hn]

/-! ## Separation-logic structural lemmas for the frame split -/

theorem sepConj_mono_r {a b b' : HProp} (h : b ⊑ b') : (a ∗ b) ⊑ (a ∗ b') := by
  rintro heap ⟨h₁, h₂, hd, rfl, ha, hb⟩; exact ⟨h₁, h₂, hd, rfl, ha, h _ hb⟩

/-- The frame introduction rule: to land in `F ∗ R`, cancel `F` off the right of the precondition
and continue with the residual `R`. -/
theorem sepConj_frame_r {pre₀ F R : HProp} (h : pre₀ ⊑ R) : (pre₀ ∗ F) ⊑ (F ∗ R) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_comm pre₀ F)) (sepConj_mono_r h)

/-! ## The registered frame procedure for `∗` -/

/-- Flatten a `∗`-tree into its atoms. -/
partial def sepAtoms (e : Expr) : Array Expr :=
  if e.isAppOf ``sepConj then sepAtoms e.appFn!.appArg! ++ sepAtoms e.appArg!
  else #[e]

/-- Automatic frame inference by domain difference: the spec's precondition `specPre` (a `∗` of atoms,
its footprint) is cancelled from the actual precondition `pre`; the leftover atoms are the frame. `none`
when the footprint does not match or nothing is left over, so the spec applies without a frame. -/
def sepConjFrameProc : FrameInferenceProc := fun _R pre _info specPre => do
  let mut rest := sepAtoms pre
  for atom in sepAtoms specPre do
    let some i ← rest.findIdxM? (isDefEqS atom ·) | return none
    rest := rest.eraseIdxIfInBounds i
  if rest.isEmpty then return none
  return some (rest.pop.foldr (fun a acc => mkApp2 (mkConst ``sepConj) a acc) rest.back!)

/-- The lattice split for `∗` is the terminal `sepConj_frame_r`: `pre ⊑ F ∗ R` cancels `F` from the
precondition, leaving the residual `pre₀ ⊑ R`. -/
@[frameproc] def heapFP : FrameProc where
  prog := ``HeapM
  mkOpAppM := fun _ => pure (mkConst ``sepConj)
  resourceTy := fun _ => pure (mkConst ``HProp)
  op := { head := ``sepConj, numConst := 0, terminal? := ``sepConj_frame_r }
  proc := some sepConjFrameProc

/-! ## The `iFrame` example: carry a disjoint cell across a `store`

`vcgen` applies the `∗` frame gadget with the frame, fires the `sepConj_frame_r` split to cancel the
framed cell from the precondition, and `finish` discharges the residual wand and the frame condition
(`frames_sepConj`). The `∗` split reaches `vcgen` because `heapFP`/`sepSplit` declare `numParams := 0`:
`sepConj` is monomorphic, with no carrier/instance prefix before its operands.

The frame is either inferred by `sepConjFrameProc` (the domain difference between the actual and the
spec precondition) or supplied explicitly via the `frames` clause. -/

/-- Storing to `l1` carries the disjoint cell `l2 ↦ b` untouched, framed automatically by `vcgen`. This
is the separation-logic move that would be `iFrame "Hl2"` in Iris. -/
example (l1 l2 a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] with finish

/-- The same goal with the frame supplied explicitly. -/
example (l1 l2 a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] frames | store l1 x => (pointsTo l2 b) with finish
