import Std.WP

/-!
The frame closure frames both channels: `frameClosure op opE` hands the framed exception
postcondition `opE r E` to the base transformer. On a two-constructor program type over a toy heap
this file shows:

1. `exit_spec_fails`: with the identity `opE`, the specification `⦃ l ↦ v ⦄ exit ⦃ ⊥; l ↦ v ⦄`,
   which says an exit owns exactly what it held, is unprovable. The characterization
   `WP.of_frameClosure_le_wp_iff` reduces it to `∀ F, F ∗ (l ↦ v) ⊑ (l ↦ v)`, and a two-cell heap
   refutes that: the identity `opE` only supports frame-absorbing exit assertions.

2. `exit_spec`: with `opE := sepConj`, the diagonal `EFrame` instance at `EPred = Pred`, the same
   specification holds. The framed obligation is `∀ F, F ∗ P ⊑ F ∗ P`.
-/

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

/-- Heap assertions. -/
abbrev HProp : Type := Heap → Prop

/-- The cell `l` holds `v`, and nothing else is owned. -/
def pointsTo (l : Addr) (v : Nat) : HProp := fun h => h = Heap.single l v

local notation:70 l:max " ↦ " v:max => pointsTo l v

/-- Separating conjunction. -/
def sepConj (P Q : HProp) : HProp :=
  fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

local infixr:65 " ∗ " => sepConj

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

/-! ## 1. The identity `opE` cannot carry exact ownership across an exit -/

/-- The identity-`opE` interpretation: only the value channel is framed. -/
@[instance_reducible] noncomputable def framedWP : WP Prog Unit HProp HProp :=
  WP.of_frameClosure sepConj (fun _ E => E) baseWP

/-- A frame does not vanish: `F ∗ P` at a two-cell heap refutes `P`. -/
theorem sepConj_not_absorbed :
    ¬ (∀ F : HProp, (F ∗ (0 ↦ 1)) ⊑ (0 ↦ 1)) := by
  intro habs
  have hdisj : (Heap.single 2 3).disjoint (Heap.single 0 1) := by
    intro n
    by_cases h2 : n = 2
    · subst h2; right; simp [Heap.single]
    · left; simp [Heap.single, h2]
  have h := habs (2 ↦ 3) ((Heap.single 2 3).union (Heap.single 0 1))
    ⟨_, _, hdisj, rfl, rfl, rfl⟩
  have := congrFun h 2
  simp [Heap.single, Heap.union] at this

/-- The specification `⦃ l ↦ v ⦄ exit ⦃ ⊥; l ↦ v ⦄` reduces, at the identity `opE`, to frames
being absorbed. -/
theorem exit_spec_iff_absorbed :
    (((0 ↦ 1) : HProp) ⊑ framedWP.wp .exit (fun _ => ⊥) (0 ↦ 1))
      ↔ (∀ F : HProp, (F ∗ (0 ↦ 1)) ⊑ (0 ↦ 1)) := by
  rw [show framedWP = WP.of_frameClosure sepConj (fun _ E => E) baseWP from rfl]
  rw [WP.of_frameClosure_le_wp_iff]
  constructor <;> intro h F <;> exact h F

theorem exit_spec_fails :
    ¬ (((0 ↦ 1) : HProp) ⊑ framedWP.wp .exit (fun _ => ⊥) (0 ↦ 1)) :=
  fun h => sepConj_not_absorbed (exit_spec_iff_absorbed.mp h)

/-! ## 2. Framing the exception channel by `sepConj` -/

/-- At `EPred = Pred`, the diagonal instance derives `opE := sepConj` from `op := sepConj`. -/
example : EFrame sepConj HProp sepConj := inferInstance

/-- The interpretation that frames both channels by `sepConj`. -/
@[instance_reducible] noncomputable def framedWPE : WP Prog Unit HProp HProp :=
  WP.of_frameClosure sepConj sepConj baseWP

/-- Landing below the closure at the transformer level: the framed obligation is
`∀ F, F ∗ P ⊑ F ∗ P`. -/
theorem exit_spec_frameClosure :
    ((0 ↦ 1) : HProp) ⊑
      ((baseWP.wpTrans .exit).frameClosure sepConj sepConj).apply (fun _ => ⊥) (0 ↦ 1) := by
  rw [PredTrans.le_frameClosure_iff]
  intro F
  exact PartialOrder.rel_refl

/-- The exit specification, at the `wp` layer. -/
theorem exit_spec :
    ((0 ↦ 1) : HProp) ⊑ framedWPE.wp .exit (fun _ => ⊥) (0 ↦ 1) :=
  WP.le_wp_of_frameClosure_eq (base := baseWP) rfl fun _ => PartialOrder.rel_refl
