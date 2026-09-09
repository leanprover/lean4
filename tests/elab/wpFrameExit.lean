import Std.WP

/-!
The frame closure frames both channels: `frameClosure op` hands the framed exception postcondition
`opE r E` to the base transformer. On a two-constructor program type over a toy heap, `exit_spec`
shows the specification `⦃ l ↦ v ⦄ exit ⦃ ⊥; l ↦ v ⦄`: an exit owns exactly what it held, with the
frame pushed into the exception postcondition by the companion `opE := sepConj` at `EPred = Pred`.
The framed obligation is `∀ F, F ∗ P ⊑ F ∗ P`.
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

/-- The interpretation that frames both channels by `sepConj`. -/
@[instance_reducible] noncomputable def framedWPE : WP Prog Unit HProp HProp :=
  WP.of_frameClosure sepConj baseWP

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
  WP.le_wp_of_frameClosure_eq (base := baseWP) rfl fun _ => PartialOrder.rel_refl
