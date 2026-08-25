import Lean
import Std.WP
import Std.Tactic.Do

set_option experimental.vcgen true
set_option grind.warning false

/-!
# Meet framing through a `throw`

`ExceptT Unit (StateM σ)` keeps the state on `throw`, so its exception layer `Unit → σ → Prop`
carries the assertion type `σ → Prop` and the derived `EFrame` companion frames it pointwise. A
`frames` clause recovers a state fact on the normal exit and through the `throw` alike.
-/

open Lean Order Meta Elab Tactic Sym Std WP

abbrev AppState := Nat × Nat

abbrev M := ExceptT Unit (StateM AppState)

/-- Bump `fst`, or throw when it is spent. The state survives the throw. -/
@[irreducible] def bumpOrThrow : M Nat := do
  let s ← get
  if s.1 > 9 then throw ()
  set ((s.1 + 1 : Nat), s.2)
  pure s.1

/-- The derived exception-channel companion of the meet at `M`'s exception stack: pointwise meet
on the layer, identity on the empty tail. -/
abbrev opE (r : AppState → Prop) (p : EStack⟨Unit → AppState → Prop⟩) :
    EStack⟨Unit → AppState → Prop⟩ :=
  (fun e => r ⊓ p.1 e, p.2)

/-- Lossy spec: says nothing about `s.2` on either exit. -/
@[spec] theorem bumpOrThrow_spec :
    ⦃ fun s => ⌜s.1 = n⌝ ⦄ (bumpOrThrow : M Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + 1⌝; estack⟨fun _ s => ⌜s.1 = n⌝⟩ ⦄ := by
  unfold bumpOrThrow
  vcgen <;> simp_all

/-- `bumpOrThrow` frames any `P` outside its `fst` footprint, on both channels. -/
@[grind .]
theorem frames_bumpOrThrow {P : AppState → Prop}
    (h : ∀ s a, P { s with fst := a } = P s) :
    PredTrans.Frames (· ⊓ ·) opE (WP.wpTrans (bumpOrThrow : M Nat)) P := by
  refine WP.frames_of_conjunctive ?_ ?_
  · vcgen [bumpOrThrow] with finish
  · intro E
    refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (Prod.mk_meet _ _).symm) ?_
    refine Prod.mk_le _ _ _ ?_ (meet_le_right _ _)
    intro e s hs
    simp only [meet_apply, meet_prop_eq_and] at hs ⊢
    exact ⟨hs.1.1, hs.2⟩

/-- Pointwise counit for the derived wand: `F s → E.fst e s` lands in the wand at `(e, s)`. -/
theorem ua_opE_fst {F : AppState → Prop} {E : EStack⟨Unit → AppState → Prop⟩}
    (e : Unit) (s : AppState) (h : F s → E.fst e s) :
    (PreservesSup.upperAdjoint (opE F) E).fst e s := by
  have hle : ((fun e' => F ⇨ E.fst e', E.snd) : EStack⟨Unit → AppState → Prop⟩)
      ⊑ PreservesSup.upperAdjoint (opE F) E := by
    apply PreservesSup.le_upperAdjoint
    refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro e'
    exact meet_himp_le
  refine hle.left e s ?_
  simp only [himp_apply, himp_prop_eq_imp]
  exact h


/-- The frame recovers `s.2 = 7`, which the lossy spec dropped, on the normal exit and through
the `throw`. -/
example : ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (bumpOrThrow : M Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = 7⌝; estack⟨fun _ s => ⌜s.2 = 7⌝⟩ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | bumpOrThrow => fun s => ⌜s.2 = 7⌝
  -- The exceptional-channel VC: the spec's exit lands in the wand of the goal postcondition.
  case vc2 => exact ua_opE_fst _ _ fun h => h
  all_goals grind
