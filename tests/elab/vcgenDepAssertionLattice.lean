import Std.Tactic.Do
import Std.Internal.Do

/-!
Regression test for a *dependent* assertion language `(st : State) → st.Invariant → Prop`. Its order
is the pointwise function order, but `vcgen`'s peel rule `le_of_forall_le` cannot currently be
applied to a dependent function lattice. `vcgen` must report a clear error instead of looping until
it runs out of heartbeats. Extracted from a user report.
-/

set_option mvcgen.warning false

open Std.Internal.Do

opaque State : Type
opaque State.Invariant : State → Prop

def Stateful (a : Type) := State → Option a × State

instance : Monad Stateful where
  pure x := fun st => (some x, st)
  bind x f := fun st =>
    let (xOptVal, stMid) := x st
    match xOptVal with
    | none => (none, stMid)
    | some xVal => f xVal stMid

def Stateful.run (x : Stateful a) (st : State) : Option a × State := x st

instance : LawfulMonad Stateful :=
  LawfulMonad.mk' Stateful
    (id_map := by simp only [Functor.map, Function.comp_apply, id_eq]; intro _ x; funext; grind)
    (pure_bind := by simp [pure, bind])
    (bind_assoc := by intro _ _ _ x f g; simp only [bind]; funext; grind)

/-- A dependent assertion language: the postcondition `Prop` may depend on a proof about the state.
An `abbrev`, so the carrier unfolds to the dependent Pi and `Assertion`/`PartialOrder` are the generic
pointwise function-lattice instances. -/
abbrev StateProp := (st : State) → st.Invariant → Prop

instance Stateful.instWP {α : Type} : WP (Stateful α) α StateProp EPost⟨⟩ where
  wpTrans f := ⟨fun post _epost =>
    fun st _ =>
      let (optRes, stOut) := f.run st
      ∃ h : stOut.Invariant,
      match optRes with
      | none => True
      | some res => post res stOut h⟩
  wp_trans_monotone x := by
    simp only [PredTrans.monotone, Lean.Order.PartialOrder.rel, Stateful.run]; grind

theorem Stateful.wpTrans_apply_eq {α : Type} (x : Stateful α)
    (post : α → StateProp) (epost : EPost⟨⟩) (st : State) (h : st.Invariant) :
    wp x post epost st h
      = ∃ h' : (x st).2.Invariant,
          match (x st).1 with
          | none => True
          | some r => post r (x st).2 h' := rfl

instance : WPMonad Stateful StateProp EPost⟨⟩ where
  toWP _ := Stateful.instWP
  pure_le_wp_pure x post epost := by
    intro st h hp; exact ⟨h, hp⟩
  bind_le_wp_bind x f post epost := by
    intro st h hp
    simp only [Stateful.wpTrans_apply_eq, bind] at hp ⊢
    grind

/--
error: failed to apply Lean.Order.le_of_forall_le to goal
  Lean.Order.PartialOrder.rel (fun x x_1 => True) (wp (pure PUnit.unit) (fun x x_1 x_2 => True) epost⟨⟩)
-/
#guard_msgs in
example : ⦃ fun _ _ => True ⦄ (pure () : Stateful Unit) ⦃ fun _ _ _ => True; epost⟨⟩ ⦄ := by
  vcgen
