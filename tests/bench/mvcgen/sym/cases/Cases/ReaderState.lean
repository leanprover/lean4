import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace ReaderState

set_option mvcgen.warning false

abbrev M := ReaderT Nat <| StateM Nat

-- Partially evaluated specs for best performance.

@[spec high]
theorem Spec.M_read :
    ⦃fun r s => Q.fst r r s⦄ read (m := M) ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_get :
    ⦃fun r s => Q.fst s r s⦄ get (m := M) ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_set (n : Nat) :
    ⦃fun r _ => Q.fst () r n⦄ set (m := M) n ⦃Q⦄ := by
  mvcgen

def step : M Unit := do
  let r ← read
  let s ← get
  set (s + r)
  let s ← get
  set (s - r)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

end ReaderState
