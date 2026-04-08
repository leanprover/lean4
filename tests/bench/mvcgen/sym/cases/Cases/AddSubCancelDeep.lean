import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace AddSubCancelDeep

set_option mvcgen.warning false

/-!
Same case as `AddSubCancel` but using a deep transformer stack.
-/

abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

-- The following specs partially evaluate the specs for `getThe` and `set` that otherwise would need
-- multiple small substeps in the modular lifting framework. This is good practice for performance
-- sensitive use cases.

@[spec high]
theorem Spec.M_getThe_Nat :
    ⦃fun s₁ s₂ => Q.fst s₂ s₁ s₂⦄ getThe (m := M) Nat ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_set_Nat (n : Nat) :
    ⦃fun s₁ _ => Q.fst ⟨⟩ s₁ n⦄ set (m := M) n ⦃Q⦄ := by
  mvcgen

def step (v : Nat) : M Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

end AddSubCancelDeep
