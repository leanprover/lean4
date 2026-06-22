import Lean
import Std.Tactic.Do

/-!
Same loop as `AddSubCancel` but threaded through a deep monad transformer stack.
-/

open Lean Parser Meta Elab Tactic Sym Lean.Order Std.Internal.Do

namespace AddSubCancelDeep

set_option mvcgen.warning false

abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

-- The following specs partially evaluate the specs for `getThe` and `set` that otherwise would need
-- multiple small substeps in the modular lifting framework. This is good practice for performance
-- sensitive use cases.

@[spec high]
theorem Spec.M_getThe_Nat :
    ⦃fun s₁ s₂ => post s₂ s₁ s₂⦄ (getThe (m := M) Nat) ⦃post⦄ := by
  vcgen

@[spec high]
theorem Spec.M_set_Nat (n : Nat) :
    ⦃fun s₁ _ => post ⟨⟩ s₁ n⦄ (set (m := M) n) ⦃post⦄ := by
  vcgen

def step (v : Nat) : M Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃fun _ => post⦄

end AddSubCancelDeep
