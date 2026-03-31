import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace AddSubCancelSimp

set_option mvcgen.warning false

-- Same benchmark as `AddSubCancel` but using simp spec equations instead of triple specs
-- for `get` and `set`. This exercises the `reduceSimpSpec` + `replaceTargetEq` code path.

@[spec high]
theorem Spec.MonadState_get {m} [Monad m] {σ} :
    get (m := StateT σ m) = fun s => pure (s, s) := by
  rfl

@[spec high]
theorem Spec.MonadStateOf_set {m} [Monad m] {σ} {s : σ} :
    set (m := StateT σ m) s = fun _ => pure (⟨⟩, s) := by
  rfl

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

end AddSubCancelSimp
