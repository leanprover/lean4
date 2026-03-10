import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace AddSubCancel

set_option mvcgen.warning false

-- The following specs partially evaluate the specs for `get` and `set` that otherwise would need
-- multiple small substeps in the modular lifting framework. This is good practice for performance
-- sensitive use cases.

@[spec high]
theorem Spec.MonadState_get {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  mvcgen'

@[spec high]
theorem Spec.MonadStateOf_set {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond PUnit (.arg σ ps)} {s : σ} :
    ⦃fun _ => Q.fst ⟨⟩ s⦄ set (m := StateT σ m) s ⦃Q⦄ := by
  mvcgen'

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

end AddSubCancel
