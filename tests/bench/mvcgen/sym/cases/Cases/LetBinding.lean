import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace LetBinding

set_option mvcgen.warning false

-- Partially evaluated specs for best performance.

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
  -- Pure let binding: `let offset := ...` produces a letE node in the elaborated term
  let offset := v + 1
  set (s + offset)
  let s ← get
  set (s - offset)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

end LetBinding
