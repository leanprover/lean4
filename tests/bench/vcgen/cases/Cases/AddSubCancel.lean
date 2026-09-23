import Lean
import Std.Tactic.WP

/-!
Basic add/sub loop in `StateM`: each `step` adds then subtracts the same value, so the
loop preserves the state. Exercises the `get`/`set` `StateT` specs in the simplest setting.
-/

open Lean Meta Order Std.WP

namespace AddSubCancel

set_option experimental.vcgen true

-- The following specs partially evaluate the specs for `get` and `set` that otherwise would need
-- multiple small substeps in the modular lifting framework. This is good practice for performance
-- sensitive use cases.

@[spec high] theorem spec_get_StateT {m : Type u → Type v} {Pred EPosts : Type u}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]
    {σ : Type u} (post : σ → σ → Pred) (eposts : EPosts) :
    ⦃ fun s => post s s ⦄ (get : StateT σ m σ) ⦃ post; eposts ⦄ := by
  vcgen

@[spec high] theorem spec_set_StateT' {m : Type u → Type v} {Pred EPosts : Type u}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]
    {σ : Type u} (s : σ) (post : PUnit → σ → Pred) (eposts : EPosts) :
    ⦃ fun _ => post ⟨⟩ s ⦄ (set s : StateT σ m PUnit) ⦃ post; eposts ⦄ := by
  vcgen

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃fun _ => post⦄

end AddSubCancel
