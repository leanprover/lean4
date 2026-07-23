import Lean
import Std.Tactic.Do

/-!
Basic add/sub loop in `StateM`: each `step` adds then subtracts the same value, so the
loop preserves the state. Exercises the `get`/`set` `StateT` specs in the simplest setting.
-/

open Lean Meta Order Std.Internal.Do

namespace AddSubCancel

set_option mvcgen.warning false

-- The following specs partially evaluate the specs for `get` and `set` that otherwise would need
-- multiple small substeps in the modular lifting framework. This is good practice for performance
-- sensitive use cases.

@[spec high] theorem spec_get_StateT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    ⦃ fun s => post s s ⦄ (get : StateT σ m σ) ⦃ post; epost ⦄ := by
  vcgen

@[spec high] theorem spec_set_StateT' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {σ : Type u} (s : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    ⦃ fun _ => post ⟨⟩ s ⦄ (set s : StateT σ m PUnit) ⦃ post; epost ⦄ := by
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
