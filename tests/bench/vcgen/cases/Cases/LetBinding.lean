import Lean
import Std.WP

/-!
Same add/sub loop as `AddSubCancel` but with a pure `let offset := ...` binding inside `step`.
Exercises the handling of pure `letE` nodes in the elaborated program (let-hoist / let-intro).
-/

open Lean Meta Order Std.WP

namespace LetBinding

set_option experimental.vcgen true

-- Partially evaluated specs for best performance.

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
  -- Pure let binding: `let offset := ...` produces a letE node in the elaborated term
  let offset := v + 1
  set (s + offset)
  let s ← get
  set (s - offset)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃fun _ => post⦄

end LetBinding
