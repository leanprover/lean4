import Lean
import Std.Tactic.Do

/-!
Same add/sub loop as `AddSubCancel` but with a pure `let offset := ...` binding inside `step`.
Exercises the handling of pure `letE` nodes in the elaborated program (let-hoist / let-intro).
-/

open Lean Meta Order Std.Internal.Do

namespace LetBinding

set_option mvcgen.warning false

-- Partially evaluated specs for best performance.

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
