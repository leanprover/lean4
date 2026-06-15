import Lean
import Std.Tactic.Do
/-!
Port of `Sym/Cases/ReaderState` to the new meta theory.

A `ReaderT Nat <| StateM Nat` combination. Each `step` reads the reader `r`, adds it to the
state and then subtracts it again, so the loop preserves both the reader and the state.
Exercises partially-evaluated `read`/`get`/`set` specs for the reader+state stack.
-/

open Lean Meta Order Std.Internal.Do

set_option mvcgen.warning false

namespace ReaderState

abbrev M := ReaderT Nat <| StateM Nat

@[spec high] theorem spec_read (post : Nat → Nat → Nat → Prop) (epost : EPost.Nil) :
    Triple (fun r s => post r r s) (read (m := M)) post epost := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_get (post : Nat → Nat → Nat → Prop) (epost : EPost.Nil) :
    Triple (fun r s => post s r s) (get (m := M)) post epost := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_set (n : Nat) (post : PUnit → Nat → Nat → Prop) (epost : EPost.Nil) :
    Triple (fun r _ => post ⟨⟩ r n) (set (m := M) n) post epost := ⟨PartialOrder.rel_refl⟩

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

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃fun _ => post⦄

end ReaderState
