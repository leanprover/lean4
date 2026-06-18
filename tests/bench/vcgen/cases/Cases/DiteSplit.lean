import Lean
import Std.Tactic.Do

/-!
Dependent if-then-else (`if h : cond then ...`) inside an `ExceptT String <| StateM Nat`
program. The add/sub around the guarded `throw` keeps the state unchanged on the success path.
-/

open Lean Meta Order Std.Internal.Do

namespace DiteSplit

set_option mvcgen.warning false

abbrev M := ExceptT String <| StateM Nat

@[spec high] theorem spec_throw (e : String) {post : α → Nat → Prop} :
    ⦃epost e⦄ (throw (m := M) e) ⦃post; epost⟨epost⟩⦄ := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_set (x : Nat) {post : PUnit → Nat → Prop} :
    ⦃fun _ => post ⟨⟩ x⦄ (set (m := M) x) ⦃post⦄ := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_get (post : Nat → Nat → Prop) :
    ⦃fun s => post s s⦄ (get (m := M)) ⦃post⦄ := ⟨PartialOrder.rel_refl⟩

def step (v : Nat) : M Unit := do
  let s ← get
  if _ : s > v then
    throw "s is too large"
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ⦃fun s => s = 0⦄ loop n ⦃fun _ s => s = 0⦄

end DiteSplit
