import Lean
import Std.Tactic.Do
/-!
Port of `Sym/Cases/GetThrowSet` to the new meta theory.

Exception handling with `ExceptT String <| StateM Nat`: each `step` conditionally throws and
otherwise increments the state by one. With the loop driving the state up from `0` the guard
never fires, so the program never throws and ends at state `n`.
-/

open Lean Meta Order Std.Internal.Do

set_option mvcgen.warning false

namespace GetThrowSet

abbrev M := ExceptT String <| StateM Nat

@[spec high] theorem spec_throw (e : String) {post : α → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (epost.head e) (throw (m := M) e) post epost := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_set (x : Nat) :
    ⦃fun _ => post ⟨⟩ x⦄ (set (m := M) x) ⦃post⦄ := by
  mvcgen'

@[spec high] theorem spec_get :
    ⦃fun s => post s s⦄ (get (m := M)) ⦃post⦄ := by
  mvcgen'

def step (lim : Nat) : M Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ⦃fun s => s = 0⦄ loop n ⦃fun _ s => s = n⦄

end GetThrowSet
