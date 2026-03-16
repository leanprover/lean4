import Std.Tactic.Do
open Std.Do

/-!
Test for performing E-matching on theorems that contain universe parameters
not referenced by any regular parameter.
-/

example (c : (SPred.pure False : SPred []).down) : False := by
  grind

opaque foo {α : Type u} {β : Type v} (a : α) (b : β) : Nat

@[grind] theorem fooEq (a : Nat) :
    foo.{0, v} (β := List (Sort v)) a [] = foo.{0, w} (β := List (Sort w)) a [] :=
  sorry

example
    (_ : foo 1 ([] : List (Sort v)) = 1)
    (_ : foo 2 ([] : List (Sort w)) ≠ foo 2 ([] : List (Sort w')))
    (_ : foo 3 ([] : List (Sort u)) = 3)
    : False := by
  grind

opaque boo (x : False) : Prop

theorem aux (_ : foo 2 ([] : List (Sort w)) ≠ foo 2 ([] : List (Sort w'))) (_ : boo (by grind)) : True := by
  grind
