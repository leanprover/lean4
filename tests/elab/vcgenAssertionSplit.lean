import Std.WP

set_option sym.debug true

/-!
`vcgen` splits an `ite`/`dite`/`cond`/match in the precondition and on the right-hand side of an
entailment, and it substitutes the equation `x = t` that each alternative of a split carries for a
local `x`. Every example closes with `vcgen` alone.
-/

open Std.WP

set_option experimental.vcgen true

/-- The precondition splits on `o`. Substituting `o = some n` reduces the postcondition. -/
example (o : Option Nat) :
    ⦃ match o with | some n => n > 0 | none => True ⦄
    (pure () : Id Unit)
    ⦃ fun _ => match o with | some n => n > 0 ∧ True | none => True ⦄ := by
  vcgen

/-- The right-hand side `(match o with …) s` splits on `o` with the state argument `s` applied. -/
example (o : Option Nat) :
    ⦃ fun (_ : Nat) => True ⦄
    (pure 0 : StateM Nat Nat)
    ⦃ fun _ => match o with | some n => fun _ => n = n | none => fun _ => True ⦄ := by
  vcgen

/-- The program splits on `o`. Substituting `o = some n` reduces the postcondition. -/
example (o : Option Nat) :
    ⦃ True ⦄
    (match o with | some n => pure n | none => pure 0 : Id Nat)
    ⦃ fun r => match o with | some n => r = n | none => r = 0 ⦄ := by
  vcgen

/-- The right-hand side splits an `ite`. -/
example (b : Bool) :
    ⦃ True ⦄
    (pure 1 : Id Nat)
    ⦃ fun r => if b then r = 1 else r = 1 ⦄ := by
  vcgen
