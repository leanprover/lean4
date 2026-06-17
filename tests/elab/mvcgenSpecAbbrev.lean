import Std.Internal.Do
import Std.Tactic.Do

/-!
Tests that `mvcgen` and `mvcgen'` apply a `@[spec]` theorem whose *type* is a
reducible abbreviation wrapping a Hoare triple, e.g. `abbrev foo.spec := ⦃P⦄ foo ⦃Q⦄`.
The triple is recovered from the proof's type and must be reduced through the
abbreviation before it is recognized as a `Triple`.
-/

set_option mvcgen.warning false

/-! `mvcgen` over a legacy `Std.Do` triple. `foo` is `irreducible`, so the
postcondition `r = 1` can only be discharged via the registered spec (`r = 0`). -/
section
open Std.Do

@[irreducible] def foo : Id Nat := pure 0

abbrev foo.spec := ⦃⌜True⌝⦄ foo ⦃⇓r => ⌜r = 0⌝⦄

@[spec] theorem foo.spec.proof : foo.spec := by
  unfold foo.spec foo; mvcgen <;> grind

example :
    ⦃⌜True⌝⦄
    do let x ← foo; pure (x + 1)
    ⦃⇓r => ⌜r = 1⌝⦄ := by
  mvcgen <;> grind

end

/-! `mvcgen'` over a new-metatheory `Std.Internal.Do` triple. `G` is an `axiom`,
so discharging `wp⟦G⟧` requires the registered spec. -/
section
open Std.Internal.Do Lean.Order
set_option warn.sorry false

axiom G : StateM Nat Unit

abbrev G.spec := ⦃fun (_ : Nat) => True⦄ G ⦃fun _ n => n = n⦄

@[spec] axiom G.spec.proof : G.spec

example : ⦃fun (_ : Nat) => True⦄ G ⦃fun _ n => n = n⦄ := by
  mvcgen'

end
