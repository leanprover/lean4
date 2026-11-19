import Std.WP

set_option sym.debug true

/-!
Tests that `vcgen` applies a `@[spec]` theorem whose *type* is a
reducible abbreviation wrapping a Hoare triple, e.g. `abbrev foo.spec := ⦃P⦄ foo ⦃Q⦄`.
The triple is recovered from the proof's type and must be reduced through the
abbreviation before it is recognized as a `Triple`.
-/

set_option experimental.vcgen true

/-! `vcgen` over a new-metatheory `Std.WP` triple. `G` is an `axiom`,
so discharging `wp⟦G⟧` requires the registered spec. -/
section
open Std.WP Lean.Order
set_option warn.sorry false

axiom G : StateM Nat Unit

abbrev G.spec := ⦃fun (_ : Nat) => True⦄ G ⦃fun _ n => n = n⦄

@[spec] axiom G.spec.proof : G.spec

example : ⦃fun (_ : Nat) => True⦄ G ⦃fun _ n => n = n⦄ := by
  vcgen

end
