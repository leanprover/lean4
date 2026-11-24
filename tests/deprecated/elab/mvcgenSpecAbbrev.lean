import Std.Tactic.Do

set_option sym.debug true

/-!
Tests that the deprecated `mvcgen` tactic applies a `@[spec]` theorem whose *type* is a reducible
abbreviation wrapping a `Std.Do` Hoare triple, e.g. `abbrev foo.spec := ⦃P⦄ foo ⦃Q⦄`.
`foo` is `irreducible`, so the postcondition `r = 1` can only be discharged via the registered spec
(`r = 0`). The `vcgen` version of this test is `tests/elab/vcgenSpecAbbrev.lean`.
-/

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
