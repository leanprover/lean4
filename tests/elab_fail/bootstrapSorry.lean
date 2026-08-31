module

prelude
import Init.Prelude

/-! Trying to generate a `sorry` should not itself lead to errors in bootstrapping contexts. -/

public abbrev Foo := Nat
