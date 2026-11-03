module

/-!
Under the module system, the unit-like check of `isDefEq` must not fail when a public structure's
constructor mentions a private declaration that is not visible in the exported environment, e.g.
while generating the injectivity theorems of a public structure wrapping it. The cross-module
variant is tested in `tests/pkg/module`.
-/

def Hidden : Type := Nat

public structure S where
  private mk ::
  private x : Hidden

public structure Foo where
  s : S

def HiddenUnit : Type := Unit

public structure U where
  private mk ::
  private x : HiddenUnit

public structure Bar where
  u : U

/-! In a private context, `HiddenUnit` is visible and `U` is unit-like. -/

example (a b : U) : a = b := rfl
