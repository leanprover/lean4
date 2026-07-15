-- Tests that `deriving` instances inside a `meta section` are properly marked `meta`.
-- Regression test for https://github.com/leanprover/lean4/pull/13043

module

public meta import Lean.Elab.Command

public meta section

namespace Test

open Lean

@[expose] def Foo := Unit
deriving Inhabited

@[expose] def Bar := Name
deriving Inhabited

end Test
