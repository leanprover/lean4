-- Tests that `wrapInstance` auxiliary definitions work correctly
-- when used inside a `meta` section, for both `inferInstanceAs` and `deriving`.

module

public meta import Lean.Elab.Command

public meta section

namespace Test

open Lean

-- `@[expose]` forces `wrapInstance` to create aux wrapper definitions,
-- which is where the meta marking matters.
@[expose] def Foo := Unit
deriving Inhabited

@[expose] def Bar := Name
deriving Inhabited

@[expose] def Baz := List Nat
instance : EmptyCollection Baz := inferInstanceAs (EmptyCollection (List Nat))

end Test
