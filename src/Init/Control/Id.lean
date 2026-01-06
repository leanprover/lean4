/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity Monad.
-/
module

prelude
public import Init.Core
public import Init.Control.MonadAttach

public section

universe u

/--
The identity function on types, used primarily for its `Monad` instance.

The identity monad is useful together with monad transformers to construct monads for particular
purposes. Additionally, it can be used with `do`-notation in order to use control structures such as
local mutability, `for`-loops, and early returns in code that does not otherwise use monads.

Examples:
```lean example
def containsFive (xs : List Nat) : Bool := Id.run do
  for x in xs do
    if x == 5 then return true
  return false
```

```lean example
#eval containsFive [1, 3, 5, 7]
```
```output
true
```
-/
@[expose] def Id (type : Type u) : Type u := type

namespace Id

@[always_inline]
instance : Monad Id where
  pure x := x
  bind x f := f x
  map f x := f x

/--
The identity monad has a `bind` operator.
-/
def hasBind : Bind Id :=
  inferInstance

/--
Runs a computation in the identity monad.

This function is the identity function. Because its parameter has type `Id α`, it causes
`do`-notation in its arguments to use the `Monad Id` instance.
-/
@[always_inline, inline, expose]
protected def run (x : Id α) : α := x

instance [OfNat α n] : OfNat (Id α) n :=
  inferInstanceAs (OfNat α n)

instance {m : Type u → Type v} [Pure m] : MonadLiftT Id m where
  monadLift x := pure x.run

instance : MonadAttach Id where
  CanReturn x a := x.run = a
  attach x := pure ⟨x.run, rfl⟩

instance : LawfulMonadAttach Id where
  map_attach := rfl
  canReturn_map_imp := by
    intro _ _ x _ h
    cases h
    exact x.run.2

end Id
