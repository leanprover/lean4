/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core

public section

namespace Std.Slice

/--
Wrapper structure for slice types that makes generic slice functions available via dot notation.
The implementation of the functions depends on the type `γ` of the internal representation.

Usually, if `γ` is the internal representation of a slice of some type `α`, then `Slice γ` can be
used directly, but one usually creates an abbreviation `AlphaSlice := Slice γ` and provides
`Self (Slice γ) AlphaSlice` and `Sliceable shape α AlphaSlice` instances. Then `AlphaSlice` can
be worked with without ever thinking of `Slice` and it is possible to extend the API with
`α`/`γ`-specific functions.
-/
structure _root_.Std.Slice (γ : Type u) where
  internalRepresentation : γ

/--
This typeclass determines that some type `α` is equal to `β` and that `β` should be used in APIs
instead of `α`.

`Self` is used in the polymorphic slice library.
-/
class Self (α : Type u) (β : outParam (Type u)) where
  eq : α = β := by rfl

end Std.Slice
