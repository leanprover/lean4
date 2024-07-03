/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.AssocList.Basic

/-!
# Definition of `DHashMap.Raw`

This file defines the type `Std.Data.DHashMap.Raw`. All of its functions are defined in the module
`Std.Data.DHashMap.Basic`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.DHashMap

/-- Dependent hash maps without bundled well-formedness invariant. Suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. -/
structure Raw (α : Type u) (β : α → Type v) where
  /-- The number of mappings present in the hash map -/
  size : Nat
  /-- Internal implementation detail of the hash map -/
  buckets : Array (DHashMap.Internal.AssocList α β)

end Std.DHashMap
