/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order
public import Std.Internal.Do.Order.Basic
public import Std.Internal.Do.Order.Frame
public import Std.Internal.Do.Order.Lemmas
universe u v w
@[expose] public section

namespace Std.Internal.Do

open Lean.Order

/-!
# Assertion

The `Assertion` class and `Assertion.ofProp` embedding.
-/

/-- An assertion type is equipped with a `CompleteLattice` structure,
used as the carrier for pre- and postconditions. -/
class abbrev Assertion (α : Type w) := CompleteLattice α



end Std.Internal.Do
