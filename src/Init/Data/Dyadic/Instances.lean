/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Arnez
-/
module

prelude
public import Init.Data.Dyadic.Basic
public import Init.Grind.Ring.Basic
public import Init.Grind.Ordered.Ring

/-! # Internal `grind` algebra instances for `Dyadic`. -/

open Lean.Grind

namespace Dyadic

instance : AddCommMonoid Dyadic := sorry

instance : AddCommGroup Dyadic := sorry

instance : CommRing Dyadic := sorry

instance : Preorder Dyadic := sorry

instance : OrderedRing Dyadic := sorry

end Dyadic
