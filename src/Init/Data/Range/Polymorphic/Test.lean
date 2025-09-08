/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core
import Init.Data.Order.Lemmas2

public section

open Std

instance : Total (α := Nat) (· ≤ ·) := inferInstance
