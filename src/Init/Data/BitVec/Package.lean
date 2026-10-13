/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
import Init.Data.BitVec.Lemmas

open Std

namespace BitVec

public instance : LinearOrderPackage (BitVec w) := .ofLE _ { }

end BitVec
