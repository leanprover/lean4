/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
import Init.Data.SInt.Lemmas
import Init.Data.Ord.SInt

open Std

instance : Std.LinearOrderPackage Int8 := .ofLE _ { }
instance : Std.LinearOrderPackage Int16 := .ofLE _ { }
instance : Std.LinearOrderPackage Int32 := .ofLE _ { }
instance : Std.LinearOrderPackage Int64 := .ofLE _ { }
instance : Std.LinearOrderPackage ISize := .ofLE _ { }
