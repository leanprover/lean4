/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
public import Init.Data.Ord.UInt
import Init.Data.UInt.Lemmas

open Std

public instance : Std.LinearOrderPackage UInt8 := .ofLE _ { }
public instance : Std.LinearOrderPackage UInt16 := .ofLE _ { }
public instance : Std.LinearOrderPackage UInt32 := .ofLE _ { }
public instance : Std.LinearOrderPackage UInt64 := .ofLE _ { }
public instance : Std.LinearOrderPackage USize := .ofLE _ { }
