/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

constant OpaquePackagePointed : PointedType.{0}

/-- Opaque reference to a `Package` used for forward declaration. -/
def OpaquePackage : Type := OpaquePackagePointed.type
