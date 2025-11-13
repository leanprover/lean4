/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

prelude
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Lemmas

public section

namespace Std.PRange.Int

@[simp]
theorem size_rco {a b : Int}:
    (a...b).size = (b - a).toNat := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[simp]
theorem size_rcc {a b : Int} :
    (a...=b).size = (b + 1 - a).toNat := by
  simp [Rcc.size, Rxc.HasSize.size]

@[simp]
theorem size_roc {a b : Int} :
    (a<...=b).size = (b - a).toNat := by
  simp only [Roc.size, Rxc.HasSize.size]
  omega

@[simp]
theorem size_roo {a b : Int} :
    (a<...b).size = (b - a - 1).toNat := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

end Std.PRange.Int
