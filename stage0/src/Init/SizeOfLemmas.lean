/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta
import Init.SizeOf
import Init.Data.Nat.Linear

@[simp] theorem Fin.sizeOf (a : Fin n) : sizeOf a = a.val + 1 := by
  cases a; simp_arith

@[simp] theorem UInt8.sizeOf (a : UInt8) : sizeOf a = a.toNat + 2 := by
  cases a; simp_arith [UInt8.toNat]

@[simp] theorem UInt16.sizeOf (a : UInt16) : sizeOf a = a.toNat + 2 := by
  cases a; simp_arith [UInt16.toNat]

@[simp] theorem UInt32.sizeOf (a : UInt32) : sizeOf a = a.toNat + 2 := by
  cases a; simp_arith [UInt32.toNat]

@[simp] theorem UInt64.sizeOf (a : UInt64) : sizeOf a = a.toNat + 2 := by
  cases a; simp_arith [UInt64.toNat]

@[simp] theorem USize.sizeOf (a : USize) : sizeOf a = a.toNat + 2 := by
  cases a; simp_arith [USize.toNat]

@[simp] theorem Char.sizeOf (a : Char) : sizeOf a = a.toNat + 3 := by
  cases a; simp_arith [Char.toNat]

@[simp] theorem Subtype.sizeOf {α : Sort u_1} {p : α → Prop} (s : Subtype p) : sizeOf s = sizeOf s.val + 1 := by
  cases s; simp_arith
