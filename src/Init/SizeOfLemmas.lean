/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta
import Init.SizeOf
import Init.Data.Nat.Linear

@[simp] protected theorem Fin.sizeOf (a : Fin n) : sizeOf a = a.val + 1 := by
  cases a; simp +arith

@[simp] protected theorem BitVec.sizeOf (a : BitVec w) : sizeOf a = sizeOf a.toFin + 1 := by
  cases a; simp +arith

@[simp] protected theorem UInt8.sizeOf (a : UInt8) : sizeOf a = a.toNat + 3 := by
  cases a; simp +arith [UInt8.toNat, BitVec.toNat]

@[simp] protected theorem UInt16.sizeOf (a : UInt16) : sizeOf a = a.toNat + 3 := by
  cases a; simp +arith [UInt16.toNat, BitVec.toNat]

@[simp] protected theorem UInt32.sizeOf (a : UInt32) : sizeOf a = a.toNat + 3 := by
  cases a; simp +arith [UInt32.toNat, BitVec.toNat]

@[simp] protected theorem UInt64.sizeOf (a : UInt64) : sizeOf a = a.toNat + 3 := by
  cases a; simp +arith [UInt64.toNat, BitVec.toNat]

@[simp] protected theorem USize.sizeOf (a : USize) : sizeOf a = a.toNat + 3 := by
  cases a; simp +arith [USize.toNat, BitVec.toNat]

@[simp] protected theorem Char.sizeOf (a : Char) : sizeOf a = a.toNat + 4 := by
  cases a; simp +arith [Char.toNat]

@[simp] protected theorem Subtype.sizeOf {α : Sort u_1} {p : α → Prop} (s : Subtype p) : sizeOf s = sizeOf s.val + 1 := by
  cases s; simp
