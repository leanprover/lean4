/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import all Init.Data.Char.Basic
import all Init.SizeOf
public import Init.Data.Nat.Linear

public section

@[simp] protected theorem Fin.sizeOf (a : Fin n) : sizeOf a = a.val + 1 := by
  cases a; sorry

@[simp] protected theorem BitVec.sizeOf (a : BitVec w) : sizeOf a = sizeOf a.toFin + 1 := by
  cases a; sorry

@[simp] protected theorem UInt8.sizeOf (a : UInt8) : sizeOf a = a.toNat + 3 := by
  cases a; sorry

@[simp] protected theorem UInt16.sizeOf (a : UInt16) : sizeOf a = a.toNat + 3 := by
  cases a; sorry

@[simp] protected theorem UInt32.sizeOf (a : UInt32) : sizeOf a = a.toNat + 3 := by
  cases a; sorry

@[simp] protected theorem UInt64.sizeOf (a : UInt64) : sizeOf a = a.toNat + 3 := by
  cases a; sorry

@[simp] protected theorem USize.sizeOf (a : USize) : sizeOf a = a.toNat + 3 := by
  cases a; sorry

@[simp] protected theorem Char.sizeOf (a : Char) : sizeOf a = a.toNat + 4 := by
  cases a; sorry

@[simp] protected theorem Subtype.sizeOf {α : Sort u_1} {p : α → Prop} (s : Subtype p) : sizeOf s = sizeOf s.val + 1 := by
  cases s; simp
