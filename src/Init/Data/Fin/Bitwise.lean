/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Nat.Bitwise
public import Init.Data.Fin.Basic

public section

namespace Fin

@[simp] theorem and_val (a b : Fin n) : (a &&& b).val = a.val &&& b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

@[simp] theorem or_val_of_two_pow {w} (a b : Fin (2 ^ w)) : (a ||| b).val = a.val ||| b.val :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)

@[simp] theorem or_val_of_uInt8Size (a b : Fin UInt8.size) : (a ||| b).val = a.val ||| b.val := or_val_of_two_pow (w := 8) a b
@[simp] theorem or_val_of_uInt16Size (a b : Fin UInt16.size) : (a ||| b).val = a.val ||| b.val := or_val_of_two_pow (w := 16) a b
@[simp] theorem or_val_of_uInt32Size (a b : Fin UInt32.size) : (a ||| b).val = a.val ||| b.val := or_val_of_two_pow (w := 32) a b
@[simp] theorem or_val_of_uInt64Size (a b : Fin UInt64.size) : (a ||| b).val = a.val ||| b.val := or_val_of_two_pow (w := 64) a b
@[simp] theorem or_val_of_uSizeSize (a b : Fin USize.size) : (a ||| b).val = a.val ||| b.val := or_val_of_two_pow a b

theorem or_val (a b : Fin n) : (a ||| b).val = (a.val ||| b.val) % n := rfl

@[simp] theorem xor_val_of_two_pow {w} (a b : Fin (2 ^ w)) : (a ^^^ b).val = a.val ^^^ b.val :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

@[simp] theorem xor_val_of_uInt8Size (a b : Fin UInt8.size) : (a ^^^ b).val = a.val ^^^ b.val := xor_val_of_two_pow (w := 8) a b
@[simp] theorem xor_val_of_uInt16Size (a b : Fin UInt16.size) : (a ^^^ b).val = a.val ^^^ b.val := xor_val_of_two_pow (w := 16) a b
@[simp] theorem xor_val_of_uInt32Size (a b : Fin UInt32.size) : (a ^^^ b).val = a.val ^^^ b.val := xor_val_of_two_pow (w := 32) a b
@[simp] theorem xor_val_of_uInt64Size (a b : Fin UInt64.size) : (a ^^^ b).val = a.val ^^^ b.val := xor_val_of_two_pow (w := 64) a b
@[simp] theorem xor_val_of_uSizeSize (a b : Fin USize.size) : (a ^^^ b).val = a.val ^^^ b.val := xor_val_of_two_pow a b

theorem xor_val (a b : Fin n) : (a ^^^ b).val = (a.val ^^^ b.val) % n := rfl

@[simp] theorem shiftLeft_val (a b : Fin n) : (a <<< b).val = (a.val <<< b.val) % n := rfl

@[simp] theorem shiftRight_val (a b : Fin n) : (a >>> b).val = a.val >>> b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

end Fin
