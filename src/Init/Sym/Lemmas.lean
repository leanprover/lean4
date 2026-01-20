/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Int.Basic
public import Init.Data.UInt.Basic
public import Init.Data.SInt.Basic
public section
namespace Lean.Sym

theorem ne_self (a : α) : (a ≠ a) = False := by simp
theorem not_true_eq : (¬ True) = False := by simp
theorem not_false_eq : (¬ False) = True := by simp

theorem ite_cond_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a b : α)
    (c' : Prop) {inst' : Decidable c'} (h : c = c') : @ite α c inst a b = @ite α c' inst' a b := by
  simp [*]

theorem dite_cond_congr {α : Sort u} (c : Prop) {inst : Decidable c} (a : c → α) (b : ¬ c → α)
    (c' : Prop) {inst' : Decidable c'} (h : c = c')
    : @dite α c inst a b = @dite α c' inst' (fun h' => a (h.mpr_prop h')) (fun h' => b (h.mpr_not h')) := by
  simp [*]

theorem cond_cond_eq_true {α : Sort u} (c : Bool) (a b : α) (h : c = true) : cond c a b = a := by
  simp [*]

theorem cond_cond_eq_false {α : Sort u} (c : Bool) (a b : α) (h : c = false) : cond c a b = b := by
  simp [*]

theorem cond_cond_congr {α : Sort u} (c : Bool) (a b : α) (c' : Bool) (h : c = c') : cond c a b = cond c' a b := by
  simp [*]

theorem Nat.lt_eq_true (a b : Nat) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int.lt_eq_true (a b : Int) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Rat.lt_eq_true (a b : Rat) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int8.lt_eq_true (a b : Int8) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int16.lt_eq_true (a b : Int16) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int32.lt_eq_true (a b : Int32) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Int64.lt_eq_true (a b : Int64) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt8.lt_eq_true (a b : UInt8) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt16.lt_eq_true (a b : UInt16) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt32.lt_eq_true (a b : UInt32) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem UInt64.lt_eq_true (a b : UInt64) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Fin.lt_eq_true (a b : Fin n) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem BitVec.lt_eq_true (a b : BitVec n) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem String.lt_eq_true (a b : String) (h : decide (a < b) = true) : (a < b) = True := by simp_all
theorem Char.lt_eq_true (a b : Char) (h : decide (a < b) = true) : (a < b) = True := by simp_all

theorem Nat.lt_eq_false (a b : Nat) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int.lt_eq_false (a b : Int) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Rat.lt_eq_false (a b : Rat) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int8.lt_eq_false (a b : Int8) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int16.lt_eq_false (a b : Int16) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int32.lt_eq_false (a b : Int32) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Int64.lt_eq_false (a b : Int64) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt8.lt_eq_false (a b : UInt8) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt16.lt_eq_false (a b : UInt16) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt32.lt_eq_false (a b : UInt32) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem UInt64.lt_eq_false (a b : UInt64) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Fin.lt_eq_false (a b : Fin n) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem BitVec.lt_eq_false (a b : BitVec n) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem String.lt_eq_false (a b : String) (h : decide (a < b) = false) : (a < b) = False := by simp_all
theorem Char.lt_eq_false (a b : Char) (h : decide (a < b) = false) : (a < b) = False := by simp_all

theorem Nat.le_eq_true (a b : Nat) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int.le_eq_true (a b : Int) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Rat.le_eq_true (a b : Rat) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int8.le_eq_true (a b : Int8) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int16.le_eq_true (a b : Int16) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int32.le_eq_true (a b : Int32) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Int64.le_eq_true (a b : Int64) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt8.le_eq_true (a b : UInt8) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt16.le_eq_true (a b : UInt16) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt32.le_eq_true (a b : UInt32) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem UInt64.le_eq_true (a b : UInt64) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Fin.le_eq_true (a b : Fin n) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem BitVec.le_eq_true (a b : BitVec n) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem String.le_eq_true (a b : String) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all
theorem Char.le_eq_true (a b : Char) (h : decide (a ≤ b) = true) : (a ≤ b) = True := by simp_all

theorem Nat.le_eq_false (a b : Nat) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int.le_eq_false (a b : Int) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Rat.le_eq_false (a b : Rat) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int8.le_eq_false (a b : Int8) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int16.le_eq_false (a b : Int16) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int32.le_eq_false (a b : Int32) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Int64.le_eq_false (a b : Int64) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt8.le_eq_false (a b : UInt8) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt16.le_eq_false (a b : UInt16) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt32.le_eq_false (a b : UInt32) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem UInt64.le_eq_false (a b : UInt64) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Fin.le_eq_false (a b : Fin n) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem BitVec.le_eq_false (a b : BitVec n) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem String.le_eq_false (a b : String) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all
theorem Char.le_eq_false (a b : Char) (h : decide (a ≤ b) = false) : (a ≤ b) = False := by simp_all

theorem Nat.eq_eq_true (a b : Nat) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int.eq_eq_true (a b : Int) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Rat.eq_eq_true (a b : Rat) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int8.eq_eq_true (a b : Int8) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int16.eq_eq_true (a b : Int16) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int32.eq_eq_true (a b : Int32) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Int64.eq_eq_true (a b : Int64) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt8.eq_eq_true (a b : UInt8) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt16.eq_eq_true (a b : UInt16) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt32.eq_eq_true (a b : UInt32) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem UInt64.eq_eq_true (a b : UInt64) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Fin.eq_eq_true (a b : Fin n) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem BitVec.eq_eq_true (a b : BitVec n) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem String.eq_eq_true (a b : String) (h : decide (a = b) = true) : (a = b) = True := by simp_all
theorem Char.eq_eq_true (a b : Char) (h : decide (a = b) = true) : (a = b) = True := by simp_all

theorem Nat.eq_eq_false (a b : Nat) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int.eq_eq_false (a b : Int) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Rat.eq_eq_false (a b : Rat) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int8.eq_eq_false (a b : Int8) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int16.eq_eq_false (a b : Int16) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int32.eq_eq_false (a b : Int32) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Int64.eq_eq_false (a b : Int64) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt8.eq_eq_false (a b : UInt8) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt16.eq_eq_false (a b : UInt16) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt32.eq_eq_false (a b : UInt32) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem UInt64.eq_eq_false (a b : UInt64) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Fin.eq_eq_false (a b : Fin n) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem BitVec.eq_eq_false (a b : BitVec n) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem String.eq_eq_false (a b : String) (h : decide (a = b) = false) : (a = b) = False := by simp_all
theorem Char.eq_eq_false (a b : Char) (h : decide (a = b) = false) : (a = b) = False := by simp_all

theorem Nat.dvd_eq_true (a b : Nat) (h : decide (a ∣ b) = true) : (a ∣ b) = True := by simp_all
theorem Int.dvd_eq_true (a b : Int) (h : decide (a ∣ b) = true) : (a ∣ b) = True := by simp_all

theorem Nat.dvd_eq_false (a b : Nat) (h : decide (a ∣ b) = false) : (a ∣ b) = False := by simp_all
theorem Int.dvd_eq_false (a b : Int) (h : decide (a ∣ b) = false) : (a ∣ b) = False := by simp_all

end Lean.Sym
