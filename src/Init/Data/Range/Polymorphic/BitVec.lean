/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Lemmas
public import Init.Data.UInt
import Init.Omega

public section

open Std Std.PRange

namespace BitVec

variable {n : Nat}

instance : UpwardEnumerable (BitVec n) where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? m i := if h : i.toNat + m < 2 ^ n then some (.ofNatLT _ h) else none

theorem succ?_eq_none {x : BitVec n} :
    UpwardEnumerable.succ? x = none ↔ x.toNat = 2 ^ n - 1 := by
  simp [succ?, ← BitVec.toNat_inj]
  apply Iff.intro
  · refine fun h => Classical.not_not.mp fun _ => ?_
    simp [Nat.mod_eq_of_lt (a := x.toNat + 1) (b := 2 ^ n) (by omega)] at h
  · have := Nat.two_pow_pos n
    simp +contextual [show 2 ^ n - 1 + 1 = 2 ^ n by omega]

theorem succ?_eq_some {x y : BitVec n} :
    succ? x = some y ↔ x.toNat < 2 ^ n - 1 ∧ y.toNat = x.toNat + 1 := by
  match h : succ? x with
  | none => simp_all [succ?_eq_none]
  | some y' =>
    simp only [Option.some.injEq]
    apply Iff.intro
    · rintro rfl
      have : ¬ succ? x = none := fun _ => by simp_all
      simp only [succ?_eq_none] at this
      simp only [succ?, ofNat_eq_ofNat, Option.ite_none_left_eq_some, Option.some.injEq] at h
      apply And.intro
      · omega
      · simp only [← toNat_inj, toNat_add, toNat_ofNat, Nat.add_mod_mod, Nat.zero_mod] at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        exact h.2.symm
    · simp only [succ?, ofNat_eq_ofNat, ← toNat_inj, toNat_add, toNat_ofNat, Nat.add_mod_mod,
        Nat.zero_mod, Option.ite_none_left_eq_some, Option.some.injEq] at h
      intro h'
      rw [Nat.mod_eq_of_lt (by omega)] at h
      simp [← BitVec.toNat_inj, *]

instance : LawfulUpwardEnumerable (BitVec n) where
  ne_of_lt := by
    simp +contextual [UpwardEnumerable.LT, ← BitVec.toNat_inj, succMany?] at ⊢
    omega
  succMany?_zero := by simp [UpwardEnumerable.succMany?, BitVec.toNat_lt_twoPow_of_le]
  succMany?_add_one a b := by
    simp +contextual [← BitVec.toNat_inj, succMany?, succ?]
    split <;> split
    · rename_i h
      simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt (a := b.toNat + a + 1) ‹_›]
      all_goals omega
    · omega
    · have : b.toNat + a + 1 = 2 ^ n := by omega
      simp [this]
    · simp

instance : LawfulUpwardEnumerableLE (BitVec n) where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, BitVec.le_def]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro <;> simp [Nat.add_sub_cancel' hle, BitVec.toNat_lt_twoPow_of_le]
    · rintro ⟨n, hn, rfl⟩
      simp [BitVec.ofNatLT]

instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance

instance : Rxc.HasSize (BitVec n) where
  size lo hi := hi.toNat + 1 - lo.toNat

instance : Rxc.LawfulHasSize (BitVec n) where
  size_eq_zero_of_not_le bound x := by
    simp only [BitVec.not_le, Rxc.HasSize.size, BitVec.lt_def]
    omega
  size_eq_one_of_succ?_eq_none lo hi := by
    have := BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _) (x := hi)
    simp only [succ?_eq_none, Rxc.HasSize.size, BitVec.le_def]
    omega
  size_eq_succ_of_succ?_eq_some lo hi x := by
    simp only [succ?_eq_some, Rxc.HasSize.size, BitVec.le_def]
    omega

instance : Rxc.IsAlwaysFinite (BitVec n) := inferInstance

instance : Rxo.HasSize (BitVec n) := .ofClosed
instance : Rxo.LawfulHasSize (BitVec n) := inferInstance
instance : Rxo.IsAlwaysFinite (BitVec n) := inferInstance

instance : Rxi.HasSize (BitVec n) where
  size lo := 2 ^ n - lo.toNat

instance : Rxi.LawfulHasSize (BitVec n) where
  size_eq_one_of_succ?_eq_none x := by
    simp only [succ?_eq_none, Rxi.HasSize.size]
    omega
  size_eq_succ_of_succ?_eq_some lo lo' := by
    simp only [succ?_eq_some, Rxi.HasSize.size]
    omega

instance : Rxi.IsAlwaysFinite (BitVec n) := inferInstance

namespace Signed

@[expose]
def rotate (x : BitVec n) : BitVec n := x + ↑(2 ^ (n - 1) : Nat)

theorem rotate_rotate {x : BitVec n} :
    rotate (rotate x) = x := by
  match n with
  | 0 => simp [eq_nil x, rotate]
  | n + 1 =>
    simp only [rotate, BitVec.add_assoc]
    simp [← BitVec.toNat_inj, ← Nat.two_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by omega]

theorem rotate_map_eq_iff {x y : Option (BitVec n)} :
    rotate <$> x = y ↔ x = rotate <$> y := by
  suffices h : ∀ x y : Option (BitVec n), rotate <$> x = y → x = rotate <$> y by
    exact ⟨h x y, fun h' => (h y x h'.symm).symm⟩
  intro x y h
  replace h := congrArg (rotate <$> ·) h
  simpa [Function.comp_def, rotate_rotate] using h

scoped instance instUpwardEnumerable : UpwardEnumerable (BitVec n) where
  succ? x := rotate <$> UpwardEnumerable.succ? (rotate x)
  succMany? n x := rotate <$> UpwardEnumerable.succMany? n (rotate x)

theorem succ?_rotate {x : BitVec n} :
    succ? (rotate x) = (haveI := BitVec.instUpwardEnumerable (n := n); rotate <$> succ? x) := by
  simp [succ?, rotate_rotate]

theorem succMany?_rotate {x : BitVec n} :
    succMany? m (rotate x) =
      (haveI := BitVec.instUpwardEnumerable (n := n); rotate <$> succMany? m x) := by
  simp [succMany?, rotate_rotate]

theorem sle_iff_rotate_le_rotate {x y : BitVec n} :
    x.sle y ↔ rotate x ≤ rotate y := by
  match n with
  | 0 => simp [eq_nil x, eq_nil y]
  | n + 1 =>
    simp [BitVec.sle_iff_toInt_le, BitVec.toInt, Nat.pow_add, Nat.mul_comm _ 2, rotate, BitVec.le_def]
    split <;> split
    · simp only [Int.ofNat_le]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : (↑y.toNat : Int) - 2 * 2 ^ n < 0 := by
        have := BitVec.toNat_lt_twoPow_of_le (x := y) (Nat.le_refl _)
        simp [Nat.pow_add, Nat.mul_comm _ 2] at this
        simp only [← Int.ofNat_lt, Int.natCast_mul, Int.cast_ofNat_Int, Int.natCast_pow] at this
        omega
      have : ¬ (↑x.toNat ≤ (↑y.toNat : Int) - 2 * 2 ^ n) := by
        apply Int.not_le_of_gt
        calc _ < 0 := this
             _ ≤ _ := by omega
      simp [this]
      rw [Nat.mod_eq_mod_iff (x := y.toNat + 2 ^ n) (y := y.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr]
      rotate_left
      · exact ⟨0, 1, by omega⟩
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : (↑x.toNat : Int) - 2 * 2 ^ n ≤ ↑y.toNat := by
        have : x.toNat < 2 * 2 ^ n := by omega
        have : (↑x.toNat : Int) < 2 * 2 ^ n := by simpa [← Int.ofNat_lt] using this
        omega
      simp [this]
      rw [Nat.mod_eq_mod_iff (x := x.toNat + 2 ^ n) (y := x.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr]
      rotate_left
      · exact ⟨0, 1, by omega⟩
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp
      rw [Nat.mod_eq_mod_iff (x := x.toNat + 2 ^ n) (y := x.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr ⟨0, 1, by omega⟩,
        Nat.mod_eq_mod_iff (x := y.toNat + 2 ^ n) (y := y.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr ⟨0, 1, by omega⟩,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem rotate_inj {x y : BitVec n} :
    rotate x = rotate y ↔ x = y := by
  apply Iff.intro
  · intro h
    simpa [rotate_rotate] using congrArg rotate h
  · intro h
    exact congrArg rotate h

theorem toInt_eq_ofNat_toNat_rotate_sub {x : BitVec n} (h : n > 0) :
    x.toInt = (↑(rotate x).toNat : Int) - 2 ^ (n - 1) := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp [BitVec.toInt, rotate]
    have : (2 : Int) ^ n > 0 := Int.pow_pos (by omega)
    split <;> rename_i h
    · rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2, Nat.mul_lt_mul_left (by omega),
        ← Int.ofNat_lt, Int.natCast_pow, Int.cast_ofNat_Int] at h
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2, Nat.mul_lt_mul_left (by omega),
        ← Int.ofNat_lt, Int.natCast_pow, Int.cast_ofNat_Int] at h
      simp [Int.pow_add, Int.mul_comm _ 2, Int.two_mul, ← Int.sub_sub]
      rw [eq_comm, Int.emod_eq_iff (by omega)]
      refine ⟨by omega, ?_, ?_⟩
      · have := BitVec.toNat_lt_twoPow_of_le (x := x) (Nat.le_refl _)
        rw [Int.ofNat_natAbs_of_nonneg (by omega)]
        simp only [Nat.pow_add, Nat.pow_one, ← Int.ofNat_lt, Int.natCast_mul, Int.natCast_pow,
          Int.cast_ofNat_Int] at this
        omega
      · conv => rhs; rw [← Int.sub_sub, Int.sub_sub (b := 2 ^ n), Int.add_comm, ← Int.sub_sub]
        exact ⟨-1, by omega⟩

scoped instance instLE : LE (BitVec n) where
  le x y := x.sle y

scoped instance : DecidableLE (BitVec n) := fun x y => inferInstanceAs (Decidable <| x.sle y)

scoped instance instLT : LT (BitVec n) where
  lt x y := x.slt y

scoped instance : DecidableLT (BitVec n) := fun x y => inferInstanceAs (Decidable <| x.slt y)

scoped instance : LawfulOrderLT (BitVec n) where
  lt_iff x y := by
    simp only [LE.le, LT.lt]
    simpa [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le] using Int.le_of_lt

scoped instance : IsPartialOrder (BitVec n) where
  le_refl x := by simp only [LE.le]; simp [BitVec.sle_iff_toInt_le]
  le_trans := by
    simp only [LE.le]
    simpa [BitVec.sle_iff_toInt_le] using fun _ _ _ => Int.le_trans
  le_antisymm := by
    simp only [LE.le, ← BitVec.toInt_inj]
    simpa [BitVec.sle_iff_toInt_le] using fun _ _ => Int.le_antisymm

scoped instance : LawfulUpwardEnumerableLE (BitVec n) where
  le_iff x y := by
    rw [← rotate_rotate (x := x), ← rotate_rotate (x := y)]
    generalize (rotate x) = x
    generalize (rotate y) = y
    simp only [LE.le]
    rw [sle_iff_rotate_le_rotate]
    letI := BitVec.instUpwardEnumerable (n := n)
    letI := instLEBitVec (w := n)
    simp [UpwardEnumerable.le_iff, rotate_rotate, UpwardEnumerable.le_iff_exists,
      succMany?_rotate, rotate_inj]

scoped instance :
    LawfulUpwardEnumerable (BitVec n) where
  ne_of_lt x y h := by
    rw [← rotate_rotate (x := x), ← rotate_rotate (x := y)] at h ⊢
    generalize rotate x = x at h ⊢
    generalize rotate y = y at h ⊢
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    have : x ≠ y := by
      apply UpwardEnumerable.ne_of_lt
      obtain ⟨n, hn⟩ := h
      refine ⟨n, ?_⟩
      rwa [succMany?_rotate, rotate_map_eq_iff, Option.map_eq_map, Option.map_some, rotate_rotate] at hn
    apply this.imp; intro heq
    simpa [rotate_rotate] using congrArg rotate heq
  succMany?_zero x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    simp [succMany?_rotate, succMany?_zero]
  succMany?_add_one m x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    simp [succMany?_rotate, succMany?_add_one, Option.bind_map, Function.comp_def, succ?_rotate]

scoped instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance
scoped instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance

scoped instance : Rxc.HasSize (BitVec n) where
  size lo hi :=
    haveI := BitVec.instHasSize (n := n)
    Rxc.HasSize.size (rotate lo) (rotate hi)

scoped instance : Rxc.LawfulHasSize (BitVec n) where
  size_eq_zero_of_not_le bound x := by
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil x, eq_nil bound]
    | n + 1 =>
      simp [BitVec.sle_iff_toInt_le, Rxc.HasSize.size,
        toInt_eq_ofNat_toNat_rotate_sub (show n + 1 > 0 by omega)]
      omega
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← rotate_rotate (x := lo)]
    generalize rotate lo = lo
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil lo, eq_nil hi, succ?, rotate, Rxc.HasSize.size]
    | n + 1 =>
      simp [BitVec.sle_iff_toInt_le, toInt_eq_ofNat_toNat_rotate_sub,
        Rxc.HasSize.size, rotate_rotate, succ?_rotate, Option.map_eq_map, Option.map_eq_none_iff,
        succ?_eq_none]
      omega
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← rotate_rotate (x := lo)]
    generalize rotate lo = lo
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil lo, eq_nil hi, succ?, rotate, Rxc.HasSize.size]
    | n + 1 =>
      simp [BitVec.sle_iff_toInt_le, toInt_eq_ofNat_toNat_rotate_sub,
        Rxc.HasSize.size, rotate_rotate, succ?_rotate, succ?_eq_some]
      rintro h y h' hy rfl
      simp only [rotate_rotate]
      omega

scoped instance : Rxc.IsAlwaysFinite (BitVec n) := inferInstance

scoped instance : Rxo.HasSize (BitVec n) := .ofClosed
scoped instance : Rxo.LawfulHasSize (BitVec n) := .of_closed
scoped instance : Rxo.IsAlwaysFinite (BitVec n) := inferInstance

scoped instance : Rxi.HasSize (BitVec n) where
  size lo := 2 ^ n - (rotate lo).toNat

scoped instance : Rxi.LawfulHasSize (BitVec n) where
  size_eq_one_of_succ?_eq_none x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    simp only [succ?_rotate, Option.map_eq_map, Option.map_eq_none_iff, Rxi.HasSize.size,
      rotate_rotate]
    letI := BitVec.instHasSize_2 (n := n)
    exact Rxi.size_eq_one_of_succ?_eq_none x
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← rotate_rotate (x := lo), ← rotate_rotate (x := lo')]
    generalize rotate lo = lo
    generalize rotate lo' = lo'
    simp [succ?_rotate, rotate_inj, instHasSize_2, rotate_rotate]
    letI := BitVec.instHasSize_2 (n := n)
    exact Rxi.size_eq_succ_of_succ?_eq_some lo lo'

scoped instance : Rxi.IsAlwaysFinite (BitVec n) := inferInstance

end Signed

end BitVec
