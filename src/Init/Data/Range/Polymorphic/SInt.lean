/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude

public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Lemmas
public import Init.Data.SInt
import Init.Data.Range.Polymorphic.UInt
import all Init.Data.SInt.Basic

import all Init.Data.Range.Polymorphic.Internal.SignedBitVec

open Std Std.PRange

namespace HasModel

open BitVec.Signed

variable {α : Type u} [LE α] [LT α] {β : Type v} [LE β] [LT β]

class _root_.HasModel (α : Type u) [LE α] [LT α] (β : outParam (Type v)) [LE β] [LT β]
    [UpwardEnumerable β] [LawfulUpwardEnumerable β] [LawfulUpwardEnumerableLE β]
    [LawfulUpwardEnumerableLT β] where
  encode : α → β
  decode : β → α
  encode_decode : encode (decode x) = x
  decode_encode : decode (encode x) = x
  le_iff_encode_le : x ≤ y ↔ (encode x) ≤ (encode y)
  lt_iff_encode_lt : x < y ↔ (encode x) < (encode y)

variable [UpwardEnumerable β] [LawfulUpwardEnumerable β] [LawfulUpwardEnumerableLE β]
  [LawfulUpwardEnumerableLT β]

scoped instance instUpwardEnumerable [m : HasModel α β] :
    UpwardEnumerable α where
  succ? a := (succ? (m.encode a)).map m.decode
  succMany? n a := (succMany? n (m.encode a)).map m.decode

theorem succ?_decode [m : HasModel α β] {x : β} :
    UpwardEnumerable.succ? (m.decode x) = (UpwardEnumerable.succ? x).map m.decode := by
  simp [instUpwardEnumerable, HasModel.encode_decode]

theorem succ?_encode [m : HasModel α β] {x : α} :
    UpwardEnumerable.succ? (m.encode x) = (UpwardEnumerable.succ? x).map m.encode := by
  simp [instUpwardEnumerable, Function.comp_def, HasModel.encode_decode]

theorem succMany?_decode [m : HasModel α β] {x : β} :
    UpwardEnumerable.succMany? n' (m.decode x) = (UpwardEnumerable.succMany? n' x).map m.decode := by
  simp [instUpwardEnumerable, HasModel.encode_decode]

theorem succMany?_encode [m : HasModel α β] {x : α} :
    UpwardEnumerable.succMany? n' (m.encode x) = (UpwardEnumerable.succMany? n' x).map m.encode := by
  simp [instUpwardEnumerable, Function.comp_def, HasModel.encode_decode]

theorem eq_of_encode_eq [m : HasModel α β] (x y : α) :
    m.encode x = m.encode y → x = y := by
  intro h
  simpa [m.decode_encode] using congrArg m.decode h

theorem encode_inj [m : HasModel α β] {x y : α} :
    m.encode x = m.encode y ↔ x = y := by
  exact ⟨m.eq_of_encode_eq x y, by simp +contextual⟩

theorem le_iff [m : HasModel α β] {x y : α} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE (m.encode x) (m.encode y) := by
  simp [UpwardEnumerable.le_iff_exists, succMany?_encode, ← Option.map_some,
    Option.map_inj_right eq_of_encode_eq]

theorem lt_iff [m : HasModel α β] {x y : α} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT (m.encode x) (m.encode y) := by
  simp [UpwardEnumerable.lt_iff_exists, succMany?_encode, ← Option.map_some,
    Option.map_inj_right eq_of_encode_eq]

attribute [local instance] HasModel.instUpwardEnumerable
scoped instance instLawfulUpwardEnumerable [m : HasModel α β] :
    LawfulUpwardEnumerable α where
  ne_of_lt x y := by
    rw [m.lt_iff, ne_eq, ← m.encode_inj]
    apply LawfulUpwardEnumerable.ne_of_lt
  succMany?_zero x := by
    rw [← Option.map_inj_right eq_of_encode_eq, ← succMany?_encode, Option.map_some]
    apply LawfulUpwardEnumerable.succMany?_zero
  succMany?_add_one n x := by
    rw [← Option.map_inj_right eq_of_encode_eq, ← succMany?_encode, Option.map_bind,
      Function.comp_def]
    simp only [← succ?_encode]
    rw [← Function.comp_def, ← Option.bind_map, ← succMany?_encode (n' := n),
      LawfulUpwardEnumerable.succMany?_add_one]

scoped instance instLawfulUpwardEnumerableLE [m : HasModel α β] :
    LawfulUpwardEnumerableLE α where
  le_iff x y := by
    rw [m.le_iff_encode_le, m.le_iff]
    apply LawfulUpwardEnumerableLE.le_iff

scoped instance instLawfulUpwardEnumerableLT [m : HasModel α β] :
    LawfulUpwardEnumerableLT α where
  lt_iff x y := by
    rw [m.lt_iff_encode_lt, m.lt_iff]
    apply LawfulUpwardEnumerableLT.lt_iff
instance : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

scoped instance instRxcHasSize [m : HasModel α β] [Rxc.HasSize β] :
    Rxc.HasSize α where
  size lo hi := Rxc.HasSize.size (m.encode lo) (m.encode hi)

scoped instance instRxcLawfulHasSize [m : HasModel α β] [Rxc.HasSize β] [Rxc.LawfulHasSize β] :
    Rxc.LawfulHasSize α where
  size_eq_zero_of_not_le lo hi := by
    simp only [m.le_iff_encode_le, Rxc.HasSize.size]
    apply Rxc.LawfulHasSize.size_eq_zero_of_not_le
  size_eq_one_of_succ?_eq_none lo hi := by
    simp only [m.le_iff_encode_le, Rxc.HasSize.size,
      show succ? lo = none ↔ succ? (m.encode lo) = none by simp [m.succ?_encode]]
    apply Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none
  size_eq_succ_of_succ?_eq_some lo hi x := by
    have : ∀ x, succ? lo = some x ↔ succ? (m.encode lo) = some (m.encode x) := by
      simp [m.succ?_encode, ← Option.map_some, Option.map_inj_right m.eq_of_encode_eq]
    simp only [m.le_iff_encode_le, Rxc.HasSize.size, this]
    apply Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some

scoped instance instRxiHasSize [m : HasModel α β] [Rxi.HasSize β] :
    Rxi.HasSize α where
  size lo := Rxi.HasSize.size (m.encode lo)

scoped instance instRxiLawfulHasSize [m : HasModel α β] [Rxi.HasSize β] [Rxi.LawfulHasSize β] :
    Rxi.LawfulHasSize α where
  size_eq_one_of_succ?_eq_none lo := by
    have : succ? lo = none ↔ succ? (m.encode lo) = none := by simp [m.succ?_encode]
    simp only [this, instRxiHasSize]
    apply Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none
  size_eq_succ_of_succ?_eq_some lo lo' := by
    have : ∀ x, succ? lo = some x ↔ succ? (m.encode lo) = some (m.encode x) := by
      simp [m.succ?_encode, ← Option.map_some, Option.map_inj_right m.eq_of_encode_eq]
    simp only [this, instRxiHasSize]
    apply Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some

section AuxiliaryLemmas

/-!
The following lemmas are stated purely in terms of `BitVec n`. Their assumptions and statements
may seem technical, but they are exactly what is needed in the actual proofs.
-/

theorem succ?_eq_of_technicalCondition {α : Type u} [UpwardEnumerable α] [LE α] [LT α] [m : HasModel α (BitVec n)]
    {x : α}
    (h : ∀ y, succ? x = some y ↔ ¬ m.encode x + 1#n = BitVec.Signed.intMinSealed n ∧ m.encode x + 1#n = m.encode y) :
    succ? x = (haveI := HasModel.instUpwardEnumerable (α := α); succ? x) := by
  ext y
  simp only [UpwardEnumerable.succ?, h]
  rw [← Option.map_inj_right HasModel.eq_of_encode_eq, Option.map_map, Function.comp_def]
  simp [HasModel.encode_decode, ← BitVec.eq_sub_iff_add_eq, rotate_eq_iff,
    ← rotate_neg_eq_intMinSealed_sub, rotate_sub, rotate_rotate]

theorem succMany?_eq {α : Type u} [UpwardEnumerable α] [LE α] [LT α]
    [m : HasModel α (BitVec n)] {x : α} {k} :
    haveI := HasModel.instUpwardEnumerable (α := α)
    succMany? k x = if (m.encode x).toInt + ↑k ≤ (BitVec.Signed.intMaxSealed n).toInt then
      some (m.decode (BitVec.ofInt n ((m.encode x).toInt + ↑k)))
    else
      none := by
  by_cases hn : n > 0; rotate_left
  · cases show n = 0 by omega
    simp [succMany?, BitVec.eq_nil (BitVec.Signed.rotate _), BitVec.eq_nil (.ofInt _ _),
      BitVec.eq_nil (encode _), BitVec.eq_nil (BitVec.Signed.intMaxSealed _)]
  have h : ∀ a b c d : Int, a - b + c ≤ d - b ↔ a + c ≤ d := by omega
  simp [UpwardEnumerable.succMany?, BitVec.ofNatLT_eq_ofNat]
  simp [toInt_eq_ofNat_toNat_rotate_sub hn, rotate_intMaxSealed, h]
  simp only [← Int.natCast_add]
  congr
  · rw [Nat.lt_iff_add_one_le, Int.ofNat_le, Nat.le_sub_iff_add_le]
    exact Nat.pow_pos (Nat.zero_lt_succ _)
  · generalize rotate (HasModel.encode x) = x
    simp only [ofNat_eq_rotate_ofInt_sub, rotate_rotate]
    congr; omega

theorem toNat_toInt_add_one_sub_toInt {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem toNat_two_pow_sub_one_sub_toInt {lo : BitVec n} (h : n > 0) :
    (2 ^ (n - 1) - lo.toInt).toNat = 2 ^ n - (rotate lo).toNat := by
  simp only [toInt_eq_ofNat_toNat_rotate_sub h, intMinSealed_def, BitVec.natCast_eq_ofNat,
    BitVec.toNat_ofNat, Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int]
  rw [Int.emod_eq_of_lt, Int.sub_eq_add_neg, Int.neg_sub, ← Int.add_sub_assoc]; rotate_left
  · exact Int.le_of_lt (Int.pow_pos (by omega))
  · exact Int.pow_lt_pow_of_lt (by omega) (by omega)
  simp [Int.toNat_sub', Int.toNat_pow_of_nonneg,
    show (2 : Int) ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n - 1 + 1) by omega,
    show n - 1 + 1 = n by omega]

end AuxiliaryLemmas

end HasModel

namespace Int8

open BitVec.Signed
open scoped HasModel

@[inline] def minValueSealed := Int8.minValue
@[inline] def maxValueSealed := Int8.maxValue
theorem minValueSealed_def : minValueSealed = Int8.minValue := (rfl)
theorem maxValueSealed_def : maxValueSealed = Int8.maxValue := (rfl)
seal minValueSealed maxValueSealed

theorem toBitVec_minValueSealed_eq_intMinSealed : minValueSealed.toBitVec = BitVec.Signed.intMinSealed 8 := by
  simp [minValueSealed_def, BitVec.Signed.intMinSealed_def]
theorem toBitVec_maxValueSealed_eq_intMaxSealed : maxValueSealed.toBitVec = BitVec.Signed.intMaxSealed 8 := by
  simp [maxValueSealed_def, BitVec.Signed.intMaxSealed_def]

@[no_expose]
public instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = minValueSealed then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ maxValueSealed.toInt then some (.ofIntLE _ (by omega) (maxValueSealed_def ▸ h)) else none

instance : Least? Int8 where
  least? := some Int8.minValue

instance : LawfulUpwardEnumerableLeast? Int8 where
  least?_le x := by
    refine ⟨Int8.minValue, rfl, (x.toInt - Int8.minValue.toInt).toNat, ?_⟩
    simp only [succMany?, toInt_neg, Int8.reduceToInt, Int.neg_neg, Nat.reducePow, Int.reduceBmod,
      Int.sub_neg, Int.ofNat_toNat, ofIntLE_eq_ofInt]
    rw [Int.max_eq_left, Int.add_comm _ 128, ← Int.add_assoc]
    · simp [maxValueSealed_def, toInt_le]
    · have := le_toInt x
      omega

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.succ?_eq_of_technicalCondition
    simp [HasModel.encode, succ?, ← Int8.toBitVec_inj, toBitVec_minValueSealed_eq_intMinSealed]
  · ext
    simp [HasModel.succMany?_eq, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_maxValueSealed_eq_intMaxSealed, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int8 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int8 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

public instance instRxcHasSize : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instRxcHasSize = HasModel.instRxcHasSize := by
  simp only [instRxcHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.toNat_toInt_add_one_sub_toInt (Nat.zero_lt_succ _)]

public instance instRxcLawfulHasSize : Rxc.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
public instance : Rxc.IsAlwaysFinite Int8 := by exact inferInstance

public instance instRxoHasSize : Rxo.HasSize Int8 := .ofClosed
public instance instRxoLawfulHasSize : Rxo.LawfulHasSize Int8 := by exact inferInstance
public instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int8 := by exact inferInstance

public instance instRxiHasSize : Rxi.HasSize Int8 where
  size lo := ((2 : Int) ^ 7 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.toNat_two_pow_sub_one_sub_toInt (show 8 > 0 by omega)]

public instance instRxiLawfulHasSize : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
public instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int8 := by exact inferInstance

end Int8

namespace Int16

open BitVec.Signed
open scoped HasModel

@[inline] def minValueSealed := Int16.minValue
@[inline] def maxValueSealed := Int16.maxValue
theorem minValueSealed_def : minValueSealed = Int16.minValue := (rfl)
theorem maxValueSealed_def : maxValueSealed = Int16.maxValue := (rfl)
seal minValueSealed maxValueSealed

theorem toBitVec_minValueSealed_eq_intMinSealed : minValueSealed.toBitVec = BitVec.Signed.intMinSealed 16 := by
  simp [minValueSealed_def, BitVec.Signed.intMinSealed_def]
theorem toBitVec_maxValueSealed_eq_intMaxSealed : maxValueSealed.toBitVec = BitVec.Signed.intMaxSealed 16 := by
  simp [maxValueSealed_def, BitVec.Signed.intMaxSealed_def]

@[no_expose]
public instance : UpwardEnumerable Int16 where
  succ? i := if i + 1 = minValueSealed then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ maxValueSealed.toInt then some (.ofIntLE _ (by omega) (maxValueSealed_def ▸ h)) else none

instance : Least? Int16 where
  least? := some Int16.minValue

instance : LawfulUpwardEnumerableLeast? Int16 where
  least?_le x := by
    refine ⟨Int16.minValue, rfl, (x.toInt - Int16.minValue.toInt).toNat, ?_⟩
    simp only [succMany?, toInt_neg, Int16.reduceToInt, Int.neg_neg, Nat.reducePow, Int.reduceBmod,
      Int.sub_neg, Int.ofNat_toNat, ofIntLE_eq_ofInt]
    rw [Int.max_eq_left, Int.add_comm _ 32768, ← Int.add_assoc]
    · simp [maxValueSealed_def, toInt_le]
    · have := le_toInt x
      omega

instance : HasModel Int16 (BitVec 16) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int16.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int16.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.succ?_eq_of_technicalCondition
    simp [HasModel.encode, succ?, ← Int16.toBitVec_inj, toBitVec_minValueSealed_eq_intMinSealed]
  · ext
    simp [HasModel.succMany?_eq, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_maxValueSealed_eq_intMaxSealed, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int16 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int16 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

public instance instRxcHasSize : Rxc.HasSize Int16 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instRxcHasSize = HasModel.instRxcHasSize := by
  simp only [instRxcHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.toNat_toInt_add_one_sub_toInt (Nat.zero_lt_succ _)]

public instance instRxcLawfulHasSize : Rxc.LawfulHasSize Int16 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
public instance : Rxc.IsAlwaysFinite Int16 := by exact inferInstance

public instance instRxoHasSize : Rxo.HasSize Int16 := .ofClosed
public instance instRxoLawfulHasSize : Rxo.LawfulHasSize Int16 := by exact inferInstance
public instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int16 := by exact inferInstance

public instance instRxiHasSize : Rxi.HasSize Int16 where
  size lo := ((2 : Int) ^ 15 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.toNat_two_pow_sub_one_sub_toInt (show 16 > 0 by omega)]

public instance instRxiLawfulHasSize : Rxi.LawfulHasSize Int16 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
public instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int16 := by exact inferInstance

end Int16

namespace Int32

open BitVec.Signed
open scoped HasModel

@[inline] def minValueSealed := Int32.minValue
@[inline] def maxValueSealed := Int32.maxValue
theorem minValueSealed_def : minValueSealed = Int32.minValue := (rfl)
theorem maxValueSealed_def : maxValueSealed = Int32.maxValue := (rfl)
seal minValueSealed maxValueSealed

theorem toBitVec_minValueSealed_eq_intMinSealed : minValueSealed.toBitVec = BitVec.Signed.intMinSealed 32 := by
  simp [minValueSealed_def, BitVec.Signed.intMinSealed_def]
theorem toBitVec_maxValueSealed_eq_intMaxSealed : maxValueSealed.toBitVec = BitVec.Signed.intMaxSealed 32 := by
  simp [maxValueSealed_def, BitVec.Signed.intMaxSealed_def]

@[no_expose]
public instance : UpwardEnumerable Int32 where
  succ? i := if i + 1 = minValueSealed then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ maxValueSealed.toInt then some (.ofIntLE _ (by omega) (maxValueSealed_def ▸ h)) else none

instance : Least? Int32 where
  least? := some Int32.minValue

instance : LawfulUpwardEnumerableLeast? Int32 where
  least?_le x := by
    refine ⟨Int32.minValue, rfl, (x.toInt - Int32.minValue.toInt).toNat, ?_⟩
    simp only [succMany?, toInt_neg, Int32.reduceToInt, Int.neg_neg, Nat.reducePow, Int.reduceBmod,
      Int.sub_neg, Int.ofNat_toNat, ofIntLE_eq_ofInt]
    rw [Int.max_eq_left, Int.add_comm _ (OfNat.ofNat _), ← Int.add_assoc]
    · simp [maxValueSealed_def, toInt_le]
    · have := le_toInt x
      omega

instance : HasModel Int32 (BitVec 32) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int32.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int32.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.succ?_eq_of_technicalCondition
    simp [HasModel.encode, succ?, ← Int32.toBitVec_inj, toBitVec_minValueSealed_eq_intMinSealed]
  · ext
    simp [HasModel.succMany?_eq, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_maxValueSealed_eq_intMaxSealed, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int32 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int32 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

public instance instRxcHasSize : Rxc.HasSize Int32 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instRxcHasSize = HasModel.instRxcHasSize := by
  simp only [instRxcHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.toNat_toInt_add_one_sub_toInt (Nat.zero_lt_succ _)]

public instance instRxcLawfulHasSize : Rxc.LawfulHasSize Int32 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
public instance : Rxc.IsAlwaysFinite Int32 := by exact inferInstance

public instance instRxoHasSize : Rxo.HasSize Int32 := .ofClosed
public instance instRxoLawfulHasSize : Rxo.LawfulHasSize Int32 := by exact inferInstance
public instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int32 := by exact inferInstance

public instance instRxiHasSize : Rxi.HasSize Int32 where
  size lo := ((2 : Int) ^ 31 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.toNat_two_pow_sub_one_sub_toInt (show 32 > 0 by omega)]

public instance instRxiLawfulHasSize : Rxi.LawfulHasSize Int32 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
public instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int32 := by exact inferInstance

end Int32

namespace Int64

open BitVec.Signed
open scoped HasModel

@[inline] def minValueSealed := Int64.minValue
@[inline] def maxValueSealed := Int64.maxValue
theorem minValueSealed_def : minValueSealed = Int64.minValue := (rfl)
theorem maxValueSealed_def : maxValueSealed = Int64.maxValue := (rfl)
seal minValueSealed maxValueSealed

theorem toBitVec_minValueSealed_eq_intMinSealed : minValueSealed.toBitVec = BitVec.Signed.intMinSealed 64 := by
  simp [minValueSealed_def, BitVec.Signed.intMinSealed_def]
theorem toBitVec_maxValueSealed_eq_intMaxSealed : maxValueSealed.toBitVec = BitVec.Signed.intMaxSealed 64 := by
  simp [maxValueSealed_def, BitVec.Signed.intMaxSealed_def]

@[no_expose]
public instance : UpwardEnumerable Int64 where
  succ? i := if i + 1 = minValueSealed then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ maxValueSealed.toInt then some (.ofIntLE _ (by omega) (maxValueSealed_def ▸ h)) else none

instance : Least? Int64 where
  least? := some Int64.minValue

instance : LawfulUpwardEnumerableLeast? Int64 where
  least?_le x := by
    refine ⟨Int64.minValue, rfl, (x.toInt - Int64.minValue.toInt).toNat, ?_⟩
    simp only [succMany?, toInt_neg, Int64.reduceToInt, Int.neg_neg, Nat.reducePow, Int.reduceBmod,
      Int.sub_neg, Int.ofNat_toNat, ofIntLE_eq_ofInt]
    rw [Int.max_eq_left, Int.add_comm _ (OfNat.ofNat _), ← Int.add_assoc]
    · simp [maxValueSealed_def, toInt_le]
    · have := le_toInt x
      omega

instance : HasModel Int64 (BitVec 64) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int64.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int64.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.succ?_eq_of_technicalCondition
    simp [HasModel.encode, succ?, ← Int64.toBitVec_inj, toBitVec_minValueSealed_eq_intMinSealed]
  · ext
    simp [HasModel.succMany?_eq, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_maxValueSealed_eq_intMaxSealed, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int64 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int64 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

public instance instRxcHasSize : Rxc.HasSize Int64 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instRxcHasSize = HasModel.instRxcHasSize := by
  simp only [instRxcHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.toNat_toInt_add_one_sub_toInt (Nat.zero_lt_succ _)]

public instance instRxcLawfulHasSize : Rxc.LawfulHasSize Int64 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
public instance : Rxc.IsAlwaysFinite Int64 := by exact inferInstance

public instance instRxoHasSize : Rxo.HasSize Int64 := .ofClosed
public instance instRxoLawfulHasSize : Rxo.LawfulHasSize Int64 := by exact inferInstance
public instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int64 := by exact inferInstance

public instance instRxiHasSize : Rxi.HasSize Int64 where
  size lo := ((2 : Int) ^ 63 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.toNat_two_pow_sub_one_sub_toInt (show 64 > 0 by omega)]

public instance instRxiLawfulHasSize : Rxi.LawfulHasSize Int64 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
public instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int64 := by exact inferInstance

end Int64

namespace ISize

open BitVec.Signed
open scoped HasModel

@[inline] def minValueSealed := ISize.minValue
@[inline] def maxValueSealed := ISize.maxValue
theorem minValueSealed_def : minValueSealed = ISize.minValue := (rfl)
theorem maxValueSealed_def : maxValueSealed = ISize.maxValue := (rfl)
seal minValueSealed maxValueSealed

private theorem toBitVec_minValueSealed_eq_intMinSealed :
    minValueSealed.toBitVec = BitVec.Signed.intMinSealed System.Platform.numBits := by
  rw [minValueSealed_def, BitVec.Signed.intMinSealed_def, toBitVec_minValue]
  have := System.Platform.numBits_eq; generalize System.Platform.numBits = a at this ⊢
  rcases this with rfl | rfl <;> rfl
private theorem toBitVec_maxValueSealed_eq_intMaxSealed :
    maxValueSealed.toBitVec = BitVec.Signed.intMaxSealed System.Platform.numBits := by
  rw [maxValueSealed_def, BitVec.Signed.intMaxSealed_def, toBitVec_maxValue]
  have := System.Platform.numBits_eq; generalize System.Platform.numBits = a at this ⊢
  rcases this with rfl | rfl <;> rfl

@[no_expose]
public instance : UpwardEnumerable ISize where
  succ? i := if i + 1 = minValueSealed then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ maxValueSealed.toInt then some (.ofIntLE _ (by omega) (maxValueSealed_def ▸ h)) else none

instance : Least? ISize where
  least? := some ISize.minValue

instance : LawfulUpwardEnumerableLeast? ISize where
  least?_le x := by
    refine ⟨ISize.minValue, rfl, (x.toInt - ISize.minValue.toInt).toNat, ?_⟩
    simp only [succMany?, Int.ofNat_toNat, ofIntLE_eq_ofInt, maxValueSealed]
    rw [Int.max_eq_left, Int.sub_eq_add_neg, Int.add_comm _ (-minValue.toInt), ← Int.add_assoc,
      ← Int.sub_eq_add_neg, Int.sub_self, Int.zero_add, dif_pos (toInt_le x), ofInt_toInt]
    have := minValue_le_toInt x
    omega

instance : HasModel ISize (BitVec System.Platform.numBits) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [ISize.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [ISize.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.succ?_eq_of_technicalCondition
    simp [HasModel.encode, succ?, ← ISize.toBitVec_inj, toBitVec_minValueSealed_eq_intMinSealed]
  · ext
    simp [HasModel.succMany?_eq, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_maxValueSealed_eq_intMaxSealed, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable ISize := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE ISize := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

public instance instRxcHasSize : Rxc.HasSize ISize where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instRxcHasSize = HasModel.instRxcHasSize := by
  simp only [instRxcHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.toNat_toInt_add_one_sub_toInt System.Platform.numBits_pos]

public instance instRxcLawfulHasSize : Rxc.LawfulHasSize ISize := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
public instance : Rxc.IsAlwaysFinite ISize := by exact inferInstance

public instance instRxoHasSize : Rxo.HasSize ISize := .ofClosed
public instance instRxoLawfulHasSize : Rxo.LawfulHasSize ISize := by exact inferInstance
public instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite ISize := by exact inferInstance

public instance instRxiHasSize : Rxi.HasSize ISize where
  size lo := ((2 : Int) ^ (System.Platform.numBits - 1) - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.toNat_two_pow_sub_one_sub_toInt System.Platform.numBits_pos]

public instance instRxiLawfulHasSize : Rxi.LawfulHasSize ISize := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
public instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite ISize := by exact inferInstance

end ISize
