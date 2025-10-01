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
import Init.Omega
public import Init.Data.Range.Polymorphic.BitVec
import Init.Data.Range.Polymorphic.UInt
import all Init.Data.SInt.Basic

public section

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
  sorry

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

-- theorem rxcHasSize_eq_toBitVec :
--     Rxc.HasSize.size (Int8.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
--   simp [Rxc.HasSize.size, rotate, ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub]
--   omega

-- private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
--     Int8.ofBitVec x = y ↔ x = y.toBitVec := by
--   rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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

theorem general_succ? {α : Type u} [UpwardEnumerable α] [LE α] [LT α] [m : HasModel α (BitVec n)]
    {x : α}
    (h : ∀ y, succ? x = some y ↔ ¬ m.encode x + 1#n = BitVec.Signed.irredMin n ∧ m.encode x + 1#n = m.encode y) :
    succ? x = (haveI := HasModel.instUpwardEnumerable (α := α); succ? x) := by
  ext y
  simp only [UpwardEnumerable.succ?, h]
  rw [← Option.map_inj_right HasModel.eq_of_encode_eq, Option.map_map, Function.comp_def]
  simp [HasModel.encode_decode, ← BitVec.eq_sub_iff_add_eq, rotate_eq_iff,
    ← rotate_neg_eq_irredMin_sub, rotate_sub, rotate_rotate]

theorem general_succMany? {α : Type u} [UpwardEnumerable α] [LE α] [LT α] [m : HasModel α (BitVec n)]
    {x : α} {k} :
    haveI := HasModel.instUpwardEnumerable (α := α)
    succMany? k x = if (m.encode x).toInt + ↑k ≤ (BitVec.Signed.irredMax n).toInt then some (m.decode (BitVec.ofInt n ((m.encode x).toInt + ↑k))) else none := by
  have h : ∀ a b c d : Int, a - b + c ≤ d - b ↔ a + c ≤ d := by omega
  simp [UpwardEnumerable.succMany?, BitVec.ofNatLT_eq_ofNat]
  simp [toInt_eq_ofNat_toNat_rotate_sub' sorry, rotate_irredMax, h]
  simp only [← Int.natCast_add]
  congr
  · rw [Nat.lt_iff_add_one_le, Int.ofNat_le, Nat.le_sub_iff_add_le]
    exact Nat.pow_pos (Nat.zero_lt_succ _)
  · generalize rotate (HasModel.encode x) = x
    simp only [ofNat_eq_rotate_ofInt_sub, rotate_rotate]
    congr; omega

theorem general_rxcSize {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem general_rxiSize {lo : BitVec n} (h : n > 0) :
    (2 ^ (n - 1) - lo.toInt).toNat = 2 ^ n - (rotate lo).toNat := by
  simp only [toInt_eq_ofNat_toNat_rotate_sub h]
  simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_comm _ (2 ^ (n - 1)),
    ← Int.add_assoc,
    show (2 : Int) ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n - 1 + 1) by omega,
    show n - 1 + 1 = n by omega]
  simp [← Int.sub_eq_add_neg, Int.toNat_sub', Int.toNat_pow_of_nonneg]

end HasModel

namespace Int8

open BitVec.Signed
open scoped HasModel

@[inline] def irredMin := Int8.minValue
@[inline] def irredMax := Int8.maxValue
theorem irredMin_def : irredMin = Int8.minValue := (rfl)
theorem irredMax_def : irredMax = Int8.maxValue := (rfl)
seal irredMin irredMax

theorem toBitVec_irredMin_eq_irredMin : irredMin.toBitVec = BitVec.Signed.irredMin 8 := by
  simp [irredMin_def, BitVec.Signed.irredMin_def]
theorem toBitVec_irredMax_eq_irredMax : irredMax.toBitVec = BitVec.Signed.irredMax 8 := by
  simp [irredMax_def, BitVec.Signed.irredMax_def]

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = irredMin then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ irredMax.toInt then some (.ofIntLE _ (by omega) (irredMax_def ▸ h)) else none

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.general_succ?
    simp [HasModel.encode, succ?, ← Int8.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · ext
    simp [HasModel.general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int8 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int8 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance

instance : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.general_rxcSize (Nat.zero_lt_succ _)]

instance : Rxc.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
instance : Rxc.IsAlwaysFinite Int8 := inferInstance

instance : Rxo.HasSize Int8 := .ofClosed
instance : Rxo.LawfulHasSize Int8 := inferInstance
instance : Rxo.IsAlwaysFinite Int8 := inferInstance

instance instRxiHasSize : Rxi.HasSize Int8 where
  size lo := ((2 : Int) ^ 7 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.general_rxiSize (show 8 > 0 by omega)]

instance : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int8 := inferInstance

end Int8

namespace Int16

open BitVec.Signed
open scoped HasModel

@[inline] def irredMin := Int16.minValue
@[inline] def irredMax := Int16.maxValue
theorem irredMin_def : irredMin = Int16.minValue := (rfl)
theorem irredMax_def : irredMax = Int16.maxValue := (rfl)
seal irredMin irredMax

theorem toBitVec_irredMin_eq_irredMin : irredMin.toBitVec = BitVec.Signed.irredMin 16 := by
  simp [irredMin_def, BitVec.Signed.irredMin_def]
theorem toBitVec_irredMax_eq_irredMax : irredMax.toBitVec = BitVec.Signed.irredMax 16 := by
  simp [irredMax_def, BitVec.Signed.irredMax_def]

instance : UpwardEnumerable Int16 where
  succ? i := if i + 1 = irredMin then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ irredMax.toInt then some (.ofIntLE _ (by omega) (irredMax_def ▸ h)) else none

instance : HasModel Int16 (BitVec 16) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int16.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int16.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

private theorem ofBitVec_eq_iff {x : BitVec 16} {y : Int16} :
    Int16.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.general_succ?
    simp [HasModel.encode, succ?, ← Int16.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · ext
    simp [HasModel.general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int16 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int16 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLT Int16 := inferInstance
instance : LawfulUpwardEnumerableLT Int16 := inferInstance

instance : Rxc.HasSize Int16 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.general_rxcSize (Nat.zero_lt_succ _)]

instance : Rxc.LawfulHasSize Int16 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
instance : Rxc.IsAlwaysFinite Int16 := inferInstance

instance : Rxo.HasSize Int16 := .ofClosed
instance : Rxo.LawfulHasSize Int16 := inferInstance
instance : Rxo.IsAlwaysFinite Int16 := inferInstance

instance instRxiHasSize : Rxi.HasSize Int16 where
  size lo := ((2 : Int) ^ 15 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.general_rxiSize (show 16 > 0 by omega)]

instance : Rxi.LawfulHasSize Int16 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int16 := inferInstance

end Int16

namespace Int32

open BitVec.Signed
open scoped HasModel

@[inline] def irredMin := Int32.minValue
@[inline] def irredMax := Int32.maxValue
theorem irredMin_def : irredMin = Int32.minValue := (rfl)
theorem irredMax_def : irredMax = Int32.maxValue := (rfl)
seal irredMin irredMax

theorem toBitVec_irredMin_eq_irredMin : irredMin.toBitVec = BitVec.Signed.irredMin 32 := by
  simp [irredMin_def, BitVec.Signed.irredMin_def]
theorem toBitVec_irredMax_eq_irredMax : irredMax.toBitVec = BitVec.Signed.irredMax 32 := by
  simp [irredMax_def, BitVec.Signed.irredMax_def]

instance : UpwardEnumerable Int32 where
  succ? i := if i + 1 = irredMin then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ irredMax.toInt then some (.ofIntLE _ (by omega) (irredMax_def ▸ h)) else none

instance : HasModel Int32 (BitVec 32) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int32.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int32.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

private theorem ofBitVec_eq_iff {x : BitVec 32} {y : Int32} :
    Int32.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.general_succ?
    simp [HasModel.encode, succ?, ← Int32.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · ext
    simp [HasModel.general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int32 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int32 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLT Int32 := inferInstance
instance : LawfulUpwardEnumerableLT Int32 := inferInstance

instance : Rxc.HasSize Int32 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.general_rxcSize (Nat.zero_lt_succ _)]

instance : Rxc.LawfulHasSize Int32 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
instance : Rxc.IsAlwaysFinite Int32 := inferInstance

instance : Rxo.HasSize Int32 := .ofClosed
instance : Rxo.LawfulHasSize Int32 := inferInstance
instance : Rxo.IsAlwaysFinite Int32 := inferInstance

instance instRxiHasSize : Rxi.HasSize Int32 where
  size lo := ((2 : Int) ^ 31 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.general_rxiSize (show 32 > 0 by omega)]

instance : Rxi.LawfulHasSize Int32 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int32 := inferInstance

end Int32

namespace Int64

open BitVec.Signed
open scoped HasModel

@[inline] def irredMin := Int64.minValue
@[inline] def irredMax := Int64.maxValue
theorem irredMin_def : irredMin = Int64.minValue := (rfl)
theorem irredMax_def : irredMax = Int64.maxValue := (rfl)
seal irredMin irredMax

theorem toBitVec_irredMin_eq_irredMin : irredMin.toBitVec = BitVec.Signed.irredMin 64 := by
  simp [irredMin_def, BitVec.Signed.irredMin_def]
theorem toBitVec_irredMax_eq_irredMax : irredMax.toBitVec = BitVec.Signed.irredMax 64 := by
  simp [irredMax_def, BitVec.Signed.irredMax_def]

instance : UpwardEnumerable Int64 where
  succ? i := if i + 1 = irredMin then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ irredMax.toInt then some (.ofIntLE _ (by omega) (irredMax_def ▸ h)) else none

instance : HasModel Int64 (BitVec 64) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int64.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int64.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

private theorem ofBitVec_eq_iff {x : BitVec 64} {y : Int64} :
    Int64.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.general_succ?
    simp [HasModel.encode, succ?, ← Int64.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · ext
    simp [HasModel.general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable Int64 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE Int64 := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLT Int64 := inferInstance
instance : LawfulUpwardEnumerableLT Int64 := inferInstance

instance : Rxc.HasSize Int64 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.general_rxcSize (Nat.zero_lt_succ _)]

instance : Rxc.LawfulHasSize Int64 := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
instance : Rxc.IsAlwaysFinite Int64 := inferInstance

instance : Rxo.HasSize Int64 := .ofClosed
instance : Rxo.LawfulHasSize Int64 := inferInstance
instance : Rxo.IsAlwaysFinite Int64 := inferInstance

instance instRxiHasSize : Rxi.HasSize Int64 where
  size lo := ((2 : Int) ^ 63 - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.general_rxiSize (show 64 > 0 by omega)]

instance : Rxi.LawfulHasSize Int64 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int64 := inferInstance

end Int64

namespace ISize

open BitVec.Signed
open scoped HasModel

@[inline] def irredMin := ISize.minValue
@[inline] def irredMax := ISize.maxValue
theorem irredMin_def : irredMin = ISize.minValue := (rfl)
theorem irredMax_def : irredMax = ISize.maxValue := (rfl)
seal irredMin irredMax

theorem toBitVec_irredMin_eq_irredMin :
    irredMin.toBitVec = BitVec.Signed.irredMin System.Platform.numBits := by
  rw [irredMin_def, BitVec.Signed.irredMin_def, toBitVec_minValue]
  have := System.Platform.numBits_eq; generalize System.Platform.numBits = a at this ⊢
  rcases this with rfl | rfl <;> rfl
theorem toBitVec_irredMax_eq_irredMax :
    irredMax.toBitVec = BitVec.Signed.irredMax System.Platform.numBits := by
  rw [irredMax_def, BitVec.Signed.irredMax_def, toBitVec_maxValue]
  have := System.Platform.numBits_eq; generalize System.Platform.numBits = a at this ⊢
  rcases this with rfl | rfl <;> rfl

instance : UpwardEnumerable ISize where
  succ? i := if i + 1 = irredMin then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ irredMax.toInt then some (.ofIntLE _ (by omega) (irredMax_def ▸ h)) else none

instance : HasModel ISize (BitVec System.Platform.numBits) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [ISize.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [ISize.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

private theorem ofBitVec_eq_iff {x : BitVec System.Platform.numBits} {y : ISize} :
    ISize.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply HasModel.general_succ?
    simp [HasModel.encode, succ?, ← ISize.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · ext
    simp [HasModel.general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

instance : LawfulUpwardEnumerable ISize := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLE ISize := by
  simp only [instUpwardEnumerable_eq]
  infer_instance

instance : LawfulUpwardEnumerableLT ISize := inferInstance
instance : LawfulUpwardEnumerableLT ISize := inferInstance

instance : Rxc.HasSize ISize where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, HasModel.general_rxcSize System.Platform.numBits_pos]

instance : Rxc.LawfulHasSize ISize := by
  simp only [instUpwardEnumerable_eq, instRxcHasSize_eq]
  infer_instance
instance : Rxc.IsAlwaysFinite ISize := inferInstance

instance : Rxo.HasSize ISize := .ofClosed
instance : Rxo.LawfulHasSize ISize := inferInstance
instance : Rxo.IsAlwaysFinite ISize := inferInstance

instance instRxiHasSize : Rxi.HasSize ISize where
  size lo := ((2 : Int) ^ (System.Platform.numBits - 1) - lo.toInt).toNat

theorem instRxiHasSize_eq :
    instRxiHasSize = HasModel.instRxiHasSize := by
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, ← toInt_toBitVec,
    HasModel.encode, HasModel.general_rxiSize System.Platform.numBits_pos]

instance : Rxi.LawfulHasSize ISize := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite ISize := inferInstance

end ISize
