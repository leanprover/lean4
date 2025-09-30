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

end HasModel

namespace Int8

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
    HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
    UpwardEnumerable.succMany?]
  congr 1
  · ext x y
    simp [← Int8.toBitVec_inj, ← BitVec.eq_sub_iff_add_eq, rotate, BitVec.sub_sub]
  · ext n x y
    have h₁ : ∀ n, (2 : Int) ^ n = ↑((2 : Nat) ^ n) := by simp
    have h₂ : ∀ x : Int8, x - ofNat (2 ^ 7) = x + ofNat (2 ^ 7) := by simp
    simp [h₁, h₂, ← Int8.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 8 > 0 by omega),
      rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int8.ofInt_eq_ofNat,
      ofInt_eq_ofNat, Int8.add_assoc, Int8.add_comm (ofNat (2 ^ 7)), and_congr_left_iff,
      - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
    omega

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

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, bla (Nat.zero_lt_succ _)]

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (Nat.zero_lt_succ _), Int.toNat_sub,
    show ∀ a : Int, (2 ^ 7) - (a - (2 ^ 7)) = ↑((2 : Nat) ^ 8) - a by omega]

instance : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int8 := inferInstance

end Int8

namespace Int16

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

@[inline]
def irredMin := Int16.minValue
theorem irredMin_def : irredMin = Int16.minValue := (rfl)
seal irredMin

@[inline]
def irredMax := Int16.maxValue
theorem irredMax_def : irredMax = Int16.maxValue := (rfl)
seal irredMax

theorem toBitVec_irredMin_eq_irredMin :
    irredMin.toBitVec = BitVec.Signed.irredMin 16 := by
  simp [irredMin_def, BitVec.Signed.irredMin_def]

theorem toBitVec_irredMax_eq_irredMax :
    irredMax.toBitVec = BitVec.Signed.irredMax 16 := by
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

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    apply general_succ?
    intro y
    simp [HasModel.encode, succ?, ← Int16.toBitVec_inj, toBitVec_irredMin_eq_irredMin]
  · apply funext; intro n; apply funext; intro x
    simp [general_succMany?, instUpwardEnumerable, HasModel.encode, HasModel.decode,
      ← toInt_toBitVec, toBitVec_irredMax_eq_irredMax, ofIntLE_eq_ofInt]

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

@[inline]
def irredMin := Int16.minValue
theorem irredMin_def : irredMin = Int16.minValue := (rfl)
seal irredMin

@[inline]
def irredMax := Int16.maxValue
theorem irredMax_def : irredMax = Int16.maxValue := (rfl)
seal irredMax

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

-- theorem bla {x : Int16} :
--     (succ? x) = (if (x.toBitVec + 1 = - 2 ^ 15) then none else some (x.toBitVec + 1)).map .ofBitVec := by
--   sorry

-- #print instUpwardEnumerable

-- axiom sry {α} : α

-- seal HasModel.instUpwardEnumerable

-- theorem ex :
--     sry = (HasModel.instUpwardEnumerable : UpwardEnumerable Int16) := by
--   apply UpwardEnumerable.ext
--   · apply funext; intro x
--     generalize h : @succ? Int16 sry x = g
--     rw [bla] at h
--     rw [bla]

theorem bla {x : Int16} :
    (succ? x) = (if (x.toBitVec + 1 = - 2 ^ 15) then none else some (x.toBitVec + 1)).map .ofBitVec := by
  simp only [← BitVec.eq_sub_iff_add_eq, succ?, ← toBitVec_inj,
    show minValue.toBitVec = - 2 ^ 15 by rfl, Int16.toBitVec_add, toBitVec_ofNat]
  split <;> simp

#print instUpwardEnumerable

--seal HasModel.instUpwardEnumerable
--seal instUpwardEnumerable

theorem ex :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  apply UpwardEnumerable.ext
  · apply funext; intro x
    refine Eq.trans bla ?_


  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable, HasModel.encode,
    HasModel.decode]
  -- simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
  --   HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
  --   UpwardEnumerable.succMany?]
  -- have : ∀ {s sm s' sm'}, sm = sm' → UpwardEnumerable.mk s sm = (UpwardEnumerable.mk s' sm' : UpwardEnumerable Int16) := by
  --   sorry

  -- apply this
  -- · ext n x y
  --   simp only [← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 16 > 0 by omega), rotate,
  --     BitVec.natCast_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  --   simp only [ofIntLE_eq_ofInt]
  --   -- simp [h₁, h₂, ← Int16.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 16 > 0 by omega),
  --   --   rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int16.ofInt_eq_ofNat,
  --   --   ofInt_eq_ofNat, Int16.add_assoc, Int16.add_comm (ofNat (2 ^ 15)), and_congr_left_iff,
  --   --   - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
  --   omega

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
    HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
    UpwardEnumerable.succMany?]
  have : ∀ {s sm s' sm'}, s = s' → sm = sm' → UpwardEnumerable.mk s sm = (UpwardEnumerable.mk s' sm' : UpwardEnumerable Int16) := by
    sorry
  apply this
  --congr 1
  · sorry
    -- ext x y
    -- simp [← Int16.toBitVec_inj, ← BitVec.eq_sub_iff_add_eq, rotate, BitVec.sub_sub]
  · ext n x y
    simp only [← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 16 > 0 by omega), rotate,
      BitVec.natCast_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [ofIntLE_eq_ofInt]
    -- simp [h₁, h₂, ← Int16.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 16 > 0 by omega),
    --   rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int16.ofInt_eq_ofNat,
    --   ofInt_eq_ofNat, Int16.add_assoc, Int16.add_comm (ofNat (2 ^ 15)), and_congr_left_iff,
    --   - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
    omega

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

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, bla (Nat.zero_lt_succ _)]

private theorem ofBitVec_eq_iff {x : BitVec 16} {y : Int16} :
    Int16.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (Nat.zero_lt_succ _), Int.toNat_sub,
    show ∀ a : Int, (2 ^ 15) - (a - (2 ^ 15)) = ↑((2 : Nat) ^ 16) - a by omega]

instance : Rxi.LawfulHasSize Int16 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int16 := inferInstance

end Int16

namespace Int8

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
    HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
    UpwardEnumerable.succMany?]
  congr 1
  · ext x y
    simp [← Int8.toBitVec_inj, ← BitVec.eq_sub_iff_add_eq, rotate, BitVec.sub_sub]
  · ext n x y
    have h₁ : ∀ n, (2 : Int) ^ n = ↑((2 : Nat) ^ n) := by simp
    have h₂ : ∀ x : Int8, x - ofNat (2 ^ 7) = x + ofNat (2 ^ 7) := by simp
    simp [h₁, h₂, ← Int8.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 8 > 0 by omega),
      rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int8.ofInt_eq_ofNat,
      ofInt_eq_ofNat, Int8.add_assoc, Int8.add_comm (ofNat (2 ^ 7)), and_congr_left_iff,
      - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
    omega

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

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, bla (Nat.zero_lt_succ _)]

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (Nat.zero_lt_succ _), Int.toNat_sub,
    show ∀ a : Int, (2 ^ 7) - (a - (2 ^ 7)) = ↑((2 : Nat) ^ 8) - a by omega]

instance : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int8 := inferInstance

end Int8

namespace Int8

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
    HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
    UpwardEnumerable.succMany?]
  congr 1
  · ext x y
    simp [← Int8.toBitVec_inj, ← BitVec.eq_sub_iff_add_eq, rotate, BitVec.sub_sub]
  · ext n x y
    have h₁ : ∀ n, (2 : Int) ^ n = ↑((2 : Nat) ^ n) := by simp
    have h₂ : ∀ x : Int8, x - ofNat (2 ^ 7) = x + ofNat (2 ^ 7) := by simp
    simp [h₁, h₂, ← Int8.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 8 > 0 by omega),
      rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int8.ofInt_eq_ofNat,
      ofInt_eq_ofNat, Int8.add_assoc, Int8.add_comm (ofNat (2 ^ 7)), and_congr_left_iff,
      - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
    omega

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

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, bla (Nat.zero_lt_succ _)]

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (Nat.zero_lt_succ _), Int.toNat_sub,
    show ∀ a : Int, (2 ^ 7) - (a - (2 ^ 7)) = ↑((2 : Nat) ^ 8) - a by omega]

instance : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int8 := inferInstance

end Int8

namespace Int8

open BitVec.Signed
open scoped HasModel

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

instance : HasModel Int8 (BitVec 8) where
  encode x := x.toBitVec
  decode x := .ofBitVec x
  encode_decode := by simp
  decode_encode := by simp
  le_iff_encode_le := by simp [Int8.le_iff_toBitVec_sle, BitVec.Signed.instLE]
  lt_iff_encode_lt := by simp [Int8.lt_iff_toBitVec_slt, BitVec.Signed.instLT]

theorem instUpwardEnumerable_eq :
    instUpwardEnumerable = HasModel.instUpwardEnumerable := by
  simp only [instUpwardEnumerable, HasModel.instUpwardEnumerable,
    HasModel.encode, HasModel.decode, UpwardEnumerable.succ?,
    UpwardEnumerable.succMany?]
  congr 1
  · ext x y
    simp [← Int8.toBitVec_inj, ← BitVec.eq_sub_iff_add_eq, rotate, BitVec.sub_sub]
  · ext n x y
    have h₁ : ∀ n, (2 : Int) ^ n = ↑((2 : Nat) ^ n) := by simp
    have h₂ : ∀ x : Int8, x - ofNat (2 ^ 7) = x + ofNat (2 ^ 7) := by simp
    simp [h₁, h₂, ← Int8.toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (show 8 > 0 by omega),
      rotate, BitVec.ofNatLT_eq_ofNat, ofIntLE_eq_ofInt, Int8.ofInt_eq_ofNat,
      ofInt_eq_ofNat, Int8.add_assoc, Int8.add_comm (ofNat (2 ^ 7)), and_congr_left_iff,
      - Int.reducePow, - Nat.reducePow, - Int.natCast_pow, - Int.natCast_add, - Int.natCast_emod, ]
    omega

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

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem instRxcHasSize_eq :
    instHasSize = HasModel.instRxcHasSize := by
  simp only [instHasSize, HasModel.instRxcHasSize, Rxc.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, bla (Nat.zero_lt_succ _)]

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

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
  simp only [instRxiHasSize, HasModel.instRxiHasSize, Rxi.HasSize.size, HasModel.encode,
    ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub (Nat.zero_lt_succ _), Int.toNat_sub,
    show ∀ a : Int, (2 ^ 7) - (a - (2 ^ 7)) = ↑((2 : Nat) ^ 8) - a by omega]

instance : Rxi.LawfulHasSize Int8 := by
  simp only [instUpwardEnumerable_eq, instRxiHasSize_eq]
  infer_instance
instance : Rxi.IsAlwaysFinite Int8 := inferInstance

end Int8

namespace Int16

open BitVec.Signed

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int16 where
  succ? i := if i + 1 = Int16.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int16.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

theorem succ?_ofBitVec {x : BitVec 16} :
    UpwardEnumerable.succ? (Int16.ofBitVec x) = Int16.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, ← toBitVec_inj, Int16.toBitVec_add, toBitVec_ofBitVec, toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, toBitVec_neg, BitVec.reduceNeg, rotate, BitVec.natCast_eq_ofNat,
    Option.map_eq_map, Option.map_map, Function.comp_def]
  split <;> split <;> try (simp_all [Int16.add_assoc]; done)
  all_goals
    rename_i h h'
    rw [BitVec.add_assoc, BitVec.add_comm 32768#16 1#16, ← BitVec.add_assoc,
      ← BitVec.eq_sub_iff_add_eq] at h'
    simp [h] at h'

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 16} :
    UpwardEnumerable.succMany? k (Int16.ofBitVec x) =
      Int16.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp only [succMany?, maxValue, ofIntLE_eq_ofInt, ofInt_add, dite_eq_ite, rotate,
    BitVec.ofNatLT_eq_ofNat, Option.map_eq_map, Option.map_if, ofBitVec_add, ofBitVec_ofNat,
    ofNat_add, ofNat_bitVecToNat]
  split <;> split <;> try (simp [← ofBitVec_ofInt, Int16.add_assoc, Int16.add_comm (-32768)]; done)
  all_goals
    rename_i h h'
    simp [toInt_eq_ofNat_toNat_rotate_sub, rotate] at h h'
    omega

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LE (Int16.ofBitVec x) (Int16.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec, ofBitVec_inj]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LT (Int16.ofBitVec x) (Int16.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec, ofBitVec_inj]

instance : LawfulUpwardEnumerable Int16 where
  ne_of_lt x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLT_ofBitVec, ne_iff_ofBitVec_ne, -ofBitVec_toBitVec] using
      LawfulUpwardEnumerable.ne_of_lt (α := BitVec 16) _ _
  succMany?_zero x := by
    rw [← ofBitVec_toBitVec x]
    simpa [succMany?_ofBitVec, ofBitVec_inj, -ofBitVec_toBitVec] using succMany?_zero
  succMany?_add_one n x := by
    rw [← ofBitVec_toBitVec x]
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec, -ofBitVec_toBitVec]

private theorem toBitVec_le {x y : Int16} :
    x.toBitVec ≤ y.toBitVec ↔ x ≤ y := by
  rw [Int16.le_iff_toBitVec_sle]
  simp [LE.le]

private theorem ofBitVec_le {x y : BitVec 16} :
    Int16.ofBitVec x ≤ Int16.ofBitVec y ↔ x ≤ y := by
  simp [← toBitVec_le]

instance : LawfulUpwardEnumerableLE Int16 where
  le_iff x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLE_ofBitVec, -ofBitVec_toBitVec, ofBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff (α := BitVec 16) _ _

instance : LawfulUpwardEnumerableLT Int16 := inferInstance
instance : LawfulUpwardEnumerableLT Int16 := inferInstance

instance : Rxc.HasSize Int16 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (Int16.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size, rotate, ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub]
  omega

private theorem ofBitVec_eq_iff {x : BitVec 16} {y : Int16} :
    Int16.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

instance : Rxc.LawfulHasSize Int16 where
  size_eq_zero_of_not_le lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt16.lt_iff_toBitVec_lt, ofBitVec_le, -ofBitVec_toBitVec] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 16) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, succ?_ofBitVec, ofBitVec_le,
      -ofBitVec_toBitVec] using Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 16) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec x, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, ← UInt16.toBitVec_inj,
      ofBitVec_le, succ?_ofBitVec, -ofBitVec_toBitVec, ofBitVec_eq_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 16) _ _ _

instance : Rxc.IsAlwaysFinite Int16 := inferInstance

instance : Rxo.HasSize Int16 := .ofClosed
instance : Rxo.LawfulHasSize Int16 := inferInstance
instance : Rxo.IsAlwaysFinite Int16 := inferInstance

instance : Rxi.HasSize Int16 where
  size lo := ((2 : Int) ^ 15 - lo.toInt).toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (Int16.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size, rotate, toInt_eq_ofNat_toNat_rotate_sub]
  omega

instance : Rxi.LawfulHasSize Int16 where
  size_eq_one_of_succ?_eq_none lo := by
    rw [← ofBitVec_toBitVec lo]
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 16) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec lo']
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, ofBitVec_eq_iff, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 16) _ _

end Int16

namespace Int32

open BitVec.Signed

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int32 where
  succ? i := if i + 1 = Int32.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int32.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

theorem succ?_ofBitVec {x : BitVec 32} :
    UpwardEnumerable.succ? (Int32.ofBitVec x) = Int32.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, ← toBitVec_inj, Int32.toBitVec_add, toBitVec_ofBitVec, toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, toBitVec_neg, BitVec.reduceNeg, rotate, BitVec.natCast_eq_ofNat,
    Option.map_eq_map, Option.map_map, Function.comp_def]
  split <;> split <;> try (simp_all [Int32.add_assoc]; done)
  all_goals
    rename_i h h'
    rw [BitVec.add_assoc, BitVec.add_comm 2147483648#32 1#32, ← BitVec.add_assoc,
      ← BitVec.eq_sub_iff_add_eq] at h'
    simp [h] at h'

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 32} :
    UpwardEnumerable.succMany? k (Int32.ofBitVec x) =
      Int32.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp only [succMany?, maxValue, ofIntLE_eq_ofInt, ofInt_add, dite_eq_ite, rotate,
    BitVec.ofNatLT_eq_ofNat, Option.map_eq_map, Option.map_if, ofBitVec_add, ofBitVec_ofNat,
    ofNat_add, ofNat_bitVecToNat]
  split <;> split <;> try (simp [← ofBitVec_ofInt, Int32.add_assoc, Int32.add_comm (-2147483648)]; done)
  all_goals
    rename_i h h'
    simp [toInt_eq_ofNat_toNat_rotate_sub, rotate] at h h'
    omega

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LE (Int32.ofBitVec x) (Int32.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec, ofBitVec_inj]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LT (Int32.ofBitVec x) (Int32.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec, ofBitVec_inj]

instance : LawfulUpwardEnumerable Int32 where
  ne_of_lt x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLT_ofBitVec, ne_iff_ofBitVec_ne, -ofBitVec_toBitVec] using
      LawfulUpwardEnumerable.ne_of_lt (α := BitVec 32) _ _
  succMany?_zero x := by
    rw [← ofBitVec_toBitVec x]
    simpa [succMany?_ofBitVec, ofBitVec_inj, -ofBitVec_toBitVec] using succMany?_zero
  succMany?_add_one n x := by
    rw [← ofBitVec_toBitVec x]
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec, -ofBitVec_toBitVec]

private theorem toBitVec_le {x y : Int32} :
    x.toBitVec ≤ y.toBitVec ↔ x ≤ y := by
  rw [Int32.le_iff_toBitVec_sle]
  simp [LE.le]

private theorem ofBitVec_le {x y : BitVec 32} :
    Int32.ofBitVec x ≤ Int32.ofBitVec y ↔ x ≤ y := by
  simp [← toBitVec_le]

instance : LawfulUpwardEnumerableLE Int32 where
  le_iff x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLE_ofBitVec, -ofBitVec_toBitVec, ofBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff (α := BitVec 32) _ _

instance : LawfulUpwardEnumerableLT Int32 := inferInstance
instance : LawfulUpwardEnumerableLT Int32 := inferInstance

instance : Rxc.HasSize Int32 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

def offset : BitVec 32 := 2 ^ 32 - 1

theorem bla {lo hi : BitVec n} (h : n > 0) :
    (hi.toInt + 1 - lo.toInt).toNat = (rotate hi).toNat + 1 - (rotate lo).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [toInt_eq_ofNat_toNat_rotate_sub h, rotate, BitVec.toNat_add, Int.natCast_emod,
      show ∀ a b c d : Int, (a - b) + c - (d - b) = a + c - d by omega]
    omega

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (Int32.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  rw [← ofBitVec_toBitVec (x := hi)]
  generalize hi.toBitVec = hi
  simp only [Rxc.HasSize.size, toInt_ofBitVec, toBitVec_ofBitVec]
  apply bla

private theorem ofBitVec_eq_iff {x : BitVec 32} {y : Int32} :
    Int32.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

instance : Rxc.LawfulHasSize Int32 where
  size_eq_zero_of_not_le lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt32.lt_iff_toBitVec_lt, ofBitVec_le, -ofBitVec_toBitVec] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 32) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, succ?_ofBitVec, ofBitVec_le,
      -ofBitVec_toBitVec] using Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 32) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec x, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, ← UInt32.toBitVec_inj,
      ofBitVec_le, succ?_ofBitVec, -ofBitVec_toBitVec, ofBitVec_eq_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 32) _ _ _

instance : Rxc.IsAlwaysFinite Int32 := inferInstance

instance : Rxo.HasSize Int32 := .ofClosed
instance : Rxo.LawfulHasSize Int32 := inferInstance
instance : Rxo.IsAlwaysFinite Int32 := inferInstance

instance : Rxi.HasSize Int32 where
  size lo := ((2 : Int) ^ 31 - lo.toInt).toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (Int32.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size, rotate, toInt_eq_ofNat_toNat_rotate_sub]
  omega

instance : Rxi.LawfulHasSize Int32 where
  size_eq_one_of_succ?_eq_none lo := by
    rw [← ofBitVec_toBitVec lo]
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 32) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec lo']
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, ofBitVec_eq_iff, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 32) _ _

end Int32
namespace Int8

open BitVec.Signed

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

theorem succ?_ofBitVec {x : BitVec 8} :
    UpwardEnumerable.succ? (Int8.ofBitVec x) = Int8.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, ← toBitVec_inj, Int8.toBitVec_add, toBitVec_ofBitVec, toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, toBitVec_neg, BitVec.reduceNeg, rotate, BitVec.natCast_eq_ofNat,
    Option.map_eq_map, Option.map_map, Function.comp_def]
  split <;> split <;> try (simp_all [Int8.add_assoc]; done)
  all_goals
    rename_i h h'
    rw [BitVec.add_assoc, BitVec.add_comm 128#8 1#8, ← BitVec.add_assoc,
      ← BitVec.eq_sub_iff_add_eq] at h'
    simp [h] at h'

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 8} :
    UpwardEnumerable.succMany? k (Int8.ofBitVec x) =
      Int8.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp only [succMany?, maxValue, ofIntLE_eq_ofInt, ofInt_add, dite_eq_ite, rotate,
    BitVec.ofNatLT_eq_ofNat, Option.map_eq_map, Option.map_if, ofBitVec_add, ofBitVec_ofNat,
    ofNat_add, ofNat_bitVecToNat]
  split <;> split <;> try (simp [← ofBitVec_ofInt, Int8.add_assoc, Int8.add_comm (-128)]; done)
  all_goals
    rename_i h h'
    simp [toInt_eq_ofNat_toNat_rotate_sub, rotate] at h h'
    omega

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LE (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec, ofBitVec_inj]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LT (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec, ofBitVec_inj]

instance : LawfulUpwardEnumerable Int8 where
  ne_of_lt x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLT_ofBitVec, ne_iff_ofBitVec_ne, -ofBitVec_toBitVec] using
      LawfulUpwardEnumerable.ne_of_lt (α := BitVec 8) _ _
  succMany?_zero x := by
    rw [← ofBitVec_toBitVec x]
    simpa [succMany?_ofBitVec, ofBitVec_inj, -ofBitVec_toBitVec] using succMany?_zero
  succMany?_add_one n x := by
    rw [← ofBitVec_toBitVec x]
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec, -ofBitVec_toBitVec]

private theorem toBitVec_le {x y : Int8} :
    x.toBitVec ≤ y.toBitVec ↔ x ≤ y := by
  rw [Int8.le_iff_toBitVec_sle]
  simp [LE.le]

private theorem ofBitVec_le {x y : BitVec 8} :
    Int8.ofBitVec x ≤ Int8.ofBitVec y ↔ x ≤ y := by
  simp [← toBitVec_le]

instance : LawfulUpwardEnumerableLE Int8 where
  le_iff x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLE_ofBitVec, -ofBitVec_toBitVec, ofBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff (α := BitVec 8) _ _

instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance

instance : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (Int8.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size, rotate, ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub]
  omega

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

instance : Rxc.LawfulHasSize Int8 where
  size_eq_zero_of_not_le lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt, ofBitVec_le, -ofBitVec_toBitVec] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_ofBitVec, ofBitVec_le,
      -ofBitVec_toBitVec] using Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec x, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj,
      ofBitVec_le, succ?_ofBitVec, -ofBitVec_toBitVec, ofBitVec_eq_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _ _

instance : Rxc.IsAlwaysFinite Int8 := inferInstance

instance : Rxo.HasSize Int8 := .ofClosed
instance : Rxo.LawfulHasSize Int8 := inferInstance
instance : Rxo.IsAlwaysFinite Int8 := inferInstance

instance : Rxi.HasSize Int8 where
  size lo := ((2 : Int) ^ 7 - lo.toInt).toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (Int8.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size, rotate, toInt_eq_ofNat_toNat_rotate_sub]
  omega

instance : Rxi.LawfulHasSize Int8 where
  size_eq_one_of_succ?_eq_none lo := by
    rw [← ofBitVec_toBitVec lo]
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec lo']
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, ofBitVec_eq_iff, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _

end Int8
namespace Int8

open BitVec.Signed

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

theorem succ?_ofBitVec {x : BitVec 8} :
    UpwardEnumerable.succ? (Int8.ofBitVec x) = Int8.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, ← toBitVec_inj, Int8.toBitVec_add, toBitVec_ofBitVec, toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, toBitVec_neg, BitVec.reduceNeg, rotate, BitVec.natCast_eq_ofNat,
    Option.map_eq_map, Option.map_map, Function.comp_def]
  split <;> split <;> try (simp_all [Int8.add_assoc]; done)
  all_goals
    rename_i h h'
    rw [BitVec.add_assoc, BitVec.add_comm 128#8 1#8, ← BitVec.add_assoc,
      ← BitVec.eq_sub_iff_add_eq] at h'
    simp [h] at h'

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 8} :
    UpwardEnumerable.succMany? k (Int8.ofBitVec x) =
      Int8.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp only [succMany?, maxValue, ofIntLE_eq_ofInt, ofInt_add, dite_eq_ite, rotate,
    BitVec.ofNatLT_eq_ofNat, Option.map_eq_map, Option.map_if, ofBitVec_add, ofBitVec_ofNat,
    ofNat_add, ofNat_bitVecToNat]
  split <;> split <;> try (simp [← ofBitVec_ofInt, Int8.add_assoc, Int8.add_comm (-128)]; done)
  all_goals
    rename_i h h'
    simp [toInt_eq_ofNat_toNat_rotate_sub, rotate] at h h'
    omega

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LE (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec, ofBitVec_inj]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LT (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec, ofBitVec_inj]

instance : LawfulUpwardEnumerable Int8 where
  ne_of_lt x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLT_ofBitVec, ne_iff_ofBitVec_ne, -ofBitVec_toBitVec] using
      LawfulUpwardEnumerable.ne_of_lt (α := BitVec 8) _ _
  succMany?_zero x := by
    rw [← ofBitVec_toBitVec x]
    simpa [succMany?_ofBitVec, ofBitVec_inj, -ofBitVec_toBitVec] using succMany?_zero
  succMany?_add_one n x := by
    rw [← ofBitVec_toBitVec x]
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec, -ofBitVec_toBitVec]

private theorem toBitVec_le {x y : Int8} :
    x.toBitVec ≤ y.toBitVec ↔ x ≤ y := by
  rw [Int8.le_iff_toBitVec_sle]
  simp [LE.le]

private theorem ofBitVec_le {x y : BitVec 8} :
    Int8.ofBitVec x ≤ Int8.ofBitVec y ↔ x ≤ y := by
  simp [← toBitVec_le]

instance : LawfulUpwardEnumerableLE Int8 where
  le_iff x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLE_ofBitVec, -ofBitVec_toBitVec, ofBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff (α := BitVec 8) _ _

instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance

instance : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (Int8.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size, rotate, ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub]
  omega

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

instance : Rxc.LawfulHasSize Int8 where
  size_eq_zero_of_not_le lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt, ofBitVec_le, -ofBitVec_toBitVec] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_ofBitVec, ofBitVec_le,
      -ofBitVec_toBitVec] using Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec x, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj,
      ofBitVec_le, succ?_ofBitVec, -ofBitVec_toBitVec, ofBitVec_eq_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _ _

instance : Rxc.IsAlwaysFinite Int8 := inferInstance

instance : Rxo.HasSize Int8 := .ofClosed
instance : Rxo.LawfulHasSize Int8 := inferInstance
instance : Rxo.IsAlwaysFinite Int8 := inferInstance

instance : Rxi.HasSize Int8 where
  size lo := ((2 : Int) ^ 7 - lo.toInt).toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (Int8.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size, rotate, toInt_eq_ofNat_toNat_rotate_sub]
  omega

instance : Rxi.LawfulHasSize Int8 where
  size_eq_one_of_succ?_eq_none lo := by
    rw [← ofBitVec_toBitVec lo]
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec lo']
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, ofBitVec_eq_iff, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _

end Int8
