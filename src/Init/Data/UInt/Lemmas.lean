/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, François G. Dorais, Mario Carneiro, Mac Malone
-/
prelude
import Init.Data.UInt.Basic
import Init.Data.Fin.Lemmas
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast

open Lean in
set_option hygiene false in
macro "declare_uint_theorems" typeName:ident bits:term:arg : command => do
  let mut cmds ← Syntax.getArgs <$> `(
  namespace $typeName

  theorem zero_def : (0 : $typeName) = ⟨0⟩ := rfl
  theorem one_def : (1 : $typeName) = ⟨1⟩ := rfl
  theorem sub_def (a b : $typeName) : a - b = ⟨a.toBitVec - b.toBitVec⟩ := rfl
  theorem mul_def (a b : $typeName) : a * b = ⟨a.toBitVec * b.toBitVec⟩ := rfl
  theorem mod_def (a b : $typeName) : a % b = ⟨a.toBitVec % b.toBitVec⟩ := rfl
  theorem add_def (a b : $typeName) : a + b = ⟨a.toBitVec + b.toBitVec⟩ := rfl

  @[simp] theorem toNat_ofBitVec : (ofBitVec a).toNat = a.toNat := rfl

  @[deprecated toNat_ofBitVec (since := "2025-02-12")]
  theorem toNat_mk : (ofBitVec a).toNat = a.toNat := rfl

  @[simp] theorem toNat_ofNat {n : Nat} : (ofNat n).toNat = n % 2 ^ $bits := BitVec.toNat_ofNat ..

  @[simp] theorem toNat_ofNatLT {n : Nat} {h : n < size} : (ofNatLT n h).toNat = n := BitVec.toNat_ofNatLT ..

  @[deprecated toNat_ofNatLT (since := "2025-02-13")]
  theorem toNat_ofNatCore {n : Nat} {h : n < size} : (ofNatLT n h).toNat = n := BitVec.toNat_ofNatLT ..

  @[simp] theorem toFin_val (x : $typeName) : x.toFin.val = x.toNat := rfl
  @[deprecated toFin_val (since := "2025-02-12")]
  theorem val_val_eq_toNat (x : $typeName) : x.toFin.val = x.toNat := rfl

  @[simp] theorem toNat_toBitVec (x : $typeName) : x.toBitVec.toNat = x.toNat := rfl
  @[simp] theorem toFin_toBitVec (x : $typeName) : x.toBitVec.toFin = x.toFin := rfl

  @[deprecated toNat_toBitVec (since := "2025-02-21")]
  theorem toNat_toBitVec_eq_toNat (x : $typeName) : x.toBitVec.toNat = x.toNat := rfl

  @[simp] theorem ofBitVec_toBitVec : ∀ (a : $typeName), ofBitVec a.toBitVec = a
    | ⟨_, _⟩ => rfl

  @[deprecated ofBitVec_toBitVec (since := "2025-02-21")]
  theorem ofBitVec_toBitVec_eq : ∀ (a : $typeName), ofBitVec a.toBitVec = a :=
    ofBitVec_toBitVec

  @[deprecated ofBitVec_toBitVec_eq (since := "2025-02-12")]
  theorem mk_toBitVec_eq : ∀ (a : $typeName), ofBitVec a.toBitVec = a
    | ⟨_, _⟩ => rfl

  theorem toBitVec_eq_of_lt {a : Nat} : a < size → (ofNat a).toBitVec.toNat = a :=
    Nat.mod_eq_of_lt

  theorem toNat_ofNat_of_lt {n : Nat} (h : n < size) : (ofNat n).toNat = n := by
    rw [toNat, toBitVec_eq_of_lt h]

  @[int_toBitVec] theorem le_def {a b : $typeName} : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl

  @[int_toBitVec] theorem lt_def {a b : $typeName} : a < b ↔ a.toBitVec < b.toBitVec := .rfl

  theorem le_iff_toNat_le {a b : $typeName} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

  theorem lt_iff_toNat_lt {a b : $typeName} : a < b ↔ a.toNat < b.toNat := .rfl

  @[simp] protected theorem not_le {a b : $typeName} : ¬ a ≤ b ↔ b < a := by simp [le_def, lt_def]

  @[simp] protected theorem not_lt {a b : $typeName} : ¬ a < b ↔ b ≤ a := by simp [le_def, lt_def]

  @[simp] protected theorem le_refl (a : $typeName) : a ≤ a := by simp [le_def]

  @[simp] protected theorem lt_irrefl (a : $typeName) : ¬ a < a := by simp

  protected theorem le_trans {a b c : $typeName} : a ≤ b → b ≤ c → a ≤ c := BitVec.le_trans

  protected theorem lt_trans {a b c : $typeName} : a < b → b < c → a < c := BitVec.lt_trans

  protected theorem le_total (a b : $typeName) : a ≤ b ∨ b ≤ a := BitVec.le_total ..

  protected theorem lt_asymm {a b : $typeName} : a < b → ¬ b < a := BitVec.lt_asymm

  protected theorem toBitVec_eq_of_eq {a b : $typeName} (h : a = b) : a.toBitVec = b.toBitVec := h ▸ rfl

  protected theorem eq_of_toBitVec_eq {a b : $typeName} (h : a.toBitVec = b.toBitVec) : a = b := by
    cases a; cases b; simp_all

  open $typeName (eq_of_toBitVec_eq toBitVec_eq_of_eq) in
  protected theorem toBitVec_inj {a b : $typeName} : a.toBitVec = b.toBitVec ↔ a = b :=
    Iff.intro eq_of_toBitVec_eq toBitVec_eq_of_eq

  open $typeName (eq_of_toBitVec_eq toBitVec_eq_of_eq) in
  @[int_toBitVec]
  protected theorem eq_iff_toBitVec_eq {a b : $typeName} : a = b ↔ a.toBitVec = b.toBitVec :=
    Iff.intro toBitVec_eq_of_eq eq_of_toBitVec_eq

  open $typeName (eq_of_toBitVec_eq toFin) in
  protected theorem eq_of_toFin_eq {a b : $typeName} (h : a.toFin = b.toFin) : a = b := by
    rcases a with ⟨⟨_⟩⟩; rcases b with ⟨⟨_⟩⟩; simp_all [toFin]
  open $typeName (eq_of_toFin_eq) in
  @[deprecated eq_of_toFin_eq (since := "2025-02-12")]
  protected theorem eq_of_val_eq {a b : $typeName} (h : a.toFin = b.toFin) : a = b :=
    eq_of_toFin_eq h

  open $typeName (eq_of_toFin_eq) in
  protected theorem toFin_inj {a b : $typeName} : a.toFin = b.toFin ↔ a = b :=
    Iff.intro eq_of_toFin_eq (congrArg toFin)
  open $typeName (toFin_inj) in
  @[deprecated toFin_inj (since := "2025-02-12")]
  protected theorem val_inj {a b : $typeName} : a.toFin = b.toFin ↔ a = b :=
    toFin_inj

  open $typeName (eq_of_toBitVec_eq) in
  protected theorem toBitVec_ne_of_ne {a b : $typeName} (h : a ≠ b) : a.toBitVec ≠ b.toBitVec :=
    fun h' => h (eq_of_toBitVec_eq h')

  open $typeName (toBitVec_eq_of_eq) in
  protected theorem ne_of_toBitVec_ne {a b : $typeName} (h : a.toBitVec ≠ b.toBitVec) : a ≠ b :=
    fun h' => absurd (toBitVec_eq_of_eq h') h

  open $typeName (ne_of_toBitVec_ne toBitVec_ne_of_ne) in
  @[int_toBitVec]
  protected theorem ne_iff_toBitVec_ne {a b : $typeName} : a ≠ b ↔ a.toBitVec ≠ b.toBitVec :=
    Iff.intro toBitVec_ne_of_ne ne_of_toBitVec_ne

  open $typeName (ne_of_toBitVec_ne) in
  protected theorem ne_of_lt {a b : $typeName} (h : a < b) : a ≠ b := by
    apply ne_of_toBitVec_ne
    apply BitVec.ne_of_lt
    simpa [lt_def] using h

  @[simp] protected theorem toNat_zero : (0 : $typeName).toNat = 0 := Nat.zero_mod _

  @[simp] protected theorem toNat_add (a b : $typeName) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ $bits := BitVec.toNat_add ..

  protected theorem toNat_sub (a b : $typeName) : (a - b).toNat = (2 ^ $bits - b.toNat + a.toNat) % 2 ^ $bits := BitVec.toNat_sub  ..

  @[simp] protected theorem toNat_mul (a b : $typeName) : (a * b).toNat = a.toNat * b.toNat % 2 ^ $bits := BitVec.toNat_mul  ..

  @[simp] protected theorem toNat_mod (a b : $typeName) : (a % b).toNat = a.toNat % b.toNat := BitVec.toNat_umod ..

  @[simp] protected theorem toNat_div (a b : $typeName) : (a / b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv  ..

  @[simp] protected theorem toNat_sub_of_le (a b : $typeName) : b ≤ a → (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le

  protected theorem toNat_lt_size (a : $typeName) : a.toNat < size := a.toBitVec.isLt

  open $typeName (toNat_mod toNat_lt_size) in
  protected theorem toNat_mod_lt {m : Nat} : ∀ (u : $typeName), m > 0 → toNat (u % ofNat m) < m := by
    intro u h1
    by_cases h2 : m < size
    · rw [toNat_mod, toNat_ofNat_of_lt h2]
      apply Nat.mod_lt _ h1
    · apply Nat.lt_of_lt_of_le
      · apply toNat_lt_size
      · simpa using h2

  open $typeName (toNat_mod_lt) in
  set_option linter.deprecated false in
  @[deprecated toNat_mod_lt (since := "2024-09-24")]
  protected theorem modn_lt {m : Nat} : ∀ (u : $typeName), m > 0 → toNat (u % m) < m := by
    intro u
    simp only [(· % ·)]
    simp only [gt_iff_lt, toNat, modn, Fin.modn_val, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
      Nat.reducePow]
    rw [Nat.mod_eq_of_lt]
    · apply Nat.mod_lt
    · apply Nat.lt_of_le_of_lt
      · apply Nat.mod_le
      · apply Fin.is_lt

  protected theorem mod_lt (a : $typeName) {b : $typeName} : 0 < b → a % b < b := by
    simp only [lt_def, mod_def]
    apply BitVec.umod_lt

  protected theorem toNat.inj : ∀ {a b : $typeName}, a.toNat = b.toNat → a = b
    | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

  protected theorem toNat_inj : ∀ {a b : $typeName}, a.toNat = b.toNat ↔ a = b :=
    Iff.intro toNat.inj (congrArg toNat)

  open $typeName (toNat_inj) in
  protected theorem le_antisymm_iff {a b : $typeName} : a = b ↔ a ≤ b ∧ b ≤ a :=
    toNat_inj.symm.trans Nat.le_antisymm_iff

  open $typeName (le_antisymm_iff) in
  protected theorem le_antisymm {a b : $typeName} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
    le_antisymm_iff.2 ⟨h₁, h₂⟩

  @[simp] protected theorem ofNat_one : ofNat 1 = 1 := rfl

  @[simp] protected theorem ofNat_toNat {x : $typeName} : ofNat x.toNat = x := by
    apply toNat.inj
    simp [Nat.mod_eq_of_lt x.toNat_lt_size]

  @[simp]
  theorem toFin_ofNat (n : Nat) : toFin (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl
  @[deprecated toFin_ofNat (since := "2025-02-12")]
  theorem val_ofNat (n : Nat) : toFin (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl

  @[simp, int_toBitVec]
  theorem toBitVec_ofNat (n : Nat) : toBitVec (no_index (OfNat.ofNat n)) = BitVec.ofNat _ n := rfl

  @[simp]
  theorem ofBitVec_ofNat (n : Nat) : ofBitVec (BitVec.ofNat _ n) = OfNat.ofNat n := rfl

  @[deprecated ofBitVec_ofNat (since := "2025-02-12")]
  theorem mk_ofNat (n : Nat) : ofBitVec (BitVec.ofNat _ n) = OfNat.ofNat n := rfl

  )
  if let some nbits := bits.raw.isNatLit? then
    if nbits > 8 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt8 (x : $typeName) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl)
    if nbits < 16 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt16 (x : $typeName) : x.toUInt16.toNat = x.toNat := rfl)
    else if nbits > 16 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt16 (x : $typeName) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl)
    if nbits < 32 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt32 (x : $typeName) : x.toUInt32.toNat = x.toNat := rfl)
    else if nbits > 32 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt32 (x : $typeName) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl)
    if nbits ≤ 32 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUSize (x : $typeName) : x.toUSize.toNat = x.toNat := rfl)
    else
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUSize (x : $typeName) : x.toUSize.toNat = x.toNat % 2 ^ System.Platform.numBits := rfl)
    if nbits < 64 then
      cmds := cmds.push <| ←
        `(@[simp] theorem toNat_toUInt64 (x : $typeName) : x.toUInt64.toNat = x.toNat := rfl)
  cmds := cmds.push <| ← `(end $typeName)
  return ⟨mkNullNode cmds⟩

declare_uint_theorems UInt8 8
declare_uint_theorems UInt16 16
declare_uint_theorems UInt32 32
declare_uint_theorems UInt64 64
declare_uint_theorems USize System.Platform.numBits

@[simp] theorem USize.toNat_ofNat32 {n : Nat} {h : n < 4294967296} : (ofNat32 n h).toNat = n := rfl

@[simp] theorem USize.toNat_toUInt8 (x : USize) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl
@[simp] theorem USize.toNat_toUInt16 (x : USize) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl
@[simp] theorem USize.toNat_toUInt32 (x : USize) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl
@[simp] theorem USize.toNat_toUInt64 (x : USize) : x.toUInt64.toNat = x.toNat := rfl

theorem USize.toNat_ofNat_of_lt_32 {n : Nat} (h : n < 4294967296) : toNat (ofNat n) = n :=
  toNat_ofNat_of_lt (Nat.lt_of_lt_of_le h USize.le_size)

theorem UInt32.toNat_lt_of_lt {n : UInt32} {m : Nat} (h : m < size) : n < ofNat m → n.toNat < m := by
  simp [-toNat_toBitVec, lt_def, BitVec.lt_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.lt_toNat_of_lt {n : UInt32} {m : Nat} (h : m < size) : ofNat m < n → m < n.toNat := by
  simp [-toNat_toBitVec, lt_def, BitVec.lt_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.toNat_le_of_le {n : UInt32} {m : Nat} (h : m < size) : n ≤ ofNat m → n.toNat ≤ m := by
  simp [-toNat_toBitVec, le_def, BitVec.le_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.le_toNat_of_le {n : UInt32} {m : Nat} (h : m < size) : ofNat m ≤ n → m ≤ n.toNat := by
  simp [-toNat_toBitVec, le_def, BitVec.le_def, UInt32.toNat, toBitVec_eq_of_lt h]

@[simp] theorem UInt8.toNat_lt (n : UInt8) : n.toNat < 2 ^ 8 := n.toFin.isLt
@[simp] theorem UInt16.toNat_lt (n : UInt16) : n.toNat < 2 ^ 16 := n.toFin.isLt
@[simp] theorem UInt32.toNat_lt (n : UInt32) : n.toNat < 2 ^ 32 := n.toFin.isLt
@[simp] theorem UInt64.toNat_lt (n : UInt64) : n.toNat < 2 ^ 64 := n.toFin.isLt

theorem UInt8.size_lt_usizeSize : UInt8.size < USize.size := by
  cases USize.size_eq <;> simp_all +decide
theorem UInt8.size_le_usizeSize : UInt8.size ≤ USize.size :=
  Nat.le_of_lt UInt8.size_lt_usizeSize
theorem UInt16.size_lt_usizeSize : UInt16.size < USize.size := by
  cases USize.size_eq <;> simp_all +decide
theorem UInt16.size_le_usizeSize : UInt16.size ≤ USize.size :=
  Nat.le_of_lt UInt16.size_lt_usizeSize
theorem UInt32.size_le_usizeSize : UInt32.size ≤ USize.size := by
  cases USize.size_eq <;> simp_all +decide
theorem USize.size_eq_two_pow : USize.size = 2 ^ System.Platform.numBits := rfl
theorem USize.toNat_lt_two_pow_numBits (n : USize) : n.toNat < 2 ^ System.Platform.numBits := n.toFin.isLt
@[simp] theorem USize.toNat_lt (n : USize) : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le n.toFin.isLt size_le

theorem UInt8.toNat_lt_usizeSize (n : UInt8) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)
theorem UInt16.toNat_lt_usizeSize (n : UInt16) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)
theorem UInt32.toNat_lt_usizeSize (n : UInt32) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)

@[simp] theorem Fin.mk_uInt8ToNat (n : UInt8) : Fin.mk n.toNat n.toFin.isLt = n.toFin := rfl
@[simp] theorem Fin.mk_uInt16ToNat (n : UInt16) : Fin.mk n.toNat n.toFin.isLt = n.toFin := rfl
@[simp] theorem Fin.mk_uInt32ToNat (n : UInt32) : Fin.mk n.toNat n.toFin.isLt = n.toFin := rfl
@[simp] theorem Fin.mk_uInt64ToNat (n : UInt64) : Fin.mk n.toNat n.toFin.isLt = n.toFin := rfl
@[simp] theorem Fin.mk_uSizeToNat (n : USize) : Fin.mk n.toNat n.toFin.isLt = n.toFin := rfl

@[simp] theorem BitVec.ofNatLT_uInt8ToNat (n : UInt8) : BitVec.ofNatLT n.toNat n.toFin.isLt = n.toBitVec := rfl
@[simp] theorem BitVec.ofNatLT_uInt16ToNat (n : UInt16) : BitVec.ofNatLT n.toNat n.toFin.isLt = n.toBitVec := rfl
@[simp] theorem BitVec.ofNatLT_uInt32ToNat (n : UInt32) : BitVec.ofNatLT n.toNat n.toFin.isLt = n.toBitVec := rfl
@[simp] theorem BitVec.ofNatLT_uInt64ToNat (n : UInt64) : BitVec.ofNatLT n.toNat n.toFin.isLt = n.toBitVec := rfl
@[simp] theorem BitVec.ofNatLT_uSizeToNat (n : USize) : BitVec.ofNatLT n.toNat n.toFin.isLt = n.toBitVec := rfl

@[simp] theorem BitVec.ofFin_uInt8ToFin (n : UInt8) : BitVec.ofFin n.toFin = n.toBitVec := rfl
@[simp] theorem BitVec.ofFin_uInt16ToFin (n : UInt16) : BitVec.ofFin n.toFin = n.toBitVec := rfl
@[simp] theorem BitVec.ofFin_uInt32ToFin (n : UInt32) : BitVec.ofFin n.toFin = n.toBitVec := rfl
@[simp] theorem BitVec.ofFin_uInt64ToFin (n : UInt64) : BitVec.ofFin n.toFin = n.toBitVec := rfl
@[simp] theorem BitVec.ofFin_uSizeToFin (n : USize) : BitVec.ofFin n.toFin = n.toBitVec := rfl

@[simp] theorem UInt8.toFin_toUInt16 (n : UInt8) : n.toUInt16.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt8.toFin_toUInt32 (n : UInt8) : n.toUInt32.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt8.toFin_toUInt64 (n : UInt8) : n.toUInt64.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt8.toFin_toUSize (n : UInt8) :
  n.toUSize.toFin = n.toFin.castLE size_le_usizeSize := rfl

@[simp] theorem UInt16.toFin_toUInt32 (n : UInt16) : n.toUInt32.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt16.toFin_toUInt64 (n : UInt16) : n.toUInt64.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt16.toFin_toUSize (n : UInt16) :
  n.toUSize.toFin = n.toFin.castLE size_le_usizeSize := rfl

@[simp] theorem UInt32.toFin_toUInt64 (n : UInt32) : n.toUInt64.toFin = n.toFin.castLE (by decide) := rfl
@[simp] theorem UInt32.toFin_toUSize (n : UInt32) :
  n.toUSize.toFin = n.toFin.castLE size_le_usizeSize := rfl

@[simp] theorem USize.toFin_toUInt64 (n : USize) : n.toUInt64.toFin = n.toFin.castLE size_le_usizeSize := rfl

@[simp] theorem UInt16.toBitVec_toUInt8 (n : UInt16) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := rfl
@[simp] theorem UInt32.toBitVec_toUInt8 (n : UInt32) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := rfl
@[simp] theorem UInt64.toBitVec_toUInt8 (n : UInt64) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := rfl
@[simp] theorem USize.toBitVec_toUInt8 (n : USize) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt8.toBitVec_toUInt16 (n : UInt8) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := rfl
@[simp] theorem UInt32.toBitVec_toUInt16 (n : UInt32) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := rfl
@[simp] theorem UInt64.toBitVec_toUInt16 (n : UInt64) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := rfl
@[simp] theorem USize.toBitVec_toUInt16 (n : USize) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt8.toBitVec_toUInt32 (n : UInt8) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := rfl
@[simp] theorem UInt16.toBitVec_toUInt32 (n : UInt16) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := rfl
@[simp] theorem UInt64.toBitVec_toUInt32 (n : UInt64) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := rfl
@[simp] theorem USize.toBitVec_toUInt32 (n : USize) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt8.toBitVec_toUInt64 (n : UInt8) : n.toUInt64.toBitVec = n.toBitVec.setWidth 64 := rfl
@[simp] theorem UInt16.toBitVec_toUInt64 (n : UInt16) : n.toUInt64.toBitVec = n.toBitVec.setWidth 64 := rfl
@[simp] theorem UInt32.toBitVec_toUInt64 (n : UInt32) : n.toUInt64.toBitVec = n.toBitVec.setWidth 64 := rfl
@[simp] theorem USize.toBitVec_toUInt64 (n : USize) : n.toUInt64.toBitVec = n.toBitVec.setWidth 64 :=
  BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt (USize.toNat_lt _)])

@[simp] theorem UInt8.toBitVec_toUSize (n : UInt8) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt n.toNat_lt_usizeSize])
@[simp] theorem UInt16.toBitVec_toUSize (n : UInt16) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt n.toNat_lt_usizeSize])
@[simp] theorem UInt32.toBitVec_toUSize (n : UInt32) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt n.toNat_lt_usizeSize])
@[simp] theorem UInt64.toBitVec_toUSize (n : UInt64) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt8.ofNatLT_toNat (n : UInt8) : UInt8.ofNatLT n.toNat n.toNat_lt = n := rfl
@[simp] theorem UInt16.ofNatLT_uInt8ToNat (n : UInt8) : UInt16.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt16 := rfl
@[simp] theorem UInt32.ofNatLT_uInt8ToNat (n : UInt8) : UInt32.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt32 := rfl
@[simp] theorem UInt64.ofNatLT_uInt8ToNat (n : UInt8) : UInt64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt64 := rfl
@[simp] theorem USize.ofNatLT_uInt8ToNat (n : UInt8) : USize.ofNatLT n.toNat n.toNat_lt_usizeSize = n.toUSize := rfl

@[simp] theorem UInt16.ofNatLT_toNat (n : UInt16) : UInt16.ofNatLT n.toNat n.toNat_lt = n := rfl
@[simp] theorem UInt32.ofNatLT_uInt16ToNat (n : UInt16) : UInt32.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt32 := rfl
@[simp] theorem UInt64.ofNatLT_uInt16ToNat (n : UInt16) : UInt64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt64 := rfl
@[simp] theorem USize.ofNatLT_uInt16ToNat (n : UInt16) : USize.ofNatLT n.toNat n.toNat_lt_usizeSize = n.toUSize := rfl

@[simp] theorem UInt32.ofNatLT_toNat (n : UInt32) : UInt32.ofNatLT n.toNat n.toNat_lt = n := rfl
@[simp] theorem UInt64.ofNatLT_uInt32ToNat (n : UInt32) : UInt64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt64 := rfl
@[simp] theorem USize.ofNatLT_uInt32ToNat (n : UInt32) : USize.ofNatLT n.toNat n.toNat_lt_usizeSize = n.toUSize := rfl

@[simp] theorem UInt64.ofNatLT_toNat (n : UInt64) : UInt64.ofNatLT n.toNat n.toNat_lt = n := rfl

@[simp] theorem USize.ofNatLT_toNat (n : USize) : USize.ofNatLT n.toNat n.toNat_lt_size = n := rfl
@[simp] theorem UInt64.ofNatLT_uSizeToNat (n : USize) : UInt64.ofNatLT n.toNat n.toNat_lt = n.toUInt64 := rfl

-- We are not making these into `simp` lemmas because they lose the information stored in `h`. ·
theorem UInt8.ofNatLT_uInt16ToNat (n : UInt16) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt8.ofNatLT_uInt32ToNat (n : UInt32) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt8.ofNatLT_uInt64ToNat (n : UInt64) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt8.ofNatLT_uSizeToNat (n : USize) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt16.ofNatLT_uInt32ToNat (n : UInt32) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt16.ofNatLT_uInt64ToNat (n : UInt64) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt16.ofNatLT_uSizeToNat (n : USize) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt32.ofNatLT_uInt64ToNat (n : UInt64) (h) : UInt32.ofNatLT n.toNat h = n.toUInt32 :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt32.ofNatLT_uSizeToNat (n : USize) (h) : UInt32.ofNatLT n.toNat h = n.toUInt32 :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem USize.ofNatLT_uInt64ToNat (n : UInt64) (h) : USize.ofNatLT n.toNat h = n.toUSize :=
  USize.toNat.inj (by simp [Nat.mod_eq_of_lt h])

@[simp] theorem UInt8.ofFin_toFin (n : UInt8) : UInt8.ofFin n.toFin = n := rfl
@[simp] theorem UInt16.ofFin_toFin (n : UInt16) : UInt16.ofFin n.toFin = n := rfl
@[simp] theorem UInt32.ofFin_toFin (n : UInt32) : UInt32.ofFin n.toFin = n := rfl
@[simp] theorem UInt64.ofFin_toFin (n : UInt64) : UInt64.ofFin n.toFin = n := rfl
@[simp] theorem USize.ofFin_toFin (n : USize) : USize.ofFin n.toFin = n := rfl

@[simp] theorem UInt16.ofFin_uint8ToFin (n : UInt8) : UInt16.ofFin (n.toFin.castLE (by decide)) = n.toUInt16 := rfl

@[simp] theorem UInt32.ofFin_uint8ToFin (n : UInt8) : UInt32.ofFin (n.toFin.castLE (by decide)) = n.toUInt32 := rfl
@[simp] theorem UInt32.ofFin_uint16ToFin (n : UInt16) : UInt32.ofFin (n.toFin.castLE (by decide)) = n.toUInt32 := rfl

@[simp] theorem UInt64.ofFin_uint8ToFin (n : UInt8) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofFin_uint16ToFin (n : UInt16) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofFin_uint32ToFin (n : UInt32) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl

@[simp] theorem USize.ofFin_uint8ToFin (n : UInt8) : USize.ofFin (n.toFin.castLE UInt8.size_le_usizeSize) = n.toUSize := rfl
@[simp] theorem USize.ofFin_uint16ToFin (n : UInt16) : USize.ofFin (n.toFin.castLE UInt16.size_le_usizeSize) = n.toUSize := rfl
@[simp] theorem USize.ofFin_uint32ToFin (n : UInt32) : USize.ofFin (n.toFin.castLE UInt32.size_le_usizeSize) = n.toUSize := rfl
