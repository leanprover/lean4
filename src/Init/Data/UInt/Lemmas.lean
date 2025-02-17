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
-- TODO(kmill): needed this for bootstrapping issue; remove option later
set_option interpreter.prefer_native false in
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

  @[simp] theorem toFin_val_eq_toNat (x : $typeName) : x.toFin.val = x.toNat := rfl
  @[deprecated toFin_val_eq_toNat (since := "2025-02-12")]
  theorem val_val_eq_toNat (x : $typeName) : x.toFin.val = x.toNat := rfl

  theorem toNat_toBitVec_eq_toNat (x : $typeName) : x.toBitVec.toNat = x.toNat := rfl

  @[simp] theorem ofBitVec_toBitVec_eq : ∀ (a : $typeName), ofBitVec a.toBitVec = a
    | ⟨_, _⟩ => rfl

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

section
-- TODO(kmill): needed this for bootstrapping issue; remove option and section later
set_option interpreter.prefer_native false
declare_uint_theorems UInt8 8
declare_uint_theorems UInt16 16
declare_uint_theorems UInt32 32
declare_uint_theorems UInt64 64
declare_uint_theorems USize System.Platform.numBits
end

@[simp] theorem USize.toNat_ofNat32 {n : Nat} {h : n < 4294967296} : (ofNat32 n h).toNat = n := rfl

@[simp] theorem USize.toNat_toUInt32 (x : USize) : x.toUInt32.toNat = x.toNat % 2 ^ 32  := rfl

@[simp] theorem USize.toNat_toUInt64 (x : USize) : x.toUInt64.toNat = x.toNat := rfl

theorem USize.toNat_ofNat_of_lt_32 {n : Nat} (h : n < 4294967296) : toNat (ofNat n) = n :=
  toNat_ofNat_of_lt (Nat.lt_of_lt_of_le h le_usize_size)

theorem UInt32.toNat_lt_of_lt {n : UInt32} {m : Nat} (h : m < size) : n < ofNat m → n.toNat < m := by
  simp [lt_def, BitVec.lt_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.lt_toNat_of_lt {n : UInt32} {m : Nat} (h : m < size) : ofNat m < n → m < n.toNat := by
  simp [lt_def, BitVec.lt_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.toNat_le_of_le {n : UInt32} {m : Nat} (h : m < size) : n ≤ ofNat m → n.toNat ≤ m := by
  simp [le_def, BitVec.le_def, UInt32.toNat, toBitVec_eq_of_lt h]

theorem UInt32.le_toNat_of_le {n : UInt32} {m : Nat} (h : m < size) : ofNat m ≤ n → m ≤ n.toNat := by
  simp [le_def, BitVec.le_def, UInt32.toNat, toBitVec_eq_of_lt h]
