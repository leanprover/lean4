/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, François G. Dorais, Mario Carneiro, Mac Malone, Markus Himmel
-/
prelude
import Init.Data.UInt.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast
import Init.Data.Nat.Div.Lemmas
import Init.System.Platform

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

  @[simp] theorem toNat_ofNat' {n : Nat} : (ofNat n).toNat = n % 2 ^ $bits := BitVec.toNat_ofNat ..

  -- Not `simp` because we have simprocs which will avoid the modulo.
  theorem toNat_ofNat {n : Nat} : toNat (no_index (OfNat.ofNat n)) = n % 2 ^ $bits := toNat_ofNat'

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

  @[deprecated "Use `toNat_toBitVec` and `toNat_ofNat_of_lt`." (since := "2025-03-05")]
  theorem toBitVec_eq_of_lt {a : Nat} : a < size → (ofNat a).toBitVec.toNat = a :=
    Nat.mod_eq_of_lt

  theorem toBitVec_ofNat' (n : Nat) : (ofNat n).toBitVec = BitVec.ofNat _ n := rfl

  theorem toNat_ofNat_of_lt' {n : Nat} (h : n < size) : (ofNat n).toNat = n := by
    rw [toNat, toBitVec_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  theorem toNat_ofNat_of_lt {n : Nat} (h : n < size) : toNat (OfNat.ofNat n) = n :=
    toNat_ofNat_of_lt' h

  @[int_toBitVec] theorem le_iff_toBitVec_le {a b : $typeName} : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl

  @[deprecated le_iff_toBitVec_le (since := "2025-03-20")]
  protected theorem le_def {a b : $typeName} : a ≤ b ↔ a.toBitVec ≤ b.toBitVec := .rfl

  @[int_toBitVec] theorem lt_iff_toBitVec_lt {a b : $typeName} : a < b ↔ a.toBitVec < b.toBitVec := .rfl

  @[deprecated lt_iff_toBitVec_lt (since := "2025-03-20")]
  protected theorem lt_def {a b : $typeName} : a < b ↔ a.toBitVec < b.toBitVec := .rfl

  theorem le_iff_toNat_le {a b : $typeName} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

  theorem lt_iff_toNat_lt {a b : $typeName} : a < b ↔ a.toNat < b.toNat := .rfl

  @[simp] protected theorem not_le {a b : $typeName} : ¬ a ≤ b ↔ b < a := by
    simp [le_iff_toBitVec_le, lt_iff_toBitVec_lt]

  @[simp] protected theorem not_lt {a b : $typeName} : ¬ a < b ↔ b ≤ a := by
    simp [le_iff_toBitVec_le, lt_iff_toBitVec_lt]

  @[simp] protected theorem le_refl (a : $typeName) : a ≤ a := by simp [le_iff_toBitVec_le]

  open $typeName (le_refl) in
  protected theorem le_rfl {a : $typeName} : a ≤ a := le_refl _

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
    simpa [lt_iff_toBitVec_lt] using h

  @[simp] protected theorem toNat_zero : (0 : $typeName).toNat = 0 := Nat.zero_mod _

  @[simp] protected theorem toNat_add (a b : $typeName) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ $bits := BitVec.toNat_add ..

  protected theorem toNat_sub (a b : $typeName) : (a - b).toNat = (2 ^ $bits - b.toNat + a.toNat) % 2 ^ $bits := BitVec.toNat_sub  ..

  @[simp] protected theorem toNat_mul (a b : $typeName) : (a * b).toNat = a.toNat * b.toNat % 2 ^ $bits := BitVec.toNat_mul  ..

  @[simp] protected theorem toNat_mod (a b : $typeName) : (a % b).toNat = a.toNat % b.toNat := BitVec.toNat_umod ..

  @[simp] protected theorem toNat_div (a b : $typeName) : (a / b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv  ..

  @[simp] protected theorem toNat_sub_of_le (a b : $typeName) : b ≤ a → (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le

  protected theorem toNat_lt_size (a : $typeName) : a.toNat < size := a.toBitVec.isLt

  open $typeName (toNat_mod toNat_lt_size) in
  protected theorem toNat_mod_lt {m : Nat} : ∀ (u : $typeName), 0 < m → toNat (u % ofNat m) < m := by
    intro u h1
    by_cases h2 : m < size
    · rw [toNat_mod, toNat_ofNat_of_lt' h2]
      apply Nat.mod_lt _ h1
    · apply Nat.lt_of_lt_of_le
      · apply toNat_lt_size
      · simpa using h2

  open $typeName (toNat_mod_lt modn) in
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
    simp only [lt_iff_toBitVec_lt, mod_def]
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

  @[simp, int_toBitVec] protected theorem toBitVec_add {a b : $typeName} : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
  @[simp, int_toBitVec] protected theorem toBitVec_sub {a b : $typeName} : (a - b).toBitVec = a.toBitVec - b.toBitVec := rfl
  @[simp, int_toBitVec] protected theorem toBitVec_mul {a b : $typeName} : (a * b).toBitVec = a.toBitVec * b.toBitVec := rfl
  @[simp, int_toBitVec] protected theorem toBitVec_div {a b : $typeName} : (a / b).toBitVec = a.toBitVec / b.toBitVec := rfl
  @[simp, int_toBitVec] protected theorem toBitVec_mod {a b : $typeName} : (a % b).toBitVec = a.toBitVec % b.toBitVec := rfl
  @[simp, int_toBitVec] protected theorem toBitVec_neg {a : $typeName} : (-a).toBitVec = -a.toBitVec := rfl

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

theorem UInt8.lt_ofNat_iff {n : UInt8} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt8.ofNat_lt_iff {n : UInt8} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt8.le_ofNat_iff {n : UInt8} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem UInt8.ofNat_le_iff {n : UInt8} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem UInt16.lt_ofNat_iff {n : UInt16} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt16.ofNat_lt_iff {n : UInt16} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt16.le_ofNat_iff {n : UInt16} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem UInt16.ofNat_le_iff {n : UInt16} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem UInt32.lt_ofNat_iff {n : UInt32} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt32.ofNat_lt_iff {n : UInt32} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt32.le_ofNat_iff {n : UInt32} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem UInt32.ofNat_le_iff {n : UInt32} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

@[deprecated UInt32.lt_ofNat_iff (since := "2025-03-18")]
theorem UInt32.toNat_lt_of_lt {n : UInt32} {m : Nat} (h : m < size) : n < ofNat m → n.toNat < m :=
  (UInt32.lt_ofNat_iff h).1

@[deprecated UInt32.ofNat_lt_iff (since := "2025-03-18")]
theorem UInt32.lt_toNat_of_lt {n : UInt32} {m : Nat} (h : m < size) : ofNat m < n → m < n.toNat :=
  (UInt32.ofNat_lt_iff h).1

@[deprecated UInt32.le_ofNat_iff (since := "2025-03-18")]
theorem UInt32.toNat_le_of_le {n : UInt32} {m : Nat} (h : m < size) : n ≤ ofNat m → n.toNat ≤ m :=
  (UInt32.le_ofNat_iff h).1

@[deprecated UInt32.ofNat_le_iff (since := "2025-03-18")]
theorem UInt32.le_toNat_of_le {n : UInt32} {m : Nat} (h : m < size) : ofNat m ≤ n → m ≤ n.toNat :=
  (UInt32.ofNat_le_iff h).1

theorem UInt64.lt_ofNat_iff {n : UInt64} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt64.ofNat_lt_iff {n : UInt64} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem UInt64.le_ofNat_iff {n : UInt64} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem UInt64.ofNat_le_iff {n : UInt64} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem USize.lt_ofNat_iff {n : USize} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem USize.ofNat_lt_iff {n : USize} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]
theorem USize.le_ofNat_iff {n : USize} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]
theorem USize.ofNat_le_iff {n : USize} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

protected theorem UInt8.mod_eq_of_lt {a b : UInt8} (h : a < b) : a % b = a := UInt8.toNat_inj.1 (Nat.mod_eq_of_lt h)
protected theorem UInt16.mod_eq_of_lt {a b : UInt16} (h : a < b) : a % b = a := UInt16.toNat_inj.1 (Nat.mod_eq_of_lt h)
protected theorem UInt32.mod_eq_of_lt {a b : UInt32} (h : a < b) : a % b = a := UInt32.toNat_inj.1 (Nat.mod_eq_of_lt h)
protected theorem UInt64.mod_eq_of_lt {a b : UInt64} (h : a < b) : a % b = a := UInt64.toNat_inj.1 (Nat.mod_eq_of_lt h)
protected theorem USize.mod_eq_of_lt {a b : USize} (h : a < b) : a % b = a := USize.toNat_inj.1 (Nat.mod_eq_of_lt h)

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
theorem USize.size_le_uint64Size : USize.size ≤ UInt64.size := by
  cases USize.size_eq <;> simp_all +decide

theorem UInt8.toNat_lt_usizeSize (n : UInt8) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)
theorem UInt16.toNat_lt_usizeSize (n : UInt16) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)
theorem UInt32.toNat_lt_usizeSize (n : UInt32) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)

theorem UInt8.size_dvd_usizeSize : UInt8.size ∣ USize.size := by cases USize.size_eq <;> simp_all +decide
theorem UInt16.size_dvd_usizeSize : UInt16.size ∣ USize.size := by cases USize.size_eq <;> simp_all +decide
theorem UInt32.size_dvd_usizeSize : UInt32.size ∣ USize.size := by cases USize.size_eq <;> simp_all +decide
theorem USize.size_dvd_uInt64Size : USize.size ∣ UInt64.size := by cases USize.size_eq <;> simp_all +decide

@[simp] theorem mod_usizeSize_uInt8Size (n : Nat) : n % USize.size % UInt8.size = n % UInt8.size :=
  Nat.mod_mod_of_dvd _ UInt8.size_dvd_usizeSize
@[simp] theorem mod_usizeSize_uInt16Size (n : Nat) : n % USize.size % UInt16.size = n % UInt16.size :=
  Nat.mod_mod_of_dvd _ UInt16.size_dvd_usizeSize
@[simp] theorem mod_usizeSize_uInt32Size (n : Nat) : n % USize.size % UInt32.size = n % UInt32.size :=
  Nat.mod_mod_of_dvd _ UInt32.size_dvd_usizeSize
@[simp] theorem mod_uInt64Size_uSizeSize (n : Nat) : n % UInt64.size % USize.size = n % USize.size :=
  Nat.mod_mod_of_dvd _ USize.size_dvd_uInt64Size

@[simp] theorem USize.size_sub_one_mod_uint8Size : (USize.size - 1) % UInt8.size = UInt8.size - 1 := by
  cases USize.size_eq <;> simp_all +decide
@[simp] theorem USize.size_sub_one_mod_uint16Size : (USize.size - 1) % UInt16.size = UInt16.size - 1 := by
  cases USize.size_eq <;> simp_all +decide
@[simp] theorem USize.size_sub_one_mod_uint32Size : (USize.size - 1) % UInt32.size = UInt32.size - 1 := by
  cases USize.size_eq <;> simp_all +decide
@[simp] theorem UInt64.size_sub_one_mod_uSizeSize : 18446744073709551615 % USize.size = USize.size - 1 := by
  cases USize.size_eq <;> simp_all +decide

@[simp] theorem UInt8.toNat_mod_size (n : UInt8) : n.toNat % UInt8.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt
@[simp] theorem UInt8.toNat_mod_uInt16Size (n : UInt8) : n.toNat % UInt16.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt8.toNat_mod_uInt32Size (n : UInt8) : n.toNat % UInt32.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt8.toNat_mod_uInt64Size (n : UInt8) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt8.toNat_mod_uSizeSize (n : UInt8) : n.toNat % USize.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt_usizeSize

@[simp] theorem UInt16.toNat_mod_size (n : UInt16) : n.toNat % UInt16.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt
@[simp] theorem UInt16.toNat_mod_uInt32Size (n : UInt16) : n.toNat % UInt32.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt16.toNat_mod_uInt64Size (n : UInt16) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt16.toNat_mod_uSizeSize (n : UInt16) : n.toNat % USize.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt_usizeSize

@[simp] theorem UInt32.toNat_mod_size (n : UInt32) : n.toNat % UInt32.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt
@[simp] theorem UInt32.toNat_mod_uInt64Size (n : UInt32) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
@[simp] theorem UInt32.toNat_mod_uSizeSize (n : UInt32) : n.toNat % USize.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt_usizeSize

@[simp] theorem UInt64.toNat_mod_size (n : UInt64) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem USize.toNat_mod_size (n : USize) : n.toNat % USize.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt_size
@[simp] theorem USize.toNat_mod_uInt64Size (n : USize) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem UInt8.toUInt16_mod_256 (n : UInt8) : n.toUInt16 % 256 = n.toUInt16 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt32_mod_256 (n : UInt8) : n.toUInt32 % 256 = n.toUInt32 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt64_mod_256 (n : UInt8) : n.toUInt64 % 256 = n.toUInt64 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt8.toUSize_mod_256 (n : UInt8) : n.toUSize % 256 = n.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_mod_65536 (n : UInt16) : n.toUInt32 % 65536 = n.toUInt32 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt64_mod_65536 (n : UInt16) : n.toUInt64 % 65536 = n.toUInt64 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt16.toUSize_mod_65536 (n : UInt16) : n.toUSize % 65536 = n.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt64_mod_4294967296 (n : UInt32) : n.toUInt64 % 4294967296 = n.toUInt64 := UInt64.toNat.inj (by simp)

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

@[simp] theorem USize.toFin_toUInt64 (n : USize) : n.toUInt64.toFin = n.toFin.castLE size_le_uint64Size := rfl

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
  BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt8.toBitVec_toUSize (n : UInt8) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem UInt16.toBitVec_toUSize (n : UInt16) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem UInt32.toBitVec_toUSize (n : UInt32) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)
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

@[simp] theorem UInt8.toFin_ofFin (n : Fin UInt8.size) : (UInt8.ofFin n).toFin = n := rfl
@[simp] theorem UInt16.toFin_ofFin (n : Fin UInt16.size) : (UInt16.ofFin n).toFin = n := rfl
@[simp] theorem UInt32.toFin_ofFin (n : Fin UInt32.size) : (UInt32.ofFin n).toFin = n := rfl
@[simp] theorem UInt64.toFin_ofFin (n : Fin UInt64.size) : (UInt64.ofFin n).toFin = n := rfl
@[simp] theorem USize.toFin_ofFin (n : Fin USize.size) : (USize.ofFin n).toFin = n := rfl

@[simp] theorem UInt16.ofFin_uint8ToFin (n : UInt8) : UInt16.ofFin (n.toFin.castLE (by decide)) = n.toUInt16 := rfl

@[simp] theorem UInt32.ofFin_uint8ToFin (n : UInt8) : UInt32.ofFin (n.toFin.castLE (by decide)) = n.toUInt32 := rfl
@[simp] theorem UInt32.ofFin_uint16ToFin (n : UInt16) : UInt32.ofFin (n.toFin.castLE (by decide)) = n.toUInt32 := rfl

@[simp] theorem UInt64.ofFin_uint8ToFin (n : UInt8) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofFin_uint16ToFin (n : UInt16) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofFin_uint32ToFin (n : UInt32) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := rfl

@[simp] theorem USize.ofFin_uint8ToFin (n : UInt8) : USize.ofFin (n.toFin.castLE UInt8.size_le_usizeSize) = n.toUSize := rfl
@[simp] theorem USize.ofFin_uint16ToFin (n : UInt16) : USize.ofFin (n.toFin.castLE UInt16.size_le_usizeSize) = n.toUSize := rfl
@[simp] theorem USize.ofFin_uint32ToFin (n : UInt32) : USize.ofFin (n.toFin.castLE UInt32.size_le_usizeSize) = n.toUSize := rfl

@[simp] theorem Nat.toUInt8_eq {n : Nat} : n.toUInt8 = UInt8.ofNat n := rfl
@[simp] theorem Nat.toUInt16_eq {n : Nat} : n.toUInt16 = UInt16.ofNat n := rfl
@[simp] theorem Nat.toUInt32_eq {n : Nat} : n.toUInt32 = UInt32.ofNat n := rfl
@[simp] theorem Nat.toUInt64_eq {n : Nat} : n.toUInt64 = UInt64.ofNat n := rfl
@[simp] theorem Nat.toUSize_eq {n : Nat} : n.toUSize = USize.ofNat n := rfl

@[simp] theorem UInt8.ofBitVec_uInt16ToBitVec (n : UInt16) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := rfl
@[simp] theorem UInt8.ofBitVec_uInt32ToBitVec (n : UInt32) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := rfl
@[simp] theorem UInt8.ofBitVec_uInt64ToBitVec (n : UInt64) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := rfl
@[simp] theorem UInt8.ofBitVec_uSizeToBitVec (n : USize) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem UInt16.ofBitVec_uInt8ToBitVec (n : UInt8) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := rfl
@[simp] theorem UInt16.ofBitVec_uInt32ToBitVec (n : UInt32) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := rfl
@[simp] theorem UInt16.ofBitVec_uInt64ToBitVec (n : UInt64) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := rfl
@[simp] theorem UInt16.ofBitVec_uSizeToBitVec (n : USize) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt32.ofBitVec_uInt8ToBitVec (n : UInt8) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := rfl
@[simp] theorem UInt32.ofBitVec_uInt16ToBitVec (n : UInt16) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := rfl
@[simp] theorem UInt32.ofBitVec_uInt64ToBitVec (n : UInt64) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := rfl
@[simp] theorem UInt32.ofBitVec_uSizeToBitVec (n : USize) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.ofBitVec_uInt8ToBitVec (n : UInt8) :
    UInt64.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofBitVec_uInt16ToBitVec (n : UInt16) :
    UInt64.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofBitVec_uInt32ToBitVec (n : UInt32) :
    UInt64.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt64 := rfl
@[simp] theorem UInt64.ofBitVec_uSizeToBitVec (n : USize) :
    UInt64.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt64 :=
  UInt64.toNat.inj (by simp)

@[simp] theorem USize.ofBitVec_uInt8ToBitVec (n : UInt8) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofBitVec_uInt16ToBitVec (n : UInt16) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofBitVec_uInt32ToBitVec (n : UInt32) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofBitVec_uInt64ToBitVec (n : UInt64) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt8.ofNat_uInt16ToNat (n : UInt16) : UInt8.ofNat n.toNat = n.toUInt8 := rfl
@[simp] theorem UInt8.ofNat_uInt32ToNat (n : UInt32) : UInt8.ofNat n.toNat = n.toUInt8 := rfl
@[simp] theorem UInt8.ofNat_uInt64ToNat (n : UInt64) : UInt8.ofNat n.toNat = n.toUInt8 := rfl
@[simp] theorem UInt8.ofNat_uSizeToNat (n : USize) : UInt8.ofNat n.toNat = n.toUInt8 := rfl

@[simp] theorem UInt16.ofNat_uInt8ToNat (n : UInt8) : UInt16.ofNat n.toNat = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt16.ofNat_uInt32ToNat (n : UInt32) : UInt16.ofNat n.toNat = n.toUInt16 := rfl
@[simp] theorem UInt16.ofNat_uInt64ToNat (n : UInt64) : UInt16.ofNat n.toNat = n.toUInt16 := rfl
@[simp] theorem UInt16.ofNat_uSizeToNat (n : USize) : UInt16.ofNat n.toNat = n.toUInt16 := rfl

@[simp] theorem UInt32.ofNat_uInt8ToNat (n : UInt8) : UInt32.ofNat n.toNat = n.toUInt32 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt32.ofNat_uInt16ToNat (n : UInt16) : UInt32.ofNat n.toNat = n.toUInt32 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt32.ofNat_uInt64ToNat (n : UInt64) : UInt32.ofNat n.toNat = n.toUInt32 := rfl
@[simp] theorem UInt32.ofNat_uSizeToNat (n : USize) : UInt32.ofNat n.toNat = n.toUInt32 := rfl

@[simp] theorem UInt64.ofNat_uInt8ToNat (n : UInt8) : UInt64.ofNat n.toNat = n.toUInt64 :=
  UInt64.toNat.inj (by simp)
@[simp] theorem UInt64.ofNat_uInt16ToNat (n : UInt16) : UInt64.ofNat n.toNat = n.toUInt64 :=
  UInt64.toNat.inj (by simp)
@[simp] theorem UInt64.ofNat_uInt32ToNat (n : UInt32) : UInt64.ofNat n.toNat = n.toUInt64 :=
  UInt64.toNat.inj (by simp)
@[simp] theorem UInt64.ofNat_uSizeToNat (n : USize) : UInt64.ofNat n.toNat = n.toUInt64 :=
  UInt64.toNat.inj (by simp)

@[simp] theorem USize.ofNat_uInt8ToNat (n : UInt8) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofNat_uInt16ToNat (n : UInt16) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofNat_uInt32ToNat (n : UInt32) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.ofNat_uInt64ToNat (n : UInt64) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)

theorem UInt8.ofNatLT_eq_ofNat (n : Nat) {h} : UInt8.ofNatLT n h = UInt8.ofNat n :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt16.ofNatLT_eq_ofNat (n : Nat) {h} : UInt16.ofNatLT n h = UInt16.ofNat n :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt32.ofNatLT_eq_ofNat (n : Nat) {h} : UInt32.ofNatLT n h = UInt32.ofNat n :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem UInt64.ofNatLT_eq_ofNat (n : Nat) {h} : UInt64.ofNatLT n h = UInt64.ofNat n :=
  UInt64.toNat.inj (by simp [Nat.mod_eq_of_lt h])
theorem USize.ofNatLT_eq_ofNat (n : Nat) {h} : USize.ofNatLT n h = USize.ofNat n :=
  USize.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt8.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt8.size) :
    UInt8.ofNatTruncate n = UInt8.ofNat n := by
  simp [ofNatTruncate, hn, UInt8.ofNatLT_eq_ofNat]
theorem UInt16.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt16.size) :
    UInt16.ofNatTruncate n = UInt16.ofNat n := by
  simp [ofNatTruncate, hn, UInt16.ofNatLT_eq_ofNat]
theorem UInt32.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt32.size) :
    UInt32.ofNatTruncate n = UInt32.ofNat n := by
  simp [ofNatTruncate, hn, UInt32.ofNatLT_eq_ofNat]
theorem UInt64.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt64.size) :
    UInt64.ofNatTruncate n = UInt64.ofNat n := by
  simp [ofNatTruncate, hn, UInt64.ofNatLT_eq_ofNat]
theorem USize.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < USize.size) :
    USize.ofNatTruncate n = USize.ofNat n := by
  simp [ofNatTruncate, hn, USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofNatTruncate_toNat (n : UInt8) : UInt8.ofNatTruncate n.toNat = n := by
  rw [UInt8.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem UInt16.ofNatTruncate_uInt8ToNat (n : UInt8) : UInt16.ofNatTruncate n.toNat = n.toUInt16 := by
  rw [UInt16.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt16.ofNatTruncate_toNat (n : UInt16) : UInt16.ofNatTruncate n.toNat = n := by
  rw [UInt16.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem UInt32.ofNatTruncate_uInt8ToNat (n : UInt8) : UInt32.ofNatTruncate n.toNat = n.toUInt32 := by
  rw [UInt32.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt32.ofNatTruncate_uInt16ToNat (n : UInt16) : UInt32.ofNatTruncate n.toNat = n.toUInt32 := by
  rw [UInt32.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt32.ofNatTruncate_toNat (n : UInt32) : UInt32.ofNatTruncate n.toNat = n := by
  rw [UInt32.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem UInt64.ofNatTruncate_uInt8ToNat (n : UInt8) : UInt64.ofNatTruncate n.toNat = n.toUInt64 := by
  rw [UInt64.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt64.ofNatTruncate_uInt16ToNat (n : UInt16) : UInt64.ofNatTruncate n.toNat = n.toUInt64 := by
  rw [UInt64.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt64.ofNatTruncate_uInt32ToNat (n : UInt32) : UInt64.ofNatTruncate n.toNat = n.toUInt64 := by
  rw [UInt64.ofNatTruncate_eq_ofNat, ofNat_uInt32ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)
@[simp] theorem UInt64.ofNatTruncate_toNat (n : UInt64) : UInt64.ofNatTruncate n.toNat = n := by
  rw [UInt64.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]
@[simp] theorem UInt64.ofNatTruncate_uSizeToNat (n : USize) : UInt64.ofNatTruncate n.toNat = n.toUInt64 := by
  rw [UInt64.ofNatTruncate_eq_ofNat, ofNat_uSizeToNat]
  exact n.toNat_lt

@[simp] theorem USize.ofNatTruncate_uInt8ToNat (n : UInt8) : USize.ofNatTruncate n.toNat = n.toUSize := by
  rw [USize.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact n.toNat_lt_usizeSize
@[simp] theorem USize.ofNatTruncate_uInt16ToNat (n : UInt16) : USize.ofNatTruncate n.toNat = n.toUSize := by
  rw [USize.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact n.toNat_lt_usizeSize
@[simp] theorem USize.ofNatTruncate_uInt32ToNat (n : UInt32) : USize.ofNatTruncate n.toNat = n.toUSize := by
  rw [USize.ofNatTruncate_eq_ofNat, ofNat_uInt32ToNat]
  exact n.toNat_lt_usizeSize
@[simp] theorem USize.ofNatTruncate_toNat (n : USize) : USize.ofNatTruncate n.toNat = n := by
  rw [USize.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt_size]

@[simp] theorem UInt8.toUInt8_toUInt16 (n : UInt8) : n.toUInt16.toUInt8 = n :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt8_toUInt32 (n : UInt8) : n.toUInt32.toUInt8 = n :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt8_toUInt64 (n : UInt8) : n.toUInt64.toUInt8 = n :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt8_toUSize (n : UInt8) : n.toUSize.toUInt8 = n :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_toUInt32 (n : UInt8) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt16_toUInt64 (n : UInt8) : n.toUInt64.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt16_toUSize (n : UInt8) : n.toUSize.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt32_toUInt16 (n : UInt8) : n.toUInt16.toUInt32 = n.toUInt32 := rfl
@[simp] theorem UInt8.toUInt32_toUInt64 (n : UInt8) : n.toUInt64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt32_toUSize (n : UInt8) : n.toUSize.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt64_toUInt16 (n : UInt8) : n.toUInt16.toUInt64 = n.toUInt64 := rfl
@[simp] theorem UInt8.toUInt64_toUInt32 (n : UInt8) : n.toUInt32.toUInt64 = n.toUInt64 := rfl
@[simp] theorem UInt8.toUInt64_toUSize (n : UInt8) : n.toUSize.toUInt64 = n.toUInt64 := rfl

@[simp] theorem UInt8.toUSize_toUInt16 (n : UInt8) : n.toUInt16.toUSize = n.toUSize := rfl
@[simp] theorem UInt8.toUSize_toUInt32 (n : UInt8) : n.toUInt32.toUSize = n.toUSize := rfl
@[simp] theorem UInt8.toUSize_toUInt64 (n : UInt8) : n.toUInt64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt8_toUInt32 (n : UInt16) : n.toUInt32.toUInt8 = n.toUInt8 := rfl
@[simp] theorem UInt16.toUInt8_toUInt64 (n : UInt16) : n.toUInt64.toUInt8 = n.toUInt8 := rfl
@[simp] theorem UInt16.toUInt8_toUSize (n : UInt16) : n.toUSize.toUInt8 = n.toUInt8 := rfl

@[simp] theorem UInt16.toUInt16_toUInt8 (n : UInt16) : n.toUInt8.toUInt16 = n % 256 := rfl
@[simp] theorem UInt16.toUInt16_toUInt32 (n : UInt16) : n.toUInt32.toUInt16 = n :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt16_toUInt64 (n : UInt16) : n.toUInt64.toUInt16 = n :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt16_toUSize (n : UInt16) : n.toUSize.toUInt16 = n :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_toUInt8 (n : UInt16) : n.toUInt8.toUInt32 = n.toUInt32 % 256 := rfl
@[simp] theorem UInt16.toUInt32_toUInt64 (n : UInt16) : n.toUInt64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt32_toUSize (n : UInt16) : n.toUSize.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt64_toUInt8 (n : UInt16) : n.toUInt8.toUInt64 = n.toUInt64 % 256 := rfl
@[simp] theorem UInt16.toUInt64_toUInt32 (n : UInt16) : n.toUInt32.toUInt64 = n.toUInt64 := rfl
@[simp] theorem UInt16.toUInt64_toUSize (n : UInt16) : n.toUSize.toUInt64 = n.toUInt64 := rfl

@[simp] theorem UInt16.toUSize_toUInt8 (n : UInt16) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)
@[simp] theorem UInt16.toUSize_toUInt32 (n : UInt16) : n.toUInt32.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)
@[simp] theorem UInt16.toUSize_toUInt64 (n : UInt16) : n.toUInt64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt8_toUInt16 (n : UInt32) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt8_toUInt64 (n : UInt32) : n.toUInt64.toUInt8 = n.toUInt8 := rfl
@[simp] theorem UInt32.toUInt8_toUSize (n : UInt32) : n.toUSize.toUInt8 = n.toUInt8 := rfl

@[simp] theorem UInt32.toUInt16_toUInt8 (n : UInt32) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt16_toUInt64 (n : UInt32) : n.toUInt64.toUInt16 = n.toUInt16 := rfl
@[simp] theorem UInt32.toUInt16_toUSize (n : UInt32) : n.toUSize.toUInt16 = n.toUInt16 := rfl

@[simp] theorem UInt32.toUInt32_toUInt8 (n : UInt32) : n.toUInt8.toUInt32 = n % 256 := rfl
@[simp] theorem UInt32.toUInt32_toUInt16 (n : UInt32) : n.toUInt16.toUInt32 = n % 65536 := rfl
@[simp] theorem UInt32.toUInt32_toUInt64 (n : UInt32) : n.toUInt64.toUInt32 = n :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt32_toUSize (n : UInt32) : n.toUSize.toUInt32 = n :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt64_toUInt8 (n : UInt32) : n.toUInt8.toUInt64 = n.toUInt64 % 256 := rfl
@[simp] theorem UInt32.toUInt64_toUInt16 (n : UInt32) : n.toUInt16.toUInt64 = n.toUInt64 % 65536 := rfl
@[simp] theorem UInt32.toUInt64_toUSize (n : UInt32) : n.toUSize.toUInt64 = n.toUInt64 := rfl

@[simp] theorem UInt32.toUSize_toUInt8 (n : UInt32) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)
@[simp] theorem UInt32.toUSize_toUInt16 (n : UInt32) : n.toUInt16.toUSize = n.toUSize % 65536 :=
  USize.toNat.inj (by simp)
@[simp] theorem UInt32.toUSize_toUInt64 (n : UInt32) : n.toUInt64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt8_toUInt16 (n : UInt64) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt8_toUInt32 (n : UInt64) : n.toUInt32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt8_toUSize (n : UInt64) : n.toUSize.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt16_toUInt8 (n : UInt64) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt16_toUInt32 (n : UInt64) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt16_toUSize (n : UInt64) : n.toUSize.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt32_toUInt8 (n : UInt64) : n.toUInt8.toUInt32 = n.toUInt32 % 256 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt32_toUInt16 (n : UInt64) : n.toUInt16.toUInt32 = n.toUInt32 % 65536 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt32_toUSize (n : UInt64) : n.toUSize.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt64_toUInt8 (n : UInt64) : n.toUInt8.toUInt64 = n % 256 := rfl
@[simp] theorem UInt64.toUInt64_toUInt16 (n : UInt64) : n.toUInt16.toUInt64 = n % 65536 := rfl
@[simp] theorem UInt64.toUInt64_toUInt32 (n : UInt64) : n.toUInt32.toUInt64 = n % 4294967296 := rfl

@[simp] theorem UInt64.toUSize_toUInt8 (n : UInt64) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)
@[simp] theorem UInt64.toUSize_toUInt16 (n : UInt64) : n.toUInt16.toUSize = n.toUSize % 65536 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize.toUInt8_toUInt16 (n : USize) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem USize.toUInt8_toUInt32 (n : USize) : n.toUInt32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)
@[simp] theorem USize.toUInt8_toUInt64 (n : USize) : n.toUInt64.toUInt8 = n.toUInt8 := rfl

@[simp] theorem USize.toUInt16_toUInt8 (n : USize) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem USize.toUInt16_toUInt32 (n : USize) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)
@[simp] theorem USize.toUInt16_toUInt64 (n : USize) : n.toUInt64.toUInt16 = n.toUInt16 := rfl

@[simp] theorem USize.toUInt64_toUInt8 (n : USize) : n.toUInt8.toUInt64 = n.toUInt64 % 256 := rfl
@[simp] theorem USize.toUInt64_toUInt16 (n : USize) : n.toUInt16.toUInt64 = n.toUInt64 % 65536 := rfl

@[simp] theorem USize.toUInt32_toUInt8 (n : USize) : n.toUInt8.toUInt32 = n.toUInt32 % 256 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem USize.toUInt32_toUInt16 (n : USize) : n.toUInt16.toUInt32 = n.toUInt32 % 65536 :=
  UInt32.toNat.inj (by simp)
@[simp] theorem USize.toUInt32_toUInt64 (n : USize) : n.toUInt64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize.toUSize_toUInt8 (n : USize) : n.toUInt8.toUSize = n % 256 :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.toUSize_toUInt16 (n : USize) : n.toUInt16.toUSize = n % 65536 :=
  USize.toNat.inj (by simp)
@[simp] theorem USize.toUSize_toUInt64 (n : USize) : n.toUInt64.toUSize = n :=
  USize.toNat.inj (by simp)

@[simp] theorem USize.toUSize_toUInt32 (n : USize) : n.toUInt32.toUSize = n % 4294967296 := by
  apply USize.toNat.inj
  simp only [UInt32.toNat_toUSize, toNat_toUInt32, Nat.reducePow, USize.toNat_mod]
  cases USize.size_eq
  · next h => rw [Nat.mod_eq_of_lt (h ▸ n.toNat_lt_size), USize.toNat_ofNat,
      ← USize.size_eq_two_pow, h, Nat.mod_self, Nat.mod_zero]
  · next h => rw [USize.toNat_ofNat_of_lt]; simp_all

-- Note: we are currently missing the following four results for which there does not seem to
-- be a good candidate for the RHS:
-- @[simp] theorem UInt64.toUInt64_toUSize (n : UInt64) : n.toUSize.toUInt64 = ? :=
-- @[simp] theorem UInt64.toUSize_toUInt32 (n : UInt64) : n.toUInt32.toUSize = ? :=
-- @[simp] theorem USize.toUInt64_toUInt32 (n : USize) : n.toUInt32.toUInt64 = ? :=

@[simp] theorem UInt8.toNat_ofFin (x : Fin UInt8.size) : (UInt8.ofFin x).toNat = x.val := rfl
@[simp] theorem UInt16.toNat_ofFin (x : Fin UInt16.size) : (UInt16.ofFin x).toNat = x.val := rfl
@[simp] theorem UInt32.toNat_ofFin (x : Fin UInt32.size) : (UInt32.ofFin x).toNat = x.val := rfl
@[simp] theorem UInt64.toNat_ofFin (x : Fin UInt64.size) : (UInt64.ofFin x).toNat = x.val := rfl
@[simp] theorem USize.toNat_ofFin (x : Fin USize.size) : (USize.ofFin x).toNat = x.val := rfl

theorem UInt8.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toNat = n := by rw [UInt8.ofNatTruncate, dif_pos hn, toNat_ofNatLT]
theorem UInt16.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toNat = n := by rw [UInt16.ofNatTruncate, dif_pos hn, toNat_ofNatLT]
theorem UInt32.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toNat = n := by rw [UInt32.ofNatTruncate, dif_pos hn, toNat_ofNatLT]
theorem UInt64.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toNat = n := by rw [UInt64.ofNatTruncate, dif_pos hn, toNat_ofNatLT]
theorem USize.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toNat = n := by rw [USize.ofNatTruncate, dif_pos hn, toNat_ofNatLT]

theorem UInt8.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toNat = UInt8.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]
theorem UInt16.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toNat = UInt16.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]
theorem UInt32.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toNat = UInt32.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]
theorem UInt64.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toNat = UInt64.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]
theorem USize.toNat_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toNat = USize.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]

@[simp] theorem UInt8.toFin_ofNatLT {n : Nat} (hn) : (UInt8.ofNatLT n hn).toFin = ⟨n, hn⟩ := rfl
@[simp] theorem UInt16.toFin_ofNatLT {n : Nat} (hn) : (UInt16.ofNatLT n hn).toFin = ⟨n, hn⟩ := rfl
@[simp] theorem UInt32.toFin_ofNatLT {n : Nat} (hn) : (UInt32.ofNatLT n hn).toFin = ⟨n, hn⟩ := rfl
@[simp] theorem UInt64.toFin_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toFin = ⟨n, hn⟩ := rfl
@[simp] theorem USize.toFin_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toFin = ⟨n, hn⟩ := rfl

@[simp] theorem UInt8.toFin_ofNat' {n : Nat} : (UInt8.ofNat n).toFin = Fin.ofNat' _ n := rfl
@[simp] theorem UInt16.toFin_ofNat' {n : Nat} : (UInt16.ofNat n).toFin = Fin.ofNat' _ n := rfl
@[simp] theorem UInt32.toFin_ofNat' {n : Nat} : (UInt32.ofNat n).toFin = Fin.ofNat' _ n := rfl
@[simp] theorem UInt64.toFin_ofNat' {n : Nat} : (UInt64.ofNat n).toFin = Fin.ofNat' _ n := rfl
@[simp] theorem USize.toFin_ofNat' {n : Nat} : (USize.ofNat n).toFin = Fin.ofNat' _ n := rfl

@[simp] theorem UInt8.toFin_ofBitVec {b} : (UInt8.ofBitVec b).toFin = b.toFin := rfl
@[simp] theorem UInt16.toFin_ofBitVec {b} : (UInt16.ofBitVec b).toFin = b.toFin := rfl
@[simp] theorem UInt32.toFin_ofBitVec {b} : (UInt32.ofBitVec b).toFin = b.toFin := rfl
@[simp] theorem UInt64.toFin_ofBitVec {b} : (UInt64.ofBitVec b).toFin = b.toFin := rfl
@[simp] theorem USize.toFin_ofBitVec {b} : (USize.ofBitVec b).toFin = b.toFin := rfl

theorem UInt8.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt16.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt32.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt64.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])
theorem USize.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toFin = ⟨UInt8.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt16.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toFin = ⟨UInt16.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt32.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toFin = ⟨UInt32.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt64.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toFin = ⟨UInt64.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])
theorem USize.toFin_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toFin = ⟨USize.size - 1, by cases USize.size_eq <;> simp_all⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt8.toBitVec_ofNatLT {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := rfl
@[simp] theorem UInt16.toBitVec_ofNatLT {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := rfl
@[simp] theorem UInt32.toBitVec_ofNatLT {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := rfl
@[simp] theorem UInt64.toBitVec_ofNatLT {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := rfl
@[simp] theorem USize.toBitVec_ofNatLT {n : Nat} (hn : n < USize.size) :
    (USize.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := rfl

@[simp] theorem UInt8.toBitVec_ofFin (n : Fin UInt8.size) : (UInt8.ofFin n).toBitVec = BitVec.ofFin n := rfl
@[simp] theorem UInt16.toBitVec_ofFin (n : Fin UInt16.size) : (UInt16.ofFin n).toBitVec = BitVec.ofFin n := rfl
@[simp] theorem UInt32.toBitVec_ofFin (n : Fin UInt32.size) : (UInt32.ofFin n).toBitVec = BitVec.ofFin n := rfl
@[simp] theorem UInt64.toBitVec_ofFin (n : Fin UInt64.size) : (UInt64.ofFin n).toBitVec = BitVec.ofFin n := rfl
@[simp] theorem USize.toBitVec_ofFin (n : Fin USize.size) : (USize.ofFin n).toBitVec = BitVec.ofFin n := rfl

@[simp] theorem UInt8.toBitVec_ofBitVec (n) : (UInt8.ofBitVec n).toBitVec = n := rfl
@[simp] theorem UInt16.toBitVec_ofBitVec (n) : (UInt16.ofBitVec n).toBitVec = n := rfl
@[simp] theorem UInt32.toBitVec_ofBitVec (n) : (UInt32.ofBitVec n).toBitVec = n := rfl
@[simp] theorem UInt64.toBitVec_ofBitVec (n) : (UInt64.ofBitVec n).toBitVec = n := rfl
@[simp] theorem USize.toBitVec_ofBitVec (n) : (USize.ofBitVec n).toBitVec = n := rfl

theorem UInt8.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt16.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt32.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt64.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])
theorem USize.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt8.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt16.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt16.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt32.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt32.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt64.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt64.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])
theorem USize.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toBitVec = BitVec.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt16.toUInt8_ofNatLT {n : Nat} (hn) : (UInt16.ofNatLT n hn).toUInt8 = UInt8.ofNat n := rfl
@[simp] theorem UInt32.toUInt8_ofNatLT {n : Nat} (hn) : (UInt32.ofNatLT n hn).toUInt8 = UInt8.ofNat n := rfl
@[simp] theorem UInt64.toUInt8_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toUInt8 = UInt8.ofNat n := rfl
@[simp] theorem USize.toUInt8_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toUInt8 = UInt8.ofNat n := rfl

@[simp] theorem UInt16.toUInt8_ofFin (n) : (UInt16.ofFin n).toUInt8 = UInt8.ofNat n.val := rfl
@[simp] theorem UInt32.toUInt8_ofFin (n) : (UInt32.ofFin n).toUInt8 = UInt8.ofNat n.val := rfl
@[simp] theorem UInt64.toUInt8_ofFin (n) : (UInt64.ofFin n).toUInt8 = UInt8.ofNat n.val := rfl
@[simp] theorem USize.toUInt8_ofFin (n) : (USize.ofFin n).toUInt8 = UInt8.ofNat n.val := rfl

@[simp] theorem UInt16.toUInt8_ofBitVec (b) : (UInt16.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt32.toUInt8_ofBitVec (b) : (UInt32.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt64.toUInt8_ofBitVec (b) : (UInt64.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := rfl
@[simp] theorem USize.toUInt8_ofBitVec (b) : (USize.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt8_ofNat' (n : Nat) : (UInt16.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt8_ofNat' (n : Nat) : (UInt32.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt8_ofNat' (n : Nat) : (UInt64.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)
@[simp] theorem USize.toUInt8_ofNat' (n : Nat) : (USize.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _
@[simp] theorem UInt32.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _
@[simp] theorem UInt64.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _
@[simp] theorem USize.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _

theorem UInt16.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]
theorem UInt32.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]
theorem UInt64.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]
theorem USize.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]

theorem UInt16.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt32.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt64.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem USize.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt32.toUInt16_ofNatLT {n : Nat} (hn) : (UInt32.ofNatLT n hn).toUInt16 = UInt16.ofNat n := rfl
@[simp] theorem UInt64.toUInt16_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toUInt16 = UInt16.ofNat n := rfl
@[simp] theorem USize.toUInt16_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toUInt16 = UInt16.ofNat n := rfl

@[simp] theorem UInt32.toUInt16_ofFin (n) : (UInt32.ofFin n).toUInt16 = UInt16.ofNat n.val := rfl
@[simp] theorem UInt64.toUInt16_ofFin (n) : (UInt64.ofFin n).toUInt16 = UInt16.ofNat n.val := rfl
@[simp] theorem USize.toUInt16_ofFin (n) : (USize.ofFin n).toUInt16 = UInt16.ofNat n.val := rfl

@[simp] theorem UInt32.toUInt16_ofBitVec (b) : (UInt32.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt64.toUInt16_ofBitVec (b) : (UInt64.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := rfl
@[simp] theorem USize.toUInt16_ofBitVec (b) : (USize.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt16_ofNat' (n : Nat) : (UInt32.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt16_ofNat' (n : Nat) : (UInt64.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)
@[simp] theorem USize.toUInt16_ofNat' (n : Nat) : (USize.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt32.toUInt16_ofNat' _
@[simp] theorem UInt64.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt64.toUInt16_ofNat' _
@[simp] theorem USize.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize.toUInt16_ofNat' _

theorem UInt32.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]
theorem UInt64.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]
theorem USize.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]

theorem UInt32.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt64.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem USize.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt64.toUInt32_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toUInt32 = UInt32.ofNat n := rfl
@[simp] theorem USize.toUInt32_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toUInt32 = UInt32.ofNat n := rfl

@[simp] theorem UInt64.toUInt32_ofFin (n) : (UInt64.ofFin n).toUInt32 = UInt32.ofNat n.val := rfl
@[simp] theorem USize.toUInt32_ofFin (n) : (USize.ofFin n).toUInt32 = UInt32.ofNat n.val := rfl

@[simp] theorem UInt64.toUInt32_ofBitVec (b) : (UInt64.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) := rfl
@[simp] theorem USize.toUInt32_ofBitVec (b) : (USize.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt32_ofNat' (n : Nat) : (UInt64.ofNat n).toUInt32 = UInt32.ofNat n := UInt32.toNat.inj (by simp)
@[simp] theorem USize.toUInt32_ofNat' (n : Nat) : (USize.ofNat n).toUInt32 = UInt32.ofNat n := UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt32_ofNat {n : Nat} : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt64.toUInt32_ofNat' _
@[simp] theorem USize.toUInt32_ofNat {n : Nat} : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize.toUInt32_ofNat' _

theorem UInt64.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toUInt32 = UInt32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt32_ofNatLT]
theorem USize.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUInt32 = UInt32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt32_ofNatLT]

theorem UInt64.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem USize.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt64.toUSize_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toUSize = USize.ofNat n := rfl

@[simp] theorem UInt64.toUSize_ofFin (n) : (UInt64.ofFin n).toUSize = USize.ofNat n.val := rfl

@[simp] theorem UInt64.toUSize_ofBitVec (b) : (UInt64.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize_ofNat' (n : Nat) : (UInt64.ofNat n).toUSize = USize.ofNat n := USize.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize_ofNat {n : Nat} : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt64.toUSize_ofNat' _

theorem UInt64.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toUSize = USize.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize_ofNatLT]

theorem UInt64.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toUSize = USize.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt8.toUInt16_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUInt16 = UInt16.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt8.toUInt32_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUInt32 = UInt32.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt8.toUInt64_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt8.toUSize_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le h size_le_usizeSize) := rfl

theorem UInt8.toUInt16_ofFin {n} :
  (UInt8.ofFin n).toUInt16 = UInt16.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt8.toUInt32_ofFin {n} :
  (UInt8.ofFin n).toUInt32 = UInt32.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt8.toUInt64_ofFin {n} :
  (UInt8.ofFin n).toUInt64 = UInt64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt8.toUSize_ofFin {n} :
  (UInt8.ofFin n).toUSize = USize.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_usizeSize) := rfl

@[simp] theorem UInt8.toUInt16_ofBitVec {b} : (UInt8.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt8.toUInt32_ofBitVec {b} : (UInt8.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt8.toUInt64_ofBitVec {b} : (UInt8.ofBitVec b).toUInt64 = UInt64.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt8.toUSize_ofBitVec {b} : (UInt8.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toBitVec_inj.1 (by simp)

theorem UInt8.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUInt16 = UInt16.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt8.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUInt32 = UInt32.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt8.toUInt64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt8.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt8.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt8.toUInt64_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUInt64 = UInt64.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt8.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUSize = USize.ofNatLT (UInt8.size - 1) (Nat.lt_of_lt_of_le (by decide) size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt16.toUInt32_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUInt32 = UInt32.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt16.toUInt64_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt16.toUSize_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le h size_le_usizeSize) := rfl

theorem UInt16.toUInt32_ofFin {n} :
  (UInt16.ofFin n).toUInt32 = UInt32.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt16.toUInt64_ofFin {n} :
  (UInt16.ofFin n).toUInt64 = UInt64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt16.toUSize_ofFin {n} :
  (UInt16.ofFin n).toUSize = USize.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_usizeSize) := rfl

@[simp] theorem UInt16.toUInt32_ofBitVec {b} : (UInt16.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt16.toUInt64_ofBitVec {b} : (UInt16.ofBitVec b).toUInt64 = UInt64.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt16.toUSize_ofBitVec {b} : (UInt16.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toBitVec_inj.1 (by simp)

theorem UInt16.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUInt32 = UInt32.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt16.toUInt64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt16.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt16.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt16.toUInt64_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUInt64 = UInt64.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt16.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUSize = USize.ofNatLT (UInt16.size - 1) (Nat.lt_of_lt_of_le (by decide) size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt32.toUInt64_ofNatLT {n : Nat} (h) :
    (UInt32.ofNatLT n h).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := rfl
theorem UInt32.toUSize_ofNatLT {n : Nat} (h) :
    (UInt32.ofNatLT n h).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le h size_le_usizeSize) := rfl

theorem UInt32.toUInt64_ofFin {n} :
  (UInt32.ofFin n).toUInt64 = UInt64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := rfl
theorem UInt32.toUSize_ofFin {n} :
  (UInt32.ofFin n).toUSize = USize.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_usizeSize) := rfl

@[simp] theorem UInt32.toUInt64_ofBitVec {b} : (UInt32.ofBitVec b).toUInt64 = UInt64.ofBitVec (b.setWidth _) := rfl
@[simp] theorem UInt32.toUSize_ofBitVec {b} : (UInt32.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toBitVec_inj.1 (by simp)

theorem UInt32.toUInt64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])
theorem UInt32.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt32.toUInt64_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUInt64 = UInt64.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])
theorem UInt32.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUSize = USize.ofNatLT (UInt32.size - 1) (Nat.lt_of_lt_of_le (by decide) size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize.toUInt64_ofNatLT {n : Nat} (h) :
    (USize.ofNatLT n h).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le h size_le_uint64Size) := rfl

theorem USize.toUInt64_ofFin {n} :
  (USize.ofFin n).toUInt64 = UInt64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_uint64Size) := rfl

@[simp] theorem USize.toUInt64_ofBitVec {b} : (USize.ofBitVec b).toUInt64 = UInt64.ofBitVec (b.setWidth _) :=
  UInt64.toBitVec_inj.1 (by simp)

theorem USize.toUInt64_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_uint64Size) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize.toUInt64_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUInt64 = UInt64.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all +decide) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt8.toUInt16_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUInt16 = UInt16.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUInt16_ofNatLT, UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt8.toUInt32_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUInt32 = UInt32.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUInt32_ofNatLT, UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt8.toUInt64_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUInt64 = UInt64.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUInt64_ofNatLT, UInt64.ofNatLT_eq_ofNat]
@[simp] theorem UInt8.toUSize_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUSize = USize.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUSize_ofNatLT, USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt16.toUInt32_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUInt32 = UInt32.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUInt32_ofNatLT, UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.toUInt64_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUInt64 = UInt64.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUInt64_ofNatLT, UInt64.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.toUSize_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUSize = USize.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUSize_ofNatLT, USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt32.toUInt64_ofNat' {n : Nat} (hn : n < UInt32.size) : (UInt32.ofNat n).toUInt64 = UInt64.ofNat n := by
  rw [← UInt32.ofNatLT_eq_ofNat (h := hn), toUInt64_ofNatLT, UInt64.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.toUSize_ofNat' {n : Nat} (hn : n < UInt32.size) : (UInt32.ofNat n).toUSize = USize.ofNat n := by
  rw [← UInt32.ofNatLT_eq_ofNat (h := hn), toUSize_ofNatLT, USize.ofNatLT_eq_ofNat]

@[simp] theorem USize.toUInt64_ofNat' {n : Nat} (hn : n < USize.size) : (USize.ofNat n).toUInt64 = UInt64.ofNat n := by
  rw [← USize.ofNatLT_eq_ofNat (h := hn), toUInt64_ofNatLT, UInt64.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.toUInt16_ofNat {n : Nat} (hn : n < 256) : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUInt16_ofNat' hn
@[simp] theorem UInt8.toUInt32_ofNat {n : Nat} (hn : n < 256) : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUInt32_ofNat' hn
@[simp] theorem UInt8.toUInt64_ofNat {n : Nat} (hn : n < 256) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUInt64_ofNat' hn
@[simp] theorem UInt8.toUSize_ofNat {n : Nat} (hn : n < 256) : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUSize_ofNat' hn

@[simp] theorem UInt16.toUInt32_ofNat {n : Nat} (hn : n < 65536) : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUInt32_ofNat' hn
@[simp] theorem UInt16.toUInt64_ofNat {n : Nat} (hn : n < 65536) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUInt64_ofNat' hn
@[simp] theorem UInt16.toUSize_ofNat {n : Nat} (hn : n < 65536) : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUSize_ofNat' hn

@[simp] theorem UInt32.toUInt64_ofNat {n : Nat} (hn : n < 4294967296) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt32.toUInt64_ofNat' hn
@[simp] theorem UInt32.toUSize_ofNat {n : Nat} (hn : n < 4294967296) : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt32.toUSize_ofNat' hn

@[simp] theorem USize.toUInt64_ofNat {n : Nat} (hn : n < 4294967296) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize.toUInt64_ofNat' (Nat.lt_of_lt_of_le hn UInt32.size_le_usizeSize)

@[simp] theorem UInt8.ofNatLT_finVal (n : Fin UInt8.size) : UInt8.ofNatLT n.val n.isLt = UInt8.ofFin n := rfl
@[simp] theorem UInt16.ofNatLT_finVal (n : Fin UInt16.size) : UInt16.ofNatLT n.val n.isLt = UInt16.ofFin n := rfl
@[simp] theorem UInt32.ofNatLT_finVal (n : Fin UInt32.size) : UInt32.ofNatLT n.val n.isLt = UInt32.ofFin n := rfl
@[simp] theorem UInt64.ofNatLT_finVal (n : Fin UInt64.size) : UInt64.ofNatLT n.val n.isLt = UInt64.ofFin n := rfl
@[simp] theorem USize.ofNatLT_finVal (n : Fin USize.size) : USize.ofNatLT n.val n.isLt = USize.ofFin n := rfl

@[simp] theorem UInt8.ofNatLT_bitVecToNat (n : BitVec 8) : UInt8.ofNatLT n.toNat n.isLt = UInt8.ofBitVec n := rfl
@[simp] theorem UInt16.ofNatLT_bitVecToNat (n : BitVec 16) : UInt16.ofNatLT n.toNat n.isLt = UInt16.ofBitVec n := rfl
@[simp] theorem UInt32.ofNatLT_bitVecToNat (n : BitVec 32) : UInt32.ofNatLT n.toNat n.isLt = UInt32.ofBitVec n := rfl
@[simp] theorem UInt64.ofNatLT_bitVecToNat (n : BitVec 64) : UInt64.ofNatLT n.toNat n.isLt = UInt64.ofBitVec n := rfl
@[simp] theorem USize.ofNatLT_bitVecToNat (n : BitVec System.Platform.numBits) : USize.ofNatLT n.toNat n.isLt = USize.ofBitVec n := rfl

@[simp] theorem UInt8.ofNat_finVal (n : Fin UInt8.size) : UInt8.ofNat n.val = UInt8.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]
@[simp] theorem UInt16.ofNat_finVal (n : Fin UInt16.size) : UInt16.ofNat n.val = UInt16.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]
@[simp] theorem UInt32.ofNat_finVal (n : Fin UInt32.size) : UInt32.ofNat n.val = UInt32.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]
@[simp] theorem UInt64.ofNat_finVal (n : Fin UInt64.size) : UInt64.ofNat n.val = UInt64.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]
@[simp] theorem USize.ofNat_finVal (n : Fin USize.size) : USize.ofNat n.val = USize.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]

@[simp] theorem UInt8.ofNat_bitVecToNat (n : BitVec 8) : UInt8.ofNat n.toNat = UInt8.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]
@[simp] theorem UInt16.ofNat_bitVecToNat (n : BitVec 16) : UInt16.ofNat n.toNat = UInt16.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]
@[simp] theorem UInt32.ofNat_bitVecToNat (n : BitVec 32) : UInt32.ofNat n.toNat = UInt32.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]
@[simp] theorem UInt64.ofNat_bitVecToNat (n : BitVec 64) : UInt64.ofNat n.toNat = UInt64.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]
@[simp] theorem USize.ofNat_bitVecToNat (n : BitVec System.Platform.numBits) : USize.ofNat n.toNat = USize.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]

@[simp] theorem UInt8.ofNatTruncate_finVal (n : Fin UInt8.size) : UInt8.ofNatTruncate n.val = UInt8.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, UInt8.ofNat_finVal]
@[simp] theorem UInt16.ofNatTruncate_finVal (n : Fin UInt16.size) : UInt16.ofNatTruncate n.val = UInt16.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, UInt16.ofNat_finVal]
@[simp] theorem UInt32.ofNatTruncate_finVal (n : Fin UInt32.size) : UInt32.ofNatTruncate n.val = UInt32.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, UInt32.ofNat_finVal]
@[simp] theorem UInt64.ofNatTruncate_finVal (n : Fin UInt64.size) : UInt64.ofNatTruncate n.val = UInt64.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, UInt64.ofNat_finVal]
@[simp] theorem USize.ofNatTruncate_finVal (n : Fin USize.size) : USize.ofNatTruncate n.val = USize.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, USize.ofNat_finVal]

@[simp] theorem UInt8.ofNatTruncate_bitVecToNat (n : BitVec 8) : UInt8.ofNatTruncate n.toNat = UInt8.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]
@[simp] theorem UInt16.ofNatTruncate_bitVecToNat (n : BitVec 16) : UInt16.ofNatTruncate n.toNat = UInt16.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]
@[simp] theorem UInt32.ofNatTruncate_bitVecToNat (n : BitVec 32) : UInt32.ofNatTruncate n.toNat = UInt32.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]
@[simp] theorem UInt64.ofNatTruncate_bitVecToNat (n : BitVec 64) : UInt64.ofNatTruncate n.toNat = UInt64.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]
@[simp] theorem USize.ofNatTruncate_bitVecToNat (n : BitVec System.Platform.numBits) : USize.ofNatTruncate n.toNat = USize.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]

@[simp] theorem UInt8.ofFin_mk {n : Nat} (hn) : UInt8.ofFin (Fin.mk n hn) = UInt8.ofNatLT n hn := rfl
@[simp] theorem UInt16.ofFin_mk {n : Nat} (hn) : UInt16.ofFin (Fin.mk n hn) = UInt16.ofNatLT n hn := rfl
@[simp] theorem UInt32.ofFin_mk {n : Nat} (hn) : UInt32.ofFin (Fin.mk n hn) = UInt32.ofNatLT n hn := rfl
@[simp] theorem UInt64.ofFin_mk {n : Nat} (hn) : UInt64.ofFin (Fin.mk n hn) = UInt64.ofNatLT n hn := rfl
@[simp] theorem USize.ofFin_mk {n : Nat} (hn) : USize.ofFin (Fin.mk n hn) = USize.ofNatLT n hn := rfl

@[simp] theorem UInt8.ofFin_bitVecToFin (n : BitVec 8) : UInt8.ofFin n.toFin = UInt8.ofBitVec n := rfl
@[simp] theorem UInt16.ofFin_bitVecToFin (n : BitVec 16) : UInt16.ofFin n.toFin = UInt16.ofBitVec n := rfl
@[simp] theorem UInt32.ofFin_bitVecToFin (n : BitVec 32) : UInt32.ofFin n.toFin = UInt32.ofBitVec n := rfl
@[simp] theorem UInt64.ofFin_bitVecToFin (n : BitVec 64) : UInt64.ofFin n.toFin = UInt64.ofBitVec n := rfl
@[simp] theorem USize.ofFin_bitVecToFin (n : BitVec System.Platform.numBits) : USize.ofFin n.toFin = USize.ofBitVec n := rfl

@[simp] theorem UInt8.ofBitVec_ofNatLT {n : Nat} (hn) : UInt8.ofBitVec (BitVec.ofNatLT n hn) = UInt8.ofNatLT n hn := rfl
@[simp] theorem UInt16.ofBitVec_ofNatLT {n : Nat} (hn) : UInt16.ofBitVec (BitVec.ofNatLT n hn) = UInt16.ofNatLT n hn := rfl
@[simp] theorem UInt32.ofBitVec_ofNatLT {n : Nat} (hn) : UInt32.ofBitVec (BitVec.ofNatLT n hn) = UInt32.ofNatLT n hn := rfl
@[simp] theorem UInt64.ofBitVec_ofNatLT {n : Nat} (hn) : UInt64.ofBitVec (BitVec.ofNatLT n hn) = UInt64.ofNatLT n hn := rfl
@[simp] theorem USize.ofBitVec_ofNatLT {n : Nat} (hn) : USize.ofBitVec (BitVec.ofNatLT n hn) = USize.ofNatLT n hn := rfl

@[simp] theorem UInt8.ofBitVec_ofFin (n) : UInt8.ofBitVec (BitVec.ofFin n) = UInt8.ofFin n := rfl
@[simp] theorem UInt16.ofBitVec_ofFin (n) : UInt16.ofBitVec (BitVec.ofFin n) = UInt16.ofFin n := rfl
@[simp] theorem UInt32.ofBitVec_ofFin (n) : UInt32.ofBitVec (BitVec.ofFin n) = UInt32.ofFin n := rfl
@[simp] theorem UInt64.ofBitVec_ofFin (n) : UInt64.ofBitVec (BitVec.ofFin n) = UInt64.ofFin n := rfl
@[simp] theorem USize.ofBitVec_ofFin (n) : USize.ofBitVec (BitVec.ofFin n) = USize.ofFin n := rfl

@[simp] theorem BitVec.ofNat_uInt8ToNat (n : UInt8) : BitVec.ofNat 8 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem BitVec.ofNat_uInt16ToNat (n : UInt16) : BitVec.ofNat 16 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem BitVec.ofNat_uInt32ToNat (n : UInt32) : BitVec.ofNat 32 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem BitVec.ofNat_uInt64ToNat (n : UInt64) : BitVec.ofNat 64 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)
@[simp] theorem BitVec.ofNat_uSizeToNat (n : USize) : BitVec.ofNat System.Platform.numBits n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] protected theorem UInt8.toFin_div (a b : UInt8) : (a / b).toFin = a.toFin / b.toFin := rfl
@[simp] protected theorem UInt16.toFin_div (a b : UInt16) : (a / b).toFin = a.toFin / b.toFin := rfl
@[simp] protected theorem UInt32.toFin_div (a b : UInt32) : (a / b).toFin = a.toFin / b.toFin := rfl
@[simp] protected theorem UInt64.toFin_div (a b : UInt64) : (a / b).toFin = a.toFin / b.toFin := rfl
@[simp] protected theorem USize.toFin_div (a b : USize) : (a / b).toFin = a.toFin / b.toFin := rfl

@[simp] theorem UInt8.toUInt16_div (a b : UInt8) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 := rfl
@[simp] theorem UInt8.toUInt32_div (a b : UInt8) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 := rfl
@[simp] theorem UInt8.toUInt64_div (a b : UInt8) : (a / b).toUInt64 = a.toUInt64 / b.toUInt64 := rfl
@[simp] theorem UInt8.toUSize_div (a b : UInt8) : (a / b).toUSize = a.toUSize / b.toUSize := rfl

@[simp] theorem UInt16.toUInt32_div (a b : UInt16) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 := rfl
@[simp] theorem UInt16.toUInt64_div (a b : UInt16) : (a / b).toUInt64 = a.toUInt64 / b.toUInt64 := rfl
@[simp] theorem UInt16.toUSize_div (a b : UInt16) : (a / b).toUSize = a.toUSize / b.toUSize := rfl

@[simp] theorem UInt32.toUInt64_div (a b : UInt32) : (a / b).toUInt64 = a.toUInt64 / b.toUInt64 := rfl
@[simp] theorem UInt32.toUSize_div (a b : UInt32) : (a / b).toUSize = a.toUSize / b.toUSize := rfl

@[simp] theorem USize.toUInt64_div (a b : USize) : (a / b).toUInt64 = a.toUInt64 / b.toUInt64 := rfl

theorem UInt16.toUInt8_div (a b : UInt16) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt32.toUInt8_div (a b : UInt32) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)
theorem UInt32.toUInt16_div (a b : UInt32) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem USize.toUInt8_div (a b : USize) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt8.size_lt_usizeSize] using Nat.div_mod_eq_mod_div_mod ha hb)
theorem USize.toUInt16_div (a b : USize) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt16.size_lt_usizeSize] using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt64.toUInt8_div (a b : UInt64) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)
theorem UInt64.toUInt16_div (a b : UInt64) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)
theorem UInt64.toUInt32_div (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)
theorem UInt64.toUSize_div (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (Nat.div_mod_eq_mod_div_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))
theorem UInt64.toUSize_div_of_toNat_lt (a b : UInt64) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) :
    (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

@[simp] protected theorem UInt8.toFin_mod (a b : UInt8) : (a % b).toFin = a.toFin % b.toFin := rfl
@[simp] protected theorem UInt16.toFin_mod (a b : UInt8) : (a % b).toFin = a.toFin % b.toFin := rfl
@[simp] protected theorem UInt32.toFin_mod (a b : UInt32) : (a % b).toFin = a.toFin % b.toFin := rfl
@[simp] protected theorem UInt64.toFin_mod (a b : UInt64) : (a % b).toFin = a.toFin % b.toFin := rfl
@[simp] protected theorem USize.toFin_mod (a b : USize) : (a % b).toFin = a.toFin % b.toFin := rfl

@[simp] theorem UInt8.toUInt16_mod (a b : UInt8) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 := rfl
@[simp] theorem UInt8.toUInt32_mod (a b : UInt8) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 := rfl
@[simp] theorem UInt8.toUInt64_mod (a b : UInt8) : (a % b).toUInt64 = a.toUInt64 % b.toUInt64 := rfl
@[simp] theorem UInt8.toUSize_mod (a b : UInt8) : (a % b).toUSize = a.toUSize % b.toUSize := rfl

@[simp] theorem UInt16.toUInt32_mod (a b : UInt16) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 := rfl
@[simp] theorem UInt16.toUInt64_mod (a b : UInt16) : (a % b).toUInt64 = a.toUInt64 % b.toUInt64 := rfl
@[simp] theorem UInt16.toUSize_mod (a b : UInt16) : (a % b).toUSize = a.toUSize % b.toUSize := rfl

@[simp] theorem UInt32.toUInt64_mod (a b : UInt32) : (a % b).toUInt64 = a.toUInt64 % b.toUInt64 := rfl
@[simp] theorem UInt32.toUSize_mod (a b : UInt32) : (a % b).toUSize = a.toUSize % b.toUSize := rfl

@[simp] theorem USize.toUInt64_mod (a b : USize) : (a % b).toUInt64 = a.toUInt64 % b.toUInt64 := rfl

theorem UInt16.toUInt8_mod (a b : UInt16) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt16.toUInt8_mod_of_dvd (a b : UInt16) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt32.toUInt8_mod (a b : UInt32) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt32.toUInt16_mod (a b : UInt32) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt32.toUInt8_mod_of_dvd (a b : UInt32) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem UInt32.toUInt16_mod_of_dvd (a b : UInt32) (hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize.toUInt8_mod (a b : USize) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt8.size_lt_usizeSize] using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem USize.toUInt16_mod (a b : USize) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt16.size_lt_usizeSize] using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem USize.toUInt32_mod (a b : USize) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 := by
  apply UInt32.toNat.inj
  simp only [toNat_toUInt32, USize.toNat_mod, Nat.reducePow, UInt32.toNat_mod]
  have := Nat.mod_mod_eq_mod_mod_mod ha hb
  obtain (h|h) := USize.size_eq
  · have ha' := h ▸ a.toNat_lt_size
    have hb' := h ▸ b.toNat_lt_size
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
  · simp_all
theorem USize.toUInt8_mod_of_dvd (a b : USize) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt8.size_lt_usizeSize] using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem USize.toUInt16_mod_of_dvd (a b : USize) (hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa [Nat.mod_eq_of_lt UInt16.size_lt_usizeSize] using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem USize.toUInt32_mod_of_dvd (a b : USize) (hb : b.toNat ∣ 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 := by
  apply UInt32.toNat.inj
  simp only [toNat_toUInt32, USize.toNat_mod, Nat.reducePow, UInt32.toNat_mod]
  have := Nat.mod_mod_eq_mod_mod_mod_of_dvd (a := a.toNat) hb
  obtain (h|h) := USize.size_eq
  · have ha' := h ▸ a.toNat_lt_size
    have hb' := h ▸ b.toNat_lt_size
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
  · simp_all

theorem UInt64.toUInt8_mod (a b : UInt64) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt64.toUInt16_mod (a b : UInt64) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt64.toUInt32_mod (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt64.toUSize_mod (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))
theorem UInt64.toUSize_mod_of_toNat_lt (a b : UInt64) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)
theorem UInt64.toUInt8_mod_of_dvd (a b : UInt64) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem UInt64.toUInt16_mod_of_dvd (a b : UInt64)(hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem UInt64.toUInt32_mod_of_dvd (a b : UInt64) (hb : b.toNat ∣ 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)
theorem UInt64.toUSize_mod_of_dvd (a b : UInt64) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.dvd_trans hb UInt32.size_dvd_usizeSize))
theorem UInt64.toUSize_mod_of_dvd_usizeSize (a b : UInt64) (hb : b.toNat ∣ USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

@[simp] protected theorem UInt8.toFin_add (a b : UInt8) : (a + b).toFin = a.toFin + b.toFin := rfl
@[simp] protected theorem UInt16.toFin_add (a b : UInt16) : (a + b).toFin = a.toFin + b.toFin := rfl
@[simp] protected theorem UInt32.toFin_add (a b : UInt32) : (a + b).toFin = a.toFin + b.toFin := rfl
@[simp] protected theorem UInt64.toFin_add (a b : UInt64) : (a + b).toFin = a.toFin + b.toFin := rfl
@[simp] protected theorem USize.toFin_add (a b : USize) : (a + b).toFin = a.toFin + b.toFin := rfl

@[simp] theorem UInt16.toUInt8_add (a b : UInt16) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt8_add (a b : UInt32) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt8_add (a b : UInt64) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem USize.toUInt8_add (a b : USize) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt16_add (a b : UInt32) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt16_add (a b : UInt64) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)
@[simp] theorem USize.toUInt16_add (a b : USize) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt32_add (a b : UInt64) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := UInt32.toNat.inj (by simp)
@[simp] theorem USize.toUInt32_add (a b : USize) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize_add (a b : UInt64) : (a + b).toUSize = a.toUSize + b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_add (a b : UInt8) : (a + b).toUInt16 = (a.toUInt16 + b.toUInt16) % 256 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt32_add (a b : UInt8) : (a + b).toUInt32 = (a.toUInt32 + b.toUInt32) % 256 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt64_add (a b : UInt8) : (a + b).toUInt64 = (a.toUInt64 + b.toUInt64) % 256 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt8.toUSize_add (a b : UInt8) : (a + b).toUSize = (a.toUSize + b.toUSize) % 256 := USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_add (a b : UInt16) : (a + b).toUInt32 = (a.toUInt32 + b.toUInt32) % 65536 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt64_add (a b : UInt16) : (a + b).toUInt64 = (a.toUInt64 + b.toUInt64) % 65536 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt16.toUSize_add (a b : UInt16) : (a + b).toUSize = (a.toUSize + b.toUSize) % 65536 := USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt64_add (a b : UInt32) : (a + b).toUInt64 = (a.toUInt64 + b.toUInt64) % 4294967296 := UInt64.toNat.inj (by simp)
/-- Note that on 32-bit machines we are doing a modulo by zero. -/
@[simp] theorem UInt32.toUSize_add (a b : UInt32) : (a + b).toUSize = (a.toUSize + b.toUSize) % 4294967296 :=
  USize.toNat.inj (by cases System.Platform.numBits_eq <;> simp_all [USize.toNat_ofNat])

@[simp] protected theorem UInt8.toFin_sub (a b : UInt8) : (a - b).toFin = a.toFin - b.toFin := rfl
@[simp] protected theorem UInt16.toFin_sub (a b : UInt16) : (a - b).toFin = a.toFin - b.toFin := rfl
@[simp] protected theorem UInt32.toFin_sub (a b : UInt32) : (a - b).toFin = a.toFin - b.toFin := rfl
@[simp] protected theorem UInt64.toFin_sub (a b : UInt64) : (a - b).toFin = a.toFin - b.toFin := rfl
@[simp] protected theorem USize.toFin_sub (a b : USize) : (a - b).toFin = a.toFin - b.toFin := rfl

@[simp] protected theorem UInt8.toFin_mul (a b : UInt8) : (a * b).toFin = a.toFin * b.toFin := rfl
@[simp] protected theorem UInt16.toFin_mul (a b : UInt16) : (a * b).toFin = a.toFin * b.toFin := rfl
@[simp] protected theorem UInt32.toFin_mul (a b : UInt32) : (a * b).toFin = a.toFin * b.toFin := rfl
@[simp] protected theorem UInt64.toFin_mul (a b : UInt64) : (a * b).toFin = a.toFin * b.toFin := rfl
@[simp] protected theorem USize.toFin_mul (a b : USize) : (a * b).toFin = a.toFin * b.toFin := rfl

@[simp] theorem UInt16.toUInt8_mul (a b : UInt16) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt32.toUInt8_mul (a b : UInt32) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt8_mul (a b : UInt64) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)
@[simp] theorem USize.toUInt8_mul (a b : USize) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt16_mul (a b : UInt32) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt64.toUInt16_mul (a b : UInt64) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)
@[simp] theorem USize.toUInt16_mul (a b : USize) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt32_mul (a b : UInt64) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := UInt32.toNat.inj (by simp)
@[simp] theorem USize.toUInt32_mul (a b : USize) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize_mul (a b : UInt64) : (a * b).toUSize = a.toUSize * b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_mul (a b : UInt8) : (a * b).toUInt16 = (a.toUInt16 * b.toUInt16) % 256 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt32_mul (a b : UInt8) : (a * b).toUInt32 = (a.toUInt32 * b.toUInt32) % 256 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt8.toUInt64_mul (a b : UInt8) : (a * b).toUInt64 = (a.toUInt64 * b.toUInt64) % 256 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt8.toUSize_mul (a b : UInt8) : (a * b).toUSize = (a.toUSize * b.toUSize) % 256 := USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_mul (a b : UInt16) : (a * b).toUInt32 = (a.toUInt32 * b.toUInt32) % 65536 := UInt32.toNat.inj (by simp)
@[simp] theorem UInt16.toUInt64_mul (a b : UInt16) : (a * b).toUInt64 = (a.toUInt64 * b.toUInt64) % 65536 := UInt64.toNat.inj (by simp)
@[simp] theorem UInt16.toUSize_mul (a b : UInt16) : (a * b).toUSize = (a.toUSize * b.toUSize) % 65536 := USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt64_mul (a b : UInt32) : (a * b).toUInt64 = (a.toUInt64 * b.toUInt64) % 4294967296 := UInt64.toNat.inj (by simp)
/-- Note that on 32-bit machines we are doing a modulo by zero. -/
@[simp] theorem UInt32.toUSize_mul (a b : UInt32) : (a * b).toUSize = (a.toUSize * b.toUSize) % 4294967296 :=
  USize.toNat.inj (by cases System.Platform.numBits_eq <;> simp_all [USize.toNat_ofNat])

theorem UInt16.toUInt8_eq (a b : UInt16) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← UInt16.toNat_inj]
theorem UInt32.toUInt8_eq (a b : UInt32) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← UInt32.toNat_inj]
theorem UInt64.toUInt8_eq (a b : UInt64) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← UInt64.toNat_inj]
theorem USize.toUInt8_eq (a b : USize) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← USize.toNat_inj]

theorem UInt32.toUInt16_eq (a b : UInt32) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← UInt32.toNat_inj]
theorem UInt64.toUInt16_eq (a b : UInt64) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← UInt64.toNat_inj]
theorem USize.toUInt16_eq (a b : USize) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← USize.toNat_inj]

theorem UInt64.toUInt32_eq (a b : UInt64) : a.toUInt32 = b.toUInt32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← UInt32.toNat_inj, ← UInt64.toNat_inj]
theorem USize.toUInt32_eq (a b : USize) : a.toUInt32 = b.toUInt32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← UInt32.toNat_inj, ← USize.toNat_inj, USize.toNat_ofNat]
  have := Nat.mod_eq_of_lt a.toNat_lt_two_pow_numBits
  have := Nat.mod_eq_of_lt b.toNat_lt_two_pow_numBits
  cases System.Platform.numBits_eq <;> simp_all

theorem UInt8.toUInt16_eq_mod_256_iff (a : UInt8) (b : UInt16) : a.toUInt16 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← UInt16.toNat_inj]
theorem UInt8.toUInt32_eq_mod_256_iff (a : UInt8) (b : UInt32) : a.toUInt32 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← UInt32.toNat_inj]
theorem UInt8.toUInt64_eq_mod_256_iff (a : UInt8) (b : UInt64) : a.toUInt64 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← UInt64.toNat_inj]
theorem UInt8.toUSize_eq_mod_256_iff (a : UInt8) (b : USize) : a.toUSize = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← USize.toNat_inj]

theorem UInt16.toUInt32_eq_mod_65536_iff (a : UInt16) (b : UInt32) : a.toUInt32 = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← UInt32.toNat_inj]
theorem UInt16.toUInt64_eq_mod_65536_iff (a : UInt16) (b : UInt64) : a.toUInt64 = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← UInt64.toNat_inj]
theorem UInt16.toUSize_eq_mod_65536_iff (a : UInt16) (b : USize) : a.toUSize = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← USize.toNat_inj]

theorem UInt32.toUInt64_eq_mod_4294967296_iff (a : UInt32) (b : UInt64) : a.toUInt64 = b % 4294967296 ↔ a = b.toUInt32 := by
  simp [← UInt32.toNat_inj, ← UInt64.toNat_inj]
theorem UInt32.toUSize_eq_mod_4294967296_iff (a : UInt32) (b : USize) : a.toUSize = b % 4294967296 ↔ a = b.toUInt32 := by
  simp [← UInt32.toNat_inj, ← USize.toNat_inj, USize.toNat_ofNat]
  have := Nat.mod_eq_of_lt b.toNat_lt_two_pow_numBits
  cases System.Platform.numBits_eq <;> simp_all

theorem USize.toUInt64_eq_mod_usizeSize_iff (a : USize) (b : UInt64) : a.toUInt64 = b % UInt64.ofNat USize.size ↔ a = b.toUSize := by
  simp [← USize.toNat_inj, ← UInt64.toNat_inj, USize.size_eq_two_pow]
  cases System.Platform.numBits_eq <;> simp_all

theorem UInt8.toUInt16_inj {a b : UInt8} : a.toUInt16 = b.toUInt16 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUInt16 a, h, toUInt8_toUInt16], by rintro rfl; rfl⟩
theorem UInt8.toUInt32_inj {a b : UInt8} : a.toUInt32 = b.toUInt32 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUInt32 a, h, toUInt8_toUInt32], by rintro rfl; rfl⟩
theorem UInt8.toUInt64_inj {a b : UInt8} : a.toUInt64 = b.toUInt64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUInt64 a, h, toUInt8_toUInt64], by rintro rfl; rfl⟩
theorem UInt8.toUSize_inj {a b : UInt8} : a.toUSize = b.toUSize ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUSize a, h, toUInt8_toUSize], by rintro rfl; rfl⟩

theorem UInt16.toUInt32_inj {a b : UInt16} : a.toUInt32 = b.toUInt32 ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUInt32 a, h, toUInt16_toUInt32], by rintro rfl; rfl⟩
theorem UInt16.toUInt64_inj {a b : UInt16} : a.toUInt64 = b.toUInt64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUInt64 a, h, toUInt16_toUInt64], by rintro rfl; rfl⟩
theorem UInt16.toUSize_inj {a b : UInt16} : a.toUSize = b.toUSize ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUSize a, h, toUInt16_toUSize], by rintro rfl; rfl⟩

theorem UInt32.toUInt64_inj {a b : UInt32} : a.toUInt64 = b.toUInt64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt32_toUInt64 a, h, toUInt32_toUInt64], by rintro rfl; rfl⟩
theorem UInt32.toUSize_inj {a b : UInt32} : a.toUSize = b.toUSize ↔ a = b :=
  ⟨fun h => by rw [← toUInt32_toUSize a, h, toUInt32_toUSize], by rintro rfl; rfl⟩

theorem USize.toUInt64_inj {a b : USize} : a.toUInt64 = b.toUInt64 ↔ a = b :=
  ⟨fun h => by rw [← toUSize_toUInt64 a, h, toUSize_toUInt64], by rintro rfl; rfl⟩

theorem UInt8.lt_iff_toFin_lt {a b : UInt8} : a < b ↔ a.toFin < b.toFin := Iff.rfl
theorem UInt16.lt_iff_toFin_lt {a b : UInt16} : a < b ↔ a.toFin < b.toFin := Iff.rfl
theorem UInt32.lt_iff_toFin_lt {a b : UInt32} : a < b ↔ a.toFin < b.toFin := Iff.rfl
theorem UInt64.lt_iff_toFin_lt {a b : UInt64} : a < b ↔ a.toFin < b.toFin := Iff.rfl
theorem USize.lt_iff_toFin_lt {a b : USize} : a < b ↔ a.toFin < b.toFin := Iff.rfl

theorem UInt8.le_iff_toFin_le {a b : UInt8} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl
theorem UInt16.le_iff_toFin_le {a b : UInt16} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl
theorem UInt32.le_iff_toFin_le {a b : UInt32} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl
theorem UInt64.le_iff_toFin_le {a b : UInt64} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl
theorem USize.le_iff_toFin_le {a b : USize} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl

@[simp] theorem UInt8.toUInt16_lt {a b : UInt8} : a.toUInt16 < b.toUInt16 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]
@[simp] theorem UInt8.toUInt32_lt {a b : UInt8} : a.toUInt32 < b.toUInt32 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]
@[simp] theorem UInt8.toUInt64_lt {a b : UInt8} : a.toUInt64 < b.toUInt64 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
@[simp] theorem UInt8.toUSize_lt {a b : UInt8} : a.toUSize < b.toUSize ↔ a < b := by
  simp [lt_iff_toNat_lt, USize.lt_iff_toNat_lt]

@[simp] theorem UInt16.toUInt32_lt {a b : UInt16} : a.toUInt32 < b.toUInt32 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]
@[simp] theorem UInt16.toUInt64_lt {a b : UInt16} : a.toUInt64 < b.toUInt64 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
@[simp] theorem UInt16.toUSize_lt {a b : UInt16} : a.toUSize < b.toUSize ↔ a < b := by
  simp [lt_iff_toNat_lt, USize.lt_iff_toNat_lt]

@[simp] theorem UInt32.toUInt64_lt {a b : UInt32} : a.toUInt64 < b.toUInt64 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
@[simp] theorem UInt32.toUSize_lt {a b : UInt32} : a.toUSize < b.toUSize ↔ a < b := by
  simp [lt_iff_toNat_lt, USize.lt_iff_toNat_lt]

@[simp] theorem USize.toUInt64_lt {a b : USize} : a.toUInt64 < b.toUInt64 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]

@[simp] theorem UInt16.toUInt8_lt {a b : UInt16} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]
@[simp] theorem UInt32.toUInt8_lt {a b : UInt32} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]
@[simp] theorem UInt64.toUInt8_lt {a b : UInt64} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]
@[simp] theorem USize.toUInt8_lt {a b : USize} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]

@[simp] theorem UInt32.toUInt16_lt {a b : UInt32} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]
@[simp] theorem UInt64.toUInt16_lt {a b : UInt64} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]
@[simp] theorem USize.toUInt16_lt {a b : USize} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]

@[simp] theorem UInt64.toUInt32_lt {a b : UInt64} : a.toUInt32 < b.toUInt32 ↔ a % 4294967296 < b % 4294967296 := by
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]
@[simp] theorem USize.toUInt32_lt {a b : USize} : a.toUInt32 < b.toUInt32 ↔ a % 4294967296 < b % 4294967296 := by
  rw [← UInt32.toUSize_lt, toUSize_toUInt32]
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]

@[simp] theorem UInt64.toUSize_lt {a b : UInt64} : a.toUSize < b.toUSize ↔ a % UInt64.ofNat USize.size < b % UInt64.ofNat USize.size := by
  simp only [USize.lt_iff_toNat_lt, toNat_toUSize, lt_iff_toNat_lt, UInt64.toNat_mod, toNat_ofNat', Nat.reducePow]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem UInt8.toUInt16_le {a b : UInt8} : a.toUInt16 ≤ b.toUInt16 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]
@[simp] theorem UInt8.toUInt32_le {a b : UInt8} : a.toUInt32 ≤ b.toUInt32 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]
@[simp] theorem UInt8.toUInt64_le {a b : UInt8} : a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt64.le_iff_toNat_le]
@[simp] theorem UInt8.toUSize_le {a b : UInt8} : a.toUSize ≤ b.toUSize ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize.le_iff_toNat_le]

@[simp] theorem UInt16.toUInt32_le {a b : UInt16} : a.toUInt32 ≤ b.toUInt32 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]
@[simp] theorem UInt16.toUInt64_le {a b : UInt16} : a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt64.le_iff_toNat_le]
@[simp] theorem UInt16.toUSize_le {a b : UInt16} : a.toUSize ≤ b.toUSize ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize.le_iff_toNat_le]

@[simp] theorem UInt32.toUInt64_le {a b : UInt32} : a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt64.le_iff_toNat_le]
@[simp] theorem UInt32.toUSize_le {a b : UInt32} : a.toUSize ≤ b.toUSize ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize.le_iff_toNat_le]

@[simp] theorem USize.toUInt64_le {a b : USize} : a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt64.le_iff_toNat_le]

@[simp] theorem UInt16.toUInt8_le {a b : UInt16} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]
@[simp] theorem UInt32.toUInt8_le {a b : UInt32} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]
@[simp] theorem UInt64.toUInt8_le {a b : UInt64} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]
@[simp] theorem USize.toUInt8_le {a b : USize} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]

@[simp] theorem UInt32.toUInt16_le {a b : UInt32} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]
@[simp] theorem UInt64.toUInt16_le {a b : UInt64} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]
@[simp] theorem USize.toUInt16_le {a b : USize} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]

@[simp] theorem UInt64.toUInt32_le {a b : UInt64} : a.toUInt32 ≤ b.toUInt32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]
@[simp] theorem USize.toUInt32_le {a b : USize} : a.toUInt32 ≤ b.toUInt32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  rw [← UInt32.toUSize_le, toUSize_toUInt32]
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]

@[simp] theorem UInt64.toUSize_le {a b : UInt64} : a.toUSize ≤ b.toUSize ↔ a % UInt64.ofNat USize.size ≤ b % UInt64.ofNat USize.size := by
  simp only [USize.le_iff_toNat_le, toNat_toUSize, le_iff_toNat_le, UInt64.toNat_mod, UInt64.reduceToNat]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem UInt16.toUInt8_neg (a : UInt16) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)

@[simp] theorem UInt32.toUInt8_neg (a : UInt32) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt16_neg (a : UInt32) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)

@[simp] theorem UInt64.toUInt8_neg (a : UInt64) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt16_neg (a : UInt64) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt32_neg (a : UInt64) : (-a).toUInt32 = -a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUSize_neg (a : UInt64) : (-a).toUSize = -a.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem USize.toUInt8_neg (a : USize) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt16_neg (a : USize) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt32_neg (a : USize) : (-a).toUInt32 = -a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toUInt16_neg (a : UInt8) : (-a).toUInt16 = -a.toUInt16 % 256 := by
  simp [UInt8.toUInt16_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt32_neg (a : UInt8) : (-a).toUInt32 = -a.toUInt32 % 256 := by
  simp [UInt8.toUInt32_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt64_neg (a : UInt8) : (-a).toUInt64 = -a.toUInt64 % 256 := by
  simp [UInt8.toUInt64_eq_mod_256_iff]
@[simp] theorem UInt8.toUSize_neg (a : UInt8) : (-a).toUSize = -a.toUSize % 256 := by
  simp [UInt8.toUSize_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt32_neg (a : UInt16) : (-a).toUInt32 = -a.toUInt32 % 65536 := by
  simp [UInt16.toUInt32_eq_mod_65536_iff]
@[simp] theorem UInt16.toUInt64_neg (a : UInt16) : (-a).toUInt64 = -a.toUInt64 % 65536 := by
  simp [UInt16.toUInt64_eq_mod_65536_iff]
@[simp] theorem UInt16.toUSize_neg (a : UInt16) : (-a).toUSize = -a.toUSize % 65536 := by
  simp [UInt16.toUSize_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt64_neg (a : UInt32) : (-a).toUInt64 = -a.toUInt64 % 4294967296 := by
  simp [UInt32.toUInt64_eq_mod_4294967296_iff]
@[simp] theorem UInt32.toUSize_neg (a : UInt32) : (-a).toUSize = -a.toUSize % 4294967296 := by
  simp [UInt32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt64_neg (a : USize) : (-a).toUInt64 = -a.toUInt64 % UInt64.ofNat USize.size := by
  simp [USize.toUInt64_eq_mod_usizeSize_iff]

@[simp] theorem UInt8.toNat_neg (a : UInt8) : (-a).toNat = (UInt8.size - a.toNat) % UInt8.size := rfl
@[simp] theorem UInt16.toNat_neg (a : UInt16) : (-a).toNat = (UInt16.size - a.toNat) % UInt16.size := rfl
@[simp] theorem UInt32.toNat_neg (a : UInt32) : (-a).toNat = (UInt32.size - a.toNat) % UInt32.size := rfl
@[simp] theorem UInt64.toNat_neg (a : UInt64) : (-a).toNat = (UInt64.size - a.toNat) % UInt64.size := rfl
@[simp] theorem USize.toNat_neg (a : USize) : (-a).toNat = (USize.size - a.toNat) % USize.size := rfl

protected theorem UInt8.sub_eq_add_neg (a b : UInt8) : a - b = a + (-b) := UInt8.toBitVec_inj.1 (BitVec.sub_toAdd _ _)
protected theorem UInt16.sub_eq_add_neg (a b : UInt16) : a - b = a + (-b) := UInt16.toBitVec_inj.1 (BitVec.sub_toAdd _ _)
protected theorem UInt32.sub_eq_add_neg (a b : UInt32) : a - b = a + (-b) := UInt32.toBitVec_inj.1 (BitVec.sub_toAdd _ _)
protected theorem UInt64.sub_eq_add_neg (a b : UInt64) : a - b = a + (-b) := UInt64.toBitVec_inj.1 (BitVec.sub_toAdd _ _)
protected theorem USize.sub_eq_add_neg (a b : USize) : a - b = a + (-b) := USize.toBitVec_inj.1 (BitVec.sub_toAdd _ _)

protected theorem UInt8.add_neg_eq_sub {a b : UInt8} : a + -b = a - b := UInt8.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem UInt16.add_neg_eq_sub {a b : UInt16} : a + -b = a - b := UInt16.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem UInt32.add_neg_eq_sub {a b : UInt32} : a + -b = a - b := UInt32.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem UInt64.add_neg_eq_sub {a b : UInt64} : a + -b = a - b := UInt64.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem USize.add_neg_eq_sub {a b : USize} : a + -b = a - b := USize.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem UInt8.neg_one_eq : (-1 : UInt8) = 255 := rfl
theorem UInt16.neg_one_eq : (-1 : UInt16) = 65535 := rfl
theorem UInt32.neg_one_eq : (-1 : UInt32) = 4294967295 := rfl
theorem UInt64.neg_one_eq : (-1 : UInt64) = 18446744073709551615 := rfl
theorem USize.neg_one_eq : (-1 : USize) = USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) :=
  USize.toNat.inj (by simp)

theorem UInt8.toBitVec_zero : toBitVec 0 = 0#8 := rfl
theorem UInt16.toBitVec_zero : toBitVec 0 = 0#16 := rfl
theorem UInt32.toBitVec_zero : toBitVec 0 = 0#32 := rfl
theorem UInt64.toBitVec_zero : toBitVec 0 = 0#64 := rfl
theorem USize.toBitVec_zero : toBitVec 0 = 0#System.Platform.numBits := rfl

theorem UInt8.toBitVec_one : toBitVec 1 = 1#8 := rfl
theorem UInt16.toBitVec_one : toBitVec 1 = 1#16 := rfl
theorem UInt32.toBitVec_one : toBitVec 1 = 1#32 := rfl
theorem UInt64.toBitVec_one : toBitVec 1 = 1#64 := rfl
theorem USize.toBitVec_one : toBitVec 1 = 1#System.Platform.numBits := rfl

theorem UInt8.neg_eq_neg_one_mul (a : UInt8) : -a = -1 * a := by
  apply UInt8.toBitVec_inj.1
  rw [UInt8.toBitVec_neg, UInt8.toBitVec_mul, UInt8.toBitVec_neg, UInt8.toBitVec_one, BitVec.neg_eq_neg_one_mul]
theorem UInt16.neg_eq_neg_one_mul (a : UInt16) : -a = -1 * a := by
  apply UInt16.toBitVec_inj.1
  rw [UInt16.toBitVec_neg, UInt16.toBitVec_mul, UInt16.toBitVec_neg, UInt16.toBitVec_one, BitVec.neg_eq_neg_one_mul]
theorem UInt32.neg_eq_neg_one_mul (a : UInt32) : -a = -1 * a := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_neg, UInt32.toBitVec_mul, UInt32.toBitVec_neg, UInt32.toBitVec_one, BitVec.neg_eq_neg_one_mul]
theorem UInt64.neg_eq_neg_one_mul (a : UInt64) : -a = -1 * a := by
  apply UInt64.toBitVec_inj.1
  rw [UInt64.toBitVec_neg, UInt64.toBitVec_mul, UInt64.toBitVec_neg, UInt64.toBitVec_one, BitVec.neg_eq_neg_one_mul]
theorem USize.neg_eq_neg_one_mul (a : USize) : -a = -1 * a := by
  apply USize.toBitVec_inj.1
  rw [USize.toBitVec_neg, USize.toBitVec_mul, USize.toBitVec_neg, USize.toBitVec_one, BitVec.neg_eq_neg_one_mul]

theorem UInt8.sub_eq_add_mul (a b : UInt8) : a - b = a + 255 * b := by
  rw [UInt8.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]
theorem UInt16.sub_eq_add_mul (a b : UInt16) : a - b = a + 65535 * b := by
  rw [UInt16.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]
theorem UInt32.sub_eq_add_mul (a b : UInt32) : a - b = a + 4294967295 * b := by
  rw [UInt32.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]
theorem UInt64.sub_eq_add_mul (a b : UInt64) : a - b = a + 18446744073709551615 * b := by
  rw [UInt64.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]
theorem USize.sub_eq_add_mul (a b : USize) : a - b = a + USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) * b := by
  rw [USize.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]

@[simp] theorem UInt8.ofNat_usizeSize_sub_one : UInt8.ofNat (USize.size - 1) = 255 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt16.ofNat_usizeSize_sub_one : UInt16.ofNat (USize.size - 1) = 65535 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt32.ofNat_usizeSize_sub_one : UInt32.ofNat (USize.size - 1) = 4294967295 := UInt32.toNat.inj (by simp)
@[simp] theorem USize.ofNat_uInt64Size_sub_one : USize.ofNat (UInt64.size - 1) = USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) :=
  USize.toNat.inj (by simp [USize.toNat_ofNat])

@[simp] theorem UInt16.toUInt8_sub (a b : UInt16) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [UInt16.sub_eq_add_neg, UInt8.sub_eq_add_neg]

@[simp] theorem UInt32.toUInt8_sub (a b : UInt32) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [UInt32.sub_eq_add_neg, UInt8.sub_eq_add_neg]
@[simp] theorem UInt32.toUInt16_sub (a b : UInt32) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [UInt32.sub_eq_add_neg, UInt16.sub_eq_add_neg]

@[simp] theorem UInt64.toUInt8_sub (a b : UInt64) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [UInt64.sub_eq_add_neg, UInt8.sub_eq_add_neg]
@[simp] theorem UInt64.toUInt16_sub (a b : UInt64) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [UInt64.sub_eq_add_neg, UInt16.sub_eq_add_neg]
@[simp] theorem UInt64.toUInt32_sub (a b : UInt64) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  simp [UInt64.sub_eq_add_neg, UInt32.sub_eq_add_neg]
@[simp] theorem UInt64.toUSize_sub (a b : UInt64) : (a - b).toUSize = a.toUSize - b.toUSize := by
  simp [UInt64.sub_eq_add_neg, USize.sub_eq_add_neg]

@[simp] theorem USize.toUInt8_sub (a b : USize) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [USize.sub_eq_add_neg, UInt8.sub_eq_add_neg]
@[simp] theorem USize.toUInt16_sub (a b : USize) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [USize.sub_eq_add_neg, UInt16.sub_eq_add_neg]
@[simp] theorem USize.toUInt32_sub (a b : USize) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  simp [USize.sub_eq_add_neg, UInt32.sub_eq_add_neg]

@[simp] theorem UInt8.toUInt16_sub (a b : UInt8) : (a - b).toUInt16 = (a.toUInt16 - b.toUInt16) % 256 := by
  simp [UInt8.toUInt16_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt32_sub (a b : UInt8) : (a - b).toUInt32 = (a.toUInt32 - b.toUInt32) % 256 := by
  simp [UInt8.toUInt32_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt64_sub (a b : UInt8) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 256 := by
  simp [UInt8.toUInt64_eq_mod_256_iff]
@[simp] theorem UInt8.toUSize_sub (a b : UInt8) : (a - b).toUSize = (a.toUSize - b.toUSize) % 256 := by
  simp [UInt8.toUSize_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt32_sub (a b : UInt16) : (a - b).toUInt32 = (a.toUInt32 - b.toUInt32) % 65536 := by
  simp [UInt16.toUInt32_eq_mod_65536_iff]
@[simp] theorem UInt16.toUInt64_sub (a b : UInt16) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 65536 := by
  simp [UInt16.toUInt64_eq_mod_65536_iff]
@[simp] theorem UInt16.toUSize_sub (a b : UInt16) : (a - b).toUSize = (a.toUSize - b.toUSize) % 65536 := by
  simp [UInt16.toUSize_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt64_sub (a b : UInt32) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 4294967296 := by
  simp [UInt32.toUInt64_eq_mod_4294967296_iff]
@[simp] theorem UInt32.toUSize_sub (a b : UInt32) : (a - b).toUSize = (a.toUSize - b.toUSize) % 4294967296 := by
  simp [UInt32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt64_sub (a b : USize) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % UInt64.ofNat USize.size := by
  simp [USize.toUInt64_eq_mod_usizeSize_iff]

@[simp] theorem UInt8.ofBitVec_neg (b : BitVec 8) : UInt8.ofBitVec (-b) = -UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_neg (b : BitVec 16) : UInt16.ofBitVec (-b) = -UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_neg (b : BitVec 32) : UInt32.ofBitVec (-b) = -UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_neg (b : BitVec 64) : UInt64.ofBitVec (-b) = -UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_neg (b : BitVec System.Platform.numBits) : USize.ofBitVec (-b) = -USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofFin_div (a b : Fin UInt8.size) : UInt8.ofFin (a / b) = UInt8.ofFin a / UInt8.ofFin b := rfl
@[simp] theorem UInt16.ofFin_div (a b : Fin UInt16.size) : UInt16.ofFin (a / b) = UInt16.ofFin a / UInt16.ofFin b := rfl
@[simp] theorem UInt32.ofFin_div (a b : Fin UInt32.size) : UInt32.ofFin (a / b) = UInt32.ofFin a / UInt32.ofFin b := rfl
@[simp] theorem UInt64.ofFin_div (a b : Fin UInt64.size) : UInt64.ofFin (a / b) = UInt64.ofFin a / UInt64.ofFin b := rfl
@[simp] theorem USize.ofFin_div (a b : Fin USize.size) : USize.ofFin (a / b) = USize.ofFin a / USize.ofFin b := rfl

@[simp] theorem UInt8.ofBitVec_div (a b : BitVec 8) : UInt8.ofBitVec (a / b) = UInt8.ofBitVec a / UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_div (a b : BitVec 16) : UInt16.ofBitVec (a / b) = UInt16.ofBitVec a / UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_div (a b : BitVec 32) : UInt32.ofBitVec (a / b) = UInt32.ofBitVec a / UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_div (a b : BitVec 64) : UInt64.ofBitVec (a / b) = UInt64.ofBitVec a / UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_div (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a / b) = USize.ofBitVec a / USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofFin_mod (a b : Fin UInt8.size) : UInt8.ofFin (a % b) = UInt8.ofFin a % UInt8.ofFin b := rfl
@[simp] theorem UInt16.ofFin_mod (a b : Fin UInt16.size) : UInt16.ofFin (a % b) = UInt16.ofFin a % UInt16.ofFin b := rfl
@[simp] theorem UInt32.ofFin_mod (a b : Fin UInt32.size) : UInt32.ofFin (a % b) = UInt32.ofFin a % UInt32.ofFin b := rfl
@[simp] theorem UInt64.ofFin_mod (a b : Fin UInt64.size) : UInt64.ofFin (a % b) = UInt64.ofFin a % UInt64.ofFin b := rfl
@[simp] theorem USize.ofFin_mod (a b : Fin USize.size) : USize.ofFin (a % b) = USize.ofFin a % USize.ofFin b := rfl

@[simp] theorem UInt8.ofBitVec_mod (a b : BitVec 8) : UInt8.ofBitVec (a % b) = UInt8.ofBitVec a % UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_mod (a b : BitVec 16) : UInt16.ofBitVec (a % b) = UInt16.ofBitVec a % UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_mod (a b : BitVec 32) : UInt32.ofBitVec (a % b) = UInt32.ofBitVec a % UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_mod (a b : BitVec 64) : UInt64.ofBitVec (a % b) = UInt64.ofBitVec a % UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_mod (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a % b) = USize.ofBitVec a % USize.ofBitVec b := rfl

theorem UInt8.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt8) : UInt8.ofNat a = b ↔ a % 2 ^ 8 = b.toNat := by
  simp [← UInt8.toNat_inj]
theorem UInt16.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt16) : UInt16.ofNat a = b ↔ a % 2 ^ 16 = b.toNat := by
  simp [← UInt16.toNat_inj]
theorem UInt32.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt32) : UInt32.ofNat a = b ↔ a % 2 ^ 32 = b.toNat := by
  simp [← UInt32.toNat_inj]
theorem UInt64.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt64) : UInt64.ofNat a = b ↔ a % 2 ^ 64 = b.toNat := by
  simp [← UInt64.toNat_inj]
theorem USize.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : USize) : USize.ofNat a = b ↔ a % 2 ^ System.Platform.numBits = b.toNat := by
  simp [← USize.toNat_inj]

@[simp] theorem UInt8.ofNat_div {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNat (a / b) = UInt8.ofNat a / UInt8.ofNat b := by
  simp [UInt8.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]
@[simp] theorem UInt16.ofNat_div {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNat (a / b) = UInt16.ofNat a / UInt16.ofNat b := by
  simp [UInt16.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]
@[simp] theorem UInt32.ofNat_div {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNat (a / b) = UInt32.ofNat a / UInt32.ofNat b := by
  simp [UInt32.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]
@[simp] theorem UInt64.ofNat_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat (a / b) = UInt64.ofNat a / UInt64.ofNat b := by
  simp [UInt64.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]
@[simp] theorem USize.ofNat_div {a b : Nat} (ha : a < 2 ^ System.Platform.numBits) (hb : b < 2 ^ System.Platform.numBits) :
    USize.ofNat (a / b) = USize.ofNat a / USize.ofNat b := by
  simp [USize.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]

@[simp] theorem UInt8.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = UInt8.ofNatLT a ha / UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat, UInt8.ofNat_div ha hb]
@[simp] theorem UInt16.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = UInt16.ofNatLT a ha / UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat, UInt16.ofNat_div ha hb]
@[simp] theorem UInt32.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = UInt32.ofNatLT a ha / UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat, UInt32.ofNat_div ha hb]
@[simp] theorem UInt64.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = UInt64.ofNatLT a ha / UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat, UInt64.ofNat_div ha hb]
@[simp] theorem USize.ofNatLT_div {a b : Nat} (ha : a < 2 ^ System.Platform.numBits) (hb : b < 2 ^ System.Platform.numBits) :
    USize.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = USize.ofNatLT a ha / USize.ofNatLT b hb := by
  simp [USize.ofNatLT_eq_ofNat, USize.ofNat_div ha hb]

@[simp] theorem UInt8.ofNat_mod {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNat (a % b) = UInt8.ofNat a % UInt8.ofNat b := by
  simp [UInt8.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]
@[simp] theorem UInt16.ofNat_mod {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNat (a % b) = UInt16.ofNat a % UInt16.ofNat b := by
  simp [UInt16.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]
@[simp] theorem UInt32.ofNat_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNat (a % b) = UInt32.ofNat a % UInt32.ofNat b := by
  simp [UInt32.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]
@[simp] theorem UInt64.ofNat_mod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat (a % b) = UInt64.ofNat a % UInt64.ofNat b := by
  simp [UInt64.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]
@[simp] theorem USize.ofNat_mod {a b : Nat} (ha : a < 2 ^ System.Platform.numBits) (hb : b < 2 ^ System.Platform.numBits) :
    USize.ofNat (a % b) = USize.ofNat a % USize.ofNat b := by
  simp [USize.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]

@[simp] theorem UInt8.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = UInt8.ofNatLT a ha % UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat, UInt8.ofNat_mod ha hb]
@[simp] theorem UInt16.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = UInt16.ofNatLT a ha % UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat, UInt16.ofNat_mod ha hb]
@[simp] theorem UInt32.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = UInt32.ofNatLT a ha % UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat, UInt32.ofNat_mod ha hb]
@[simp] theorem UInt64.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = UInt64.ofNatLT a ha % UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat, UInt64.ofNat_mod ha hb]
@[simp] theorem USize.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ System.Platform.numBits) (hb : b < 2 ^ System.Platform.numBits) :
    USize.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = USize.ofNatLT a ha % USize.ofNatLT b hb := by
  simp [USize.ofNatLT_eq_ofNat, USize.ofNat_mod ha hb]

@[simp] theorem UInt8.ofNat_add (a b : Nat) : UInt8.ofNat (a + b) = UInt8.ofNat a + UInt8.ofNat b := by
  simp [UInt8.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt16.ofNat_add (a b : Nat) : UInt16.ofNat (a + b) = UInt16.ofNat a + UInt16.ofNat b := by
  simp [UInt16.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt32.ofNat_add (a b : Nat) : UInt32.ofNat (a + b) = UInt32.ofNat a + UInt32.ofNat b := by
  simp [UInt32.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt64.ofNat_add (a b : Nat) : UInt64.ofNat (a + b) = UInt64.ofNat a + UInt64.ofNat b := by
  simp [UInt64.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem USize.ofNat_add (a b : Nat) : USize.ofNat (a + b) = USize.ofNat a + USize.ofNat b := by
  simp [USize.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem UInt8.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 8) :
    UInt8.ofNatLT (a + b) hab = UInt8.ofNatLT a (Nat.lt_of_add_right_lt hab) + UInt8.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [UInt8.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 16) :
    UInt16.ofNatLT (a + b) hab = UInt16.ofNatLT a (Nat.lt_of_add_right_lt hab) + UInt16.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 32) :
    UInt32.ofNatLT (a + b) hab = UInt32.ofNatLT a (Nat.lt_of_add_right_lt hab) + UInt32.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt64.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 64) :
    UInt64.ofNatLT (a + b) hab = UInt64.ofNatLT a (Nat.lt_of_add_right_lt hab) + UInt64.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [UInt64.ofNatLT_eq_ofNat]
@[simp] theorem USize.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ System.Platform.numBits) :
    USize.ofNatLT (a + b) hab = USize.ofNatLT a (Nat.lt_of_add_right_lt hab) + USize.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofFin_add (a b : Fin UInt8.size) : UInt8.ofFin (a + b) = UInt8.ofFin a + UInt8.ofFin b := rfl
@[simp] theorem UInt16.ofFin_add (a b : Fin UInt16.size) : UInt16.ofFin (a + b) = UInt16.ofFin a + UInt16.ofFin b := rfl
@[simp] theorem UInt32.ofFin_add (a b : Fin UInt32.size) : UInt32.ofFin (a + b) = UInt32.ofFin a + UInt32.ofFin b := rfl
@[simp] theorem UInt64.ofFin_add (a b : Fin UInt64.size) : UInt64.ofFin (a + b) = UInt64.ofFin a + UInt64.ofFin b := rfl
@[simp] theorem USize.ofFin_add (a b : Fin USize.size) : USize.ofFin (a + b) = USize.ofFin a + USize.ofFin b := rfl

@[simp] theorem UInt8.ofBitVec_add (a b : BitVec 8) : UInt8.ofBitVec (a + b) = UInt8.ofBitVec a + UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_add (a b : BitVec 16) : UInt16.ofBitVec (a + b) = UInt16.ofBitVec a + UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_add (a b : BitVec 32) : UInt32.ofBitVec (a + b) = UInt32.ofBitVec a + UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_add (a b : BitVec 64) : UInt64.ofBitVec (a + b) = UInt64.ofBitVec a + UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_add (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a + b) = USize.ofBitVec a + USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofFin_sub (a b : Fin UInt8.size) : UInt8.ofFin (a - b) = UInt8.ofFin a - UInt8.ofFin b := rfl
@[simp] theorem UInt16.ofFin_sub (a b : Fin UInt16.size) : UInt16.ofFin (a - b) = UInt16.ofFin a - UInt16.ofFin b := rfl
@[simp] theorem UInt32.ofFin_sub (a b : Fin UInt32.size) : UInt32.ofFin (a - b) = UInt32.ofFin a - UInt32.ofFin b := rfl
@[simp] theorem UInt64.ofFin_sub (a b : Fin UInt64.size) : UInt64.ofFin (a - b) = UInt64.ofFin a - UInt64.ofFin b := rfl
@[simp] theorem USize.ofFin_sub (a b : Fin USize.size) : USize.ofFin (a - b) = USize.ofFin a - USize.ofFin b := rfl

@[simp] theorem UInt8.ofBitVec_sub (a b : BitVec 8) : UInt8.ofBitVec (a - b) = UInt8.ofBitVec a - UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_sub (a b : BitVec 16) : UInt16.ofBitVec (a - b) = UInt16.ofBitVec a - UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_sub (a b : BitVec 32) : UInt32.ofBitVec (a - b) = UInt32.ofBitVec a - UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_sub (a b : BitVec 64) : UInt64.ofBitVec (a - b) = UInt64.ofBitVec a - UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_sub (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a - b) = USize.ofBitVec a - USize.ofBitVec b := rfl

@[simp] protected theorem UInt8.add_sub_cancel (a b : UInt8) : a + b - b = a := UInt8.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem UInt16.add_sub_cancel (a b : UInt16) : a + b - b = a := UInt16.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem UInt32.add_sub_cancel (a b : UInt32) : a + b - b = a := UInt32.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem UInt64.add_sub_cancel (a b : UInt64) : a + b - b = a := UInt64.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem USize.add_sub_cancel (a b : USize) : a + b - b = a := USize.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

theorem UInt8.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt8.ofNat (a - b) = UInt8.ofNat a - UInt8.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ UInt8.ofNat_add (a - b) b :), UInt8.add_sub_cancel]
theorem UInt16.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt16.ofNat (a - b) = UInt16.ofNat a - UInt16.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ UInt16.ofNat_add (a - b) b :), UInt16.add_sub_cancel]
theorem UInt32.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt32.ofNat (a - b) = UInt32.ofNat a - UInt32.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ UInt32.ofNat_add (a - b) b :), UInt32.add_sub_cancel]
theorem UInt64.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt64.ofNat (a - b) = UInt64.ofNat a - UInt64.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ UInt64.ofNat_add (a - b) b :), UInt64.add_sub_cancel]
theorem USize.ofNat_sub {a b : Nat} (hab : b ≤ a) : USize.ofNat (a - b) = USize.ofNat a - USize.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ USize.ofNat_add (a - b) b :), USize.add_sub_cancel]

theorem UInt8.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 8) (hab : b ≤ a) :
    UInt8.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt8.ofNatLT a ha - UInt8.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [UInt8.ofNatLT_eq_ofNat, UInt8.ofNat_sub hab]
theorem UInt16.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 16) (hab : b ≤ a) :
    UInt16.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt16.ofNatLT a ha - UInt16.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [UInt16.ofNatLT_eq_ofNat, UInt16.ofNat_sub hab]
theorem UInt32.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 32) (hab : b ≤ a) :
    UInt32.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt32.ofNatLT a ha - UInt32.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [UInt32.ofNatLT_eq_ofNat, UInt32.ofNat_sub hab]
theorem UInt64.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 64) (hab : b ≤ a) :
    UInt64.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt64.ofNatLT a ha - UInt64.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [UInt64.ofNatLT_eq_ofNat, UInt64.ofNat_sub hab]
theorem USize.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ System.Platform.numBits) (hab : b ≤ a) :
    USize.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = USize.ofNatLT a ha - USize.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [USize.ofNatLT_eq_ofNat, USize.ofNat_sub hab]

@[simp] theorem UInt8.ofNat_mul (a b : Nat) : UInt8.ofNat (a * b) = UInt8.ofNat a * UInt8.ofNat b := by
  simp [UInt8.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt16.ofNat_mul (a b : Nat) : UInt16.ofNat (a * b) = UInt16.ofNat a * UInt16.ofNat b := by
  simp [UInt16.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt32.ofNat_mul (a b : Nat) : UInt32.ofNat (a * b) = UInt32.ofNat a * UInt32.ofNat b := by
  simp [UInt32.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem UInt64.ofNat_mul (a b : Nat) : UInt64.ofNat (a * b) = UInt64.ofNat a * UInt64.ofNat b := by
  simp [UInt64.ofNat_eq_iff_mod_eq_toNat]
@[simp] theorem USize.ofNat_mul (a b : Nat) : USize.ofNat (a * b) = USize.ofNat a * USize.ofNat b := by
  simp [USize.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem UInt8.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) (hab : a * b < 2 ^ 8) :
    UInt8.ofNatLT (a * b) hab = UInt8.ofNatLT a ha * UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (hab : a * b < 2 ^ 16) :
    UInt16.ofNatLT (a * b) hab = UInt16.ofNatLT a ha * UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hab : a * b < 2 ^ 32) :
    UInt32.ofNatLT (a * b) hab = UInt32.ofNatLT a ha * UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt64.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a * b < 2 ^ 64) :
    UInt64.ofNatLT (a * b) hab = UInt64.ofNatLT a ha * UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat]
@[simp] theorem USize.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ System.Platform.numBits)
    (hb : b < 2 ^ System.Platform.numBits) (hab : a * b < 2 ^ System.Platform.numBits) :
    USize.ofNatLT (a * b) hab = USize.ofNatLT a ha * USize.ofNatLT b hb := by
  simp [USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofFin_mul (a b : Fin UInt8.size) : UInt8.ofFin (a * b) = UInt8.ofFin a * UInt8.ofFin b := rfl
@[simp] theorem UInt16.ofFin_mul (a b : Fin UInt16.size) : UInt16.ofFin (a * b) = UInt16.ofFin a * UInt16.ofFin b := rfl
@[simp] theorem UInt32.ofFin_mul (a b : Fin UInt32.size) : UInt32.ofFin (a * b) = UInt32.ofFin a * UInt32.ofFin b := rfl
@[simp] theorem UInt64.ofFin_mul (a b : Fin UInt64.size) : UInt64.ofFin (a * b) = UInt64.ofFin a * UInt64.ofFin b := rfl
@[simp] theorem USize.ofFin_mul (a b : Fin USize.size) : USize.ofFin (a * b) = USize.ofFin a * USize.ofFin b := rfl

@[simp] theorem UInt8.ofBitVec_mul (a b : BitVec 8) : UInt8.ofBitVec (a * b) = UInt8.ofBitVec a * UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_mul (a b : BitVec 16) : UInt16.ofBitVec (a * b) = UInt16.ofBitVec a * UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_mul (a b : BitVec 32) : UInt32.ofBitVec (a * b) = UInt32.ofBitVec a * UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_mul (a b : BitVec 64) : UInt64.ofBitVec (a * b) = UInt64.ofBitVec a * UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_mul (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a * b) = USize.ofBitVec a * USize.ofBitVec b := rfl

theorem UInt8.ofFin_lt_iff_lt {a b : Fin UInt8.size} : UInt8.ofFin a < UInt8.ofFin b ↔ a < b := Iff.rfl
theorem UInt16.ofFin_lt_iff_lt {a b : Fin UInt16.size} : UInt16.ofFin a < UInt16.ofFin b ↔ a < b := Iff.rfl
theorem UInt32.ofFin_lt_iff_lt {a b : Fin UInt32.size} : UInt32.ofFin a < UInt32.ofFin b ↔ a < b := Iff.rfl
theorem UInt64.ofFin_lt_iff_lt {a b : Fin UInt64.size} : UInt64.ofFin a < UInt64.ofFin b ↔ a < b := Iff.rfl
theorem USize.ofFin_lt_iff_lt {a b : Fin USize.size} : USize.ofFin a < USize.ofFin b ↔ a < b := Iff.rfl

theorem UInt8.ofFin_le_iff_le {a b : Fin UInt8.size} : UInt8.ofFin a ≤ UInt8.ofFin b ↔ a ≤ b := Iff.rfl
theorem UInt16.ofFin_le_iff_le {a b : Fin UInt16.size} : UInt16.ofFin a ≤ UInt16.ofFin b ↔ a ≤ b := Iff.rfl
theorem UInt32.ofFin_le_iff_le {a b : Fin UInt32.size} : UInt32.ofFin a ≤ UInt32.ofFin b ↔ a ≤ b := Iff.rfl
theorem UInt64.ofFin_le_iff_le {a b : Fin UInt64.size} : UInt64.ofFin a ≤ UInt64.ofFin b ↔ a ≤ b := Iff.rfl
theorem USize.ofFin_le_iff_le {a b : Fin USize.size} : USize.ofFin a ≤ USize.ofFin b ↔ a ≤ b := Iff.rfl

theorem UInt8.ofBitVec_lt_iff_lt {a b : BitVec 8} : UInt8.ofBitVec a < UInt8.ofBitVec b ↔ a < b := Iff.rfl
theorem UInt16.ofBitVec_lt_iff_lt {a b : BitVec 16} : UInt16.ofBitVec a < UInt16.ofBitVec b ↔ a < b := Iff.rfl
theorem UInt32.ofBitVec_lt_iff_lt {a b : BitVec 32} : UInt32.ofBitVec a < UInt32.ofBitVec b ↔ a < b := Iff.rfl
theorem UInt64.ofBitVec_lt_iff_lt {a b : BitVec 64} : UInt64.ofBitVec a < UInt64.ofBitVec b ↔ a < b := Iff.rfl
theorem USize.ofBitVec_lt_iff_lt {a b : BitVec System.Platform.numBits} : USize.ofBitVec a < USize.ofBitVec b ↔ a < b := Iff.rfl

theorem UInt8.ofBitVec_le_iff_le {a b : BitVec 8} : UInt8.ofBitVec a ≤ UInt8.ofBitVec b ↔ a ≤ b := Iff.rfl
theorem UInt16.ofBitVec_le_iff_le {a b : BitVec 16} : UInt16.ofBitVec a ≤ UInt16.ofBitVec b ↔ a ≤ b := Iff.rfl
theorem UInt32.ofBitVec_le_iff_le {a b : BitVec 32} : UInt32.ofBitVec a ≤ UInt32.ofBitVec b ↔ a ≤ b := Iff.rfl
theorem UInt64.ofBitVec_le_iff_le {a b : BitVec 64} : UInt64.ofBitVec a ≤ UInt64.ofBitVec b ↔ a ≤ b := Iff.rfl
theorem USize.ofBitVec_le_iff_le {a b : BitVec System.Platform.numBits} : USize.ofBitVec a ≤ USize.ofBitVec b ↔ a ≤ b := Iff.rfl

theorem UInt8.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt8.size) (hb : b < UInt8.size) :
    UInt8.ofNatLT a ha < UInt8.ofNatLT b hb ↔ a < b := Iff.rfl
theorem UInt16.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt16.size) (hb : b < UInt16.size) :
    UInt16.ofNatLT a ha < UInt16.ofNatLT b hb ↔ a < b := Iff.rfl
theorem UInt32.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNatLT a ha < UInt32.ofNatLT b hb ↔ a < b := Iff.rfl
theorem UInt64.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size) :
    UInt64.ofNatLT a ha < UInt64.ofNatLT b hb ↔ a < b := Iff.rfl
theorem USize.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) :
    USize.ofNatLT a ha < USize.ofNatLT b hb ↔ a < b := Iff.rfl

theorem UInt8.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt8.size) (hb : b < UInt8.size) :
    UInt8.ofNatLT a ha ≤ UInt8.ofNatLT b hb ↔ a ≤ b := Iff.rfl
theorem UInt16.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt16.size) (hb : b < UInt16.size) :
    UInt16.ofNatLT a ha ≤ UInt16.ofNatLT b hb ↔ a ≤ b := Iff.rfl
theorem UInt32.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNatLT a ha ≤ UInt32.ofNatLT b hb ↔ a ≤ b := Iff.rfl
theorem UInt64.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size) :
    UInt64.ofNatLT a ha ≤ UInt64.ofNatLT b hb ↔ a ≤ b := Iff.rfl
theorem USize.ofNatLT_le_iff_le {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) :
    USize.ofNatLT a ha ≤ USize.ofNatLT b hb ↔ a ≤ b := Iff.rfl

theorem UInt8.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt8.size) (hb : b < UInt8.size) :
    UInt8.ofNat a < UInt8.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]
theorem UInt16.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt16.size) (hb : b < UInt16.size) :
    UInt16.ofNat a < UInt16.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]
theorem UInt32.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNat a < UInt32.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]
theorem UInt64.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size) :
    UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]
theorem USize.ofNat_lt_iff_lt {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) :
    USize.ofNat a < USize.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]

theorem UInt8.ofNat_le_iff_le {a b : Nat} (ha : a < UInt8.size) (hb : b < UInt8.size) :
    UInt8.ofNat a ≤ UInt8.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]
theorem UInt16.ofNat_le_iff_le {a b : Nat} (ha : a < UInt16.size) (hb : b < UInt16.size) :
    UInt16.ofNat a ≤ UInt16.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]
theorem UInt32.ofNat_le_iff_le {a b : Nat} (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNat a ≤ UInt32.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]
theorem UInt64.ofNat_le_iff_le {a b : Nat} (ha : a < UInt64.size) (hb : b < UInt64.size) :
    UInt64.ofNat a ≤ UInt64.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]
theorem USize.ofNat_le_iff_le {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) :
    USize.ofNat a ≤ USize.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]

theorem UInt8.toNat_one : (1 : UInt8).toNat = 1 := rfl
theorem UInt16.toNat_one : (1 : UInt16).toNat = 1 := rfl
theorem UInt32.toNat_one : (1 : UInt32).toNat = 1 := rfl
theorem UInt64.toNat_one : (1 : UInt64).toNat = 1 := rfl
theorem USize.toNat_one : (1 : USize).toNat = 1 := by simp

theorem UInt8.zero_lt_one : (0 : UInt8) < 1 := by simp
theorem UInt16.zero_lt_one : (0 : UInt16) < 1 := by simp
theorem UInt32.zero_lt_one : (0 : UInt32) < 1 := by simp
theorem UInt64.zero_lt_one : (0 : UInt64) < 1 := by simp
theorem USize.zero_lt_one : (0 : USize) < 1 := by simp [lt_iff_toNat_lt]

theorem UInt8.zero_ne_one : (0 : UInt8) ≠ 1 := by simp
theorem UInt16.zero_ne_one : (0 : UInt16) ≠ 1 := by simp
theorem UInt32.zero_ne_one : (0 : UInt32) ≠ 1 := by simp
theorem UInt64.zero_ne_one : (0 : UInt64) ≠ 1 := by simp
theorem USize.zero_ne_one : (0 : USize) ≠ 1 := by simp [← USize.toNat_inj]

protected theorem UInt8.add_assoc (a b c : UInt8) : a + b + c = a + (b + c) :=
  UInt8.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem UInt16.add_assoc (a b c : UInt16) : a + b + c = a + (b + c) :=
  UInt16.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem UInt32.add_assoc (a b c : UInt32) : a + b + c = a + (b + c) :=
  UInt32.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem UInt64.add_assoc (a b c : UInt64) : a + b + c = a + (b + c) :=
  UInt64.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem USize.add_assoc (a b c : USize) : a + b + c = a + (b + c) :=
  USize.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := UInt8) (· + ·) := ⟨UInt8.add_assoc⟩
instance : Std.Associative (α := UInt16) (· + ·) := ⟨UInt16.add_assoc⟩
instance : Std.Associative (α := UInt32) (· + ·) := ⟨UInt32.add_assoc⟩
instance : Std.Associative (α := UInt64) (· + ·) := ⟨UInt64.add_assoc⟩
instance : Std.Associative (α := USize) (· + ·) := ⟨USize.add_assoc⟩

protected theorem UInt8.add_comm (a b : UInt8) : a + b = b + a := UInt8.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem UInt16.add_comm (a b : UInt16) : a + b = b + a := UInt16.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem UInt32.add_comm (a b : UInt32) : a + b = b + a := UInt32.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem UInt64.add_comm (a b : UInt64) : a + b = b + a := UInt64.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem USize.add_comm (a b : USize) : a + b = b + a := USize.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := UInt8) (· + ·) := ⟨UInt8.add_comm⟩
instance : Std.Commutative (α := UInt16) (· + ·) := ⟨UInt16.add_comm⟩
instance : Std.Commutative (α := UInt32) (· + ·) := ⟨UInt32.add_comm⟩
instance : Std.Commutative (α := UInt64) (· + ·) := ⟨UInt64.add_comm⟩
instance : Std.Commutative (α := USize) (· + ·) := ⟨USize.add_comm⟩

@[simp] protected theorem UInt8.add_zero (a : UInt8) : a + 0 = a := UInt8.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem UInt16.add_zero (a : UInt16) : a + 0 = a := UInt16.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem UInt32.add_zero (a : UInt32) : a + 0 = a := UInt32.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem UInt64.add_zero (a : UInt64) : a + 0 = a := UInt64.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem USize.add_zero (a : USize) : a + 0 = a := USize.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem UInt8.zero_add (a : UInt8) : 0 + a = a := UInt8.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem UInt16.zero_add (a : UInt16) : 0 + a = a := UInt16.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem UInt32.zero_add (a : UInt32) : 0 + a = a := UInt32.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem UInt64.zero_add (a : UInt64) : 0 + a = a := UInt64.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem USize.zero_add (a : USize) : 0 + a = a := USize.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := UInt8) (· + ·) 0 where
  left_id := UInt8.zero_add
  right_id := UInt8.add_zero
instance : Std.LawfulIdentity (α := UInt16) (· + ·) 0 where
  left_id := UInt16.zero_add
  right_id := UInt16.add_zero
instance : Std.LawfulIdentity (α := UInt32) (· + ·) 0 where
  left_id := UInt32.zero_add
  right_id := UInt32.add_zero
instance : Std.LawfulIdentity (α := UInt64) (· + ·) 0 where
  left_id := UInt64.zero_add
  right_id := UInt64.add_zero
instance : Std.LawfulIdentity (α := USize) (· + ·) 0 where
  left_id := USize.zero_add
  right_id := USize.add_zero

@[simp] protected theorem UInt8.sub_zero (a : UInt8) : a - 0 = a := UInt8.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem UInt16.sub_zero (a : UInt16) : a - 0 = a := UInt16.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem UInt32.sub_zero (a : UInt32) : a - 0 = a := UInt32.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem UInt64.sub_zero (a : UInt64) : a - 0 = a := UInt64.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem USize.sub_zero (a : USize) : a - 0 = a := USize.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem UInt8.zero_sub (a : UInt8) : 0 - a = -a := UInt8.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem UInt16.zero_sub (a : UInt16) : 0 - a = -a := UInt16.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem UInt32.zero_sub (a : UInt32) : 0 - a = -a := UInt32.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem UInt64.zero_sub (a : UInt64) : 0 - a = -a := UInt64.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem USize.zero_sub (a : USize) : 0 - a = -a := USize.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem UInt8.sub_self (a : UInt8) : a - a = 0 := UInt8.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem UInt16.sub_self (a : UInt16) : a - a = 0 := UInt16.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem UInt32.sub_self (a : UInt32) : a - a = 0 := UInt32.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem UInt64.sub_self (a : UInt64) : a - a = 0 := UInt64.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem USize.sub_self (a : USize) : a - a = 0 := USize.toBitVec_inj.1 (BitVec.sub_self _)

@[simp] protected theorem UInt8.neg_zero : -(0 : UInt8) = 0 := rfl
@[simp] protected theorem UInt16.neg_zero : -(0 : UInt16) = 0 := rfl
@[simp] protected theorem UInt32.neg_zero : -(0 : UInt32) = 0 := rfl
@[simp] protected theorem UInt64.neg_zero : -(0 : UInt64) = 0 := rfl
@[simp] protected theorem USize.neg_zero : -(0 : USize) = 0 := USize.toBitVec_inj.1 (BitVec.neg_zero _)

@[simp] protected theorem UInt8.sub_add_cancel (a b : UInt8) : a - b + b = a :=
  UInt8.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem UInt16.sub_add_cancel (a b : UInt16) : a - b + b = a :=
  UInt16.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem UInt32.sub_add_cancel (a b : UInt32) : a - b + b = a :=
  UInt32.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem UInt64.sub_add_cancel (a b : UInt64) : a - b + b = a :=
  UInt64.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem USize.sub_add_cancel (a b : USize) : a - b + b = a :=
  USize.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem UInt8.eq_sub_iff_add_eq {a b c : UInt8} : a = c - b ↔ a + b = c := by
  simpa [← UInt8.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem UInt16.eq_sub_iff_add_eq {a b c : UInt16} : a = c - b ↔ a + b = c := by
  simpa [← UInt16.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem UInt32.eq_sub_iff_add_eq {a b c : UInt32} : a = c - b ↔ a + b = c := by
  simpa [← UInt32.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem UInt64.eq_sub_iff_add_eq {a b c : UInt64} : a = c - b ↔ a + b = c := by
  simpa [← UInt64.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem USize.eq_sub_iff_add_eq {a b c : USize} : a = c - b ↔ a + b = c := by
  simpa [← USize.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem UInt8.sub_eq_iff_eq_add {a b c : UInt8} : a - b = c ↔ a = c + b := by
  simpa [← UInt8.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem UInt16.sub_eq_iff_eq_add {a b c : UInt16} : a - b = c ↔ a = c + b := by
  simpa [← UInt16.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem UInt32.sub_eq_iff_eq_add {a b c : UInt32} : a - b = c ↔ a = c + b := by
  simpa [← UInt32.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem UInt64.sub_eq_iff_eq_add {a b c : UInt64} : a - b = c ↔ a = c + b := by
  simpa [← UInt64.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem USize.sub_eq_iff_eq_add {a b c : USize} : a - b = c ↔ a = c + b := by
  simpa [← USize.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem UInt8.neg_neg {a : UInt8} : - -a = a := UInt8.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem UInt16.neg_neg {a : UInt16} : - -a = a := UInt16.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem UInt32.neg_neg {a : UInt32} : - -a = a := UInt32.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem UInt64.neg_neg {a : UInt64} : - -a = a := UInt64.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem USize.neg_neg {a : USize} : - -a = a := USize.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem UInt8.neg_inj {a b : UInt8} : -a = -b ↔ a = b := by simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.neg_inj {a b : UInt16} : -a = -b ↔ a = b := by simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.neg_inj {a b : UInt32} : -a = -b ↔ a = b := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.neg_inj {a b : UInt64} : -a = -b ↔ a = b := by simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.neg_inj {a b : USize} : -a = -b ↔ a = b := by simp [← USize.toBitVec_inj]

@[simp] protected theorem UInt8.neg_ne_zero {a : UInt8} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.neg_ne_zero {a : UInt16} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.neg_ne_zero {a : UInt32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.neg_ne_zero {a : UInt64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.neg_ne_zero {a : USize} : -a ≠ 0 ↔ a ≠ 0 := by simp [← USize.toBitVec_inj]

protected theorem UInt8.neg_add {a b : UInt8} : - (a + b) = -a - b := UInt8.toBitVec_inj.1 BitVec.neg_add
protected theorem UInt16.neg_add {a b : UInt16} : - (a + b) = -a - b := UInt16.toBitVec_inj.1 BitVec.neg_add
protected theorem UInt32.neg_add {a b : UInt32} : - (a + b) = -a - b := UInt32.toBitVec_inj.1 BitVec.neg_add
protected theorem UInt64.neg_add {a b : UInt64} : - (a + b) = -a - b := UInt64.toBitVec_inj.1 BitVec.neg_add
protected theorem USize.neg_add {a b : USize} : - (a + b) = -a - b := USize.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem UInt8.sub_neg {a b : UInt8} : a - -b = a + b := UInt8.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem UInt16.sub_neg {a b : UInt16} : a - -b = a + b := UInt16.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem UInt32.sub_neg {a b : UInt32} : a - -b = a + b := UInt32.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem UInt64.sub_neg {a b : UInt64} : a - -b = a + b := UInt64.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem USize.sub_neg {a b : USize} : a - -b = a + b := USize.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem UInt8.neg_sub {a b : UInt8} : -(a - b) = b - a := by
  rw [UInt8.sub_eq_add_neg, UInt8.neg_add, UInt8.sub_neg, UInt8.add_comm, ← UInt8.sub_eq_add_neg]
@[simp] protected theorem UInt16.neg_sub {a b : UInt16} : -(a - b) = b - a := by
  rw [UInt16.sub_eq_add_neg, UInt16.neg_add, UInt16.sub_neg, UInt16.add_comm, ← UInt16.sub_eq_add_neg]
@[simp] protected theorem UInt32.neg_sub {a b : UInt32} : -(a - b) = b - a := by
  rw [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.sub_neg, UInt32.add_comm, ← UInt32.sub_eq_add_neg]
@[simp] protected theorem UInt64.neg_sub {a b : UInt64} : -(a - b) = b - a := by
  rw [UInt64.sub_eq_add_neg, UInt64.neg_add, UInt64.sub_neg, UInt64.add_comm, ← UInt64.sub_eq_add_neg]
@[simp] protected theorem USize.neg_sub {a b : USize} : -(a - b) = b - a := by
  rw [USize.sub_eq_add_neg, USize.neg_add, USize.sub_neg, USize.add_comm, ← USize.sub_eq_add_neg]

@[simp] protected theorem UInt8.add_left_inj {a b : UInt8} (c : UInt8) : (a + c = b + c) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.add_left_inj {a b : UInt16} (c : UInt16) : (a + c = b + c) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.add_left_inj {a b : UInt32} (c : UInt32) : (a + c = b + c) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.add_left_inj {a b : UInt64} (c : UInt64) : (a + c = b + c) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.add_left_inj {a b : USize} (c : USize) : (a + c = b + c) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] protected theorem UInt8.add_right_inj {a b : UInt8} (c : UInt8) : (c + a = c + b) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.add_right_inj {a b : UInt16} (c : UInt16) : (c + a = c + b) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.add_right_inj {a b : UInt32} (c : UInt32) : (c + a = c + b) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.add_right_inj {a b : UInt64} (c : UInt64) : (c + a = c + b) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.add_right_inj {a b : USize} (c : USize) : (c + a = c + b) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] protected theorem UInt8.sub_left_inj {a b : UInt8} (c : UInt8) : (a - c = b - c) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.sub_left_inj {a b : UInt16} (c : UInt16) : (a - c = b - c) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.sub_left_inj {a b : UInt32} (c : UInt32) : (a - c = b - c) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.sub_left_inj {a b : UInt64} (c : UInt64) : (a - c = b - c) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.sub_left_inj {a b : USize} (c : USize) : (a - c = b - c) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] protected theorem UInt8.sub_right_inj {a b : UInt8} (c : UInt8) : (c - a = c - b) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.sub_right_inj {a b : UInt16} (c : UInt16) : (c - a = c - b) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.sub_right_inj {a b : UInt32} (c : UInt32) : (c - a = c - b) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.sub_right_inj {a b : UInt64} (c : UInt64) : (c - a = c - b) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] protected theorem USize.sub_right_inj {a b : USize} (c : USize) : (c - a = c - b) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.add_eq_right {a b : UInt8} : a + b = b ↔ a = 0 := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.add_eq_right {a b : UInt16} : a + b = b ↔ a = 0 := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.add_eq_right {a b : UInt32} : a + b = b ↔ a = 0 := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.add_eq_right {a b : UInt64} : a + b = b ↔ a = 0 := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.add_eq_right {a b : USize} : a + b = b ↔ a = 0 := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.add_eq_left {a b : UInt8} : a + b = a ↔ b = 0 := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.add_eq_left {a b : UInt16} : a + b = a ↔ b = 0 := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.add_eq_left {a b : UInt32} : a + b = a ↔ b = 0 := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.add_eq_left {a b : UInt64} : a + b = a ↔ b = 0 := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.add_eq_left {a b : USize} : a + b = a ↔ b = 0 := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.right_eq_add {a b : UInt8} : b = a + b ↔ a = 0 := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.right_eq_add {a b : UInt16} : b = a + b ↔ a = 0 := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.right_eq_add {a b : UInt32} : b = a + b ↔ a = 0 := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.right_eq_add {a b : UInt64} : b = a + b ↔ a = 0 := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.right_eq_add {a b : USize} : b = a + b ↔ a = 0 := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.left_eq_add {a b : UInt8} : a = a + b ↔ b = 0 := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.left_eq_add {a b : UInt16} : a = a + b ↔ b = 0 := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.left_eq_add {a b : UInt32} : a = a + b ↔ b = 0 := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.left_eq_add {a b : UInt64} : a = a + b ↔ b = 0 := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.left_eq_add {a b : USize} : a = a + b ↔ b = 0 := by
  simp [← USize.toBitVec_inj]

protected theorem UInt8.mul_comm (a b : UInt8) : a * b = b * a := UInt8.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem UInt16.mul_comm (a b : UInt16) : a * b = b * a := UInt16.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem UInt32.mul_comm (a b : UInt32) : a * b = b * a := UInt32.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem UInt64.mul_comm (a b : UInt64) : a * b = b * a := UInt64.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem USize.mul_comm (a b : USize) : a * b = b * a := USize.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := UInt8) (· * ·) := ⟨UInt8.mul_comm⟩
instance : Std.Commutative (α := UInt16) (· * ·) := ⟨UInt16.mul_comm⟩
instance : Std.Commutative (α := UInt32) (· * ·) := ⟨UInt32.mul_comm⟩
instance : Std.Commutative (α := UInt64) (· * ·) := ⟨UInt64.mul_comm⟩
instance : Std.Commutative (α := USize) (· * ·) := ⟨USize.mul_comm⟩

protected theorem UInt8.mul_assoc (a b c : UInt8) : a * b * c = a * (b * c) := UInt8.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem UInt16.mul_assoc (a b c : UInt16) : a * b * c = a * (b * c) := UInt16.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem UInt32.mul_assoc (a b c : UInt32) : a * b * c = a * (b * c) := UInt32.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem UInt64.mul_assoc (a b c : UInt64) : a * b * c = a * (b * c) := UInt64.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem USize.mul_assoc (a b c : USize) : a * b * c = a * (b * c) := USize.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := UInt8) (· * ·) := ⟨UInt8.mul_assoc⟩
instance : Std.Associative (α := UInt16) (· * ·) := ⟨UInt16.mul_assoc⟩
instance : Std.Associative (α := UInt32) (· * ·) := ⟨UInt32.mul_assoc⟩
instance : Std.Associative (α := UInt64) (· * ·) := ⟨UInt64.mul_assoc⟩
instance : Std.Associative (α := USize) (· * ·) := ⟨USize.mul_assoc⟩

@[simp] theorem UInt8.mul_one (a : UInt8) : a * 1 = a := UInt8.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem UInt16.mul_one (a : UInt16) : a * 1 = a := UInt16.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem UInt32.mul_one (a : UInt32) : a * 1 = a := UInt32.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem UInt64.mul_one (a : UInt64) : a * 1 = a := UInt64.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem USize.mul_one (a : USize) : a * 1 = a := USize.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem UInt8.one_mul (a : UInt8) : 1 * a = a := UInt8.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem UInt16.one_mul (a : UInt16) : 1 * a = a := UInt16.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem UInt32.one_mul (a : UInt32) : 1 * a = a := UInt32.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem UInt64.one_mul (a : UInt64) : 1 * a = a := UInt64.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem USize.one_mul (a : USize) : 1 * a = a := USize.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := UInt8) (· * ·) 1 where
  right_id := UInt8.mul_one
instance : Std.LawfulCommIdentity (α := UInt16) (· * ·) 1 where
  right_id := UInt16.mul_one
instance : Std.LawfulCommIdentity (α := UInt32) (· * ·) 1 where
  right_id := UInt32.mul_one
instance : Std.LawfulCommIdentity (α := UInt64) (· * ·) 1 where
  right_id := UInt64.mul_one
instance : Std.LawfulCommIdentity (α := USize) (· * ·) 1 where
  right_id := USize.mul_one

@[simp] theorem UInt8.mul_zero {a : UInt8} : a * 0 = 0 := UInt8.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem UInt16.mul_zero {a : UInt16} : a * 0 = 0 := UInt16.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem UInt32.mul_zero {a : UInt32} : a * 0 = 0 := UInt32.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem UInt64.mul_zero {a : UInt64} : a * 0 = 0 := UInt64.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem USize.mul_zero {a : USize} : a * 0 = 0 := USize.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem UInt8.zero_mul {a : UInt8} : 0 * a = 0 := UInt8.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem UInt16.zero_mul {a : UInt16} : 0 * a = 0 := UInt16.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem UInt32.zero_mul {a : UInt32} : 0 * a = 0 := UInt32.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem UInt64.zero_mul {a : UInt64} : 0 * a = 0 := UInt64.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem USize.zero_mul {a : USize} : 0 * a = 0 := USize.toBitVec_inj.1 BitVec.zero_mul

protected theorem UInt8.mul_add {a b c : UInt8} : a * (b + c) = a * b + a * c :=
    UInt8.toBitVec_inj.1 BitVec.mul_add
protected theorem UInt16.mul_add {a b c : UInt16} : a * (b + c) = a * b + a * c :=
    UInt16.toBitVec_inj.1 BitVec.mul_add
protected theorem UInt32.mul_add {a b c : UInt32} : a * (b + c) = a * b + a * c :=
    UInt32.toBitVec_inj.1 BitVec.mul_add
protected theorem UInt64.mul_add {a b c : UInt64} : a * (b + c) = a * b + a * c :=
    UInt64.toBitVec_inj.1 BitVec.mul_add
protected theorem USize.mul_add {a b c : USize} : a * (b + c) = a * b + a * c :=
    USize.toBitVec_inj.1 BitVec.mul_add

protected theorem UInt8.add_mul {a b c : UInt8} : (a + b) * c = a * c + b * c := by
  rw [UInt8.mul_comm, UInt8.mul_add, UInt8.mul_comm a c, UInt8.mul_comm c b]
protected theorem UInt16.add_mul {a b c : UInt16} : (a + b) * c = a * c + b * c := by
  rw [UInt16.mul_comm, UInt16.mul_add, UInt16.mul_comm a c, UInt16.mul_comm c b]
protected theorem UInt32.add_mul {a b c : UInt32} : (a + b) * c = a * c + b * c := by
  rw [UInt32.mul_comm, UInt32.mul_add, UInt32.mul_comm a c, UInt32.mul_comm c b]
protected theorem UInt64.add_mul {a b c : UInt64} : (a + b) * c = a * c + b * c := by
  rw [UInt64.mul_comm, UInt64.mul_add, UInt64.mul_comm a c, UInt64.mul_comm c b]
protected theorem USize.add_mul {a b c : USize} : (a + b) * c = a * c + b * c := by
  rw [USize.mul_comm, USize.mul_add, USize.mul_comm a c, USize.mul_comm c b]

protected theorem UInt8.mul_succ {a b : UInt8} : a * (b + 1) = a * b + a := by simp [UInt8.mul_add]
protected theorem UInt16.mul_succ {a b : UInt16} : a * (b + 1) = a * b + a := by simp [UInt16.mul_add]
protected theorem UInt32.mul_succ {a b : UInt32} : a * (b + 1) = a * b + a := by simp [UInt32.mul_add]
protected theorem UInt64.mul_succ {a b : UInt64} : a * (b + 1) = a * b + a := by simp [UInt64.mul_add]
protected theorem USize.mul_succ {a b : USize} : a * (b + 1) = a * b + a := by simp [USize.mul_add]

protected theorem UInt8.succ_mul {a b : UInt8} : (a + 1) * b = a * b + b := by simp [UInt8.add_mul]
protected theorem UInt16.succ_mul {a b : UInt16} : (a + 1) * b = a * b + b := by simp [UInt16.add_mul]
protected theorem UInt32.succ_mul {a b : UInt32} : (a + 1) * b = a * b + b := by simp [UInt32.add_mul]
protected theorem UInt64.succ_mul {a b : UInt64} : (a + 1) * b = a * b + b := by simp [UInt64.add_mul]
protected theorem USize.succ_mul {a b : USize} : (a + 1) * b = a * b + b := by simp [USize.add_mul]

protected theorem UInt8.two_mul {a : UInt8} : 2 * a = a + a := UInt8.toBitVec_inj.1 BitVec.two_mul
protected theorem UInt16.two_mul {a : UInt16} : 2 * a = a + a := UInt16.toBitVec_inj.1 BitVec.two_mul
protected theorem UInt32.two_mul {a : UInt32} : 2 * a = a + a := UInt32.toBitVec_inj.1 BitVec.two_mul
protected theorem UInt64.two_mul {a : UInt64} : 2 * a = a + a := UInt64.toBitVec_inj.1 BitVec.two_mul
protected theorem USize.two_mul {a : USize} : 2 * a = a + a := USize.toBitVec_inj.1 BitVec.two_mul

protected theorem UInt8.mul_two {a : UInt8} : a * 2 = a + a := UInt8.toBitVec_inj.1 BitVec.mul_two
protected theorem UInt16.mul_two {a : UInt16} : a * 2 = a + a := UInt16.toBitVec_inj.1 BitVec.mul_two
protected theorem UInt32.mul_two {a : UInt32} : a * 2 = a + a := UInt32.toBitVec_inj.1 BitVec.mul_two
protected theorem UInt64.mul_two {a : UInt64} : a * 2 = a + a := UInt64.toBitVec_inj.1 BitVec.mul_two
protected theorem USize.mul_two {a : USize} : a * 2 = a + a := USize.toBitVec_inj.1 BitVec.mul_two

protected theorem UInt8.neg_mul (a b : UInt8) : -a * b = -(a * b) := UInt8.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem UInt16.neg_mul (a b : UInt16) : -a * b = -(a * b) := UInt16.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem UInt32.neg_mul (a b : UInt32) : -a * b = -(a * b) := UInt32.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem UInt64.neg_mul (a b : UInt64) : -a * b = -(a * b) := UInt64.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem USize.neg_mul (a b : USize) : -a * b = -(a * b) := USize.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem UInt8.mul_neg (a b : UInt8) : a * -b = -(a * b) := UInt8.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem UInt16.mul_neg (a b : UInt16) : a * -b = -(a * b) := UInt16.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem UInt32.mul_neg (a b : UInt32) : a * -b = -(a * b) := UInt32.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem UInt64.mul_neg (a b : UInt64) : a * -b = -(a * b) := UInt64.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem USize.mul_neg (a b : USize) : a * -b = -(a * b) := USize.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem UInt8.neg_mul_neg (a b : UInt8) : -a * -b = a * b := UInt8.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem UInt16.neg_mul_neg (a b : UInt16) : -a * -b = a * b := UInt16.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem UInt32.neg_mul_neg (a b : UInt32) : -a * -b = a * b := UInt32.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem UInt64.neg_mul_neg (a b : UInt64) : -a * -b = a * b := UInt64.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem USize.neg_mul_neg (a b : USize) : -a * -b = a * b := USize.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem UInt8.neg_mul_comm (a b : UInt8) : -a * b = a * -b := UInt8.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem UInt16.neg_mul_comm (a b : UInt16) : -a * b = a * -b := UInt16.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem UInt32.neg_mul_comm (a b : UInt32) : -a * b = a * -b := UInt32.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem UInt64.neg_mul_comm (a b : UInt64) : -a * b = a * -b := UInt64.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem USize.neg_mul_comm (a b : USize) : -a * b = a * -b := USize.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem UInt8.mul_sub {a b c : UInt8} : a * (b - c) = a * b - a * c := UInt8.toBitVec_inj.1 BitVec.mul_sub
protected theorem UInt16.mul_sub {a b c : UInt16} : a * (b - c) = a * b - a * c := UInt16.toBitVec_inj.1 BitVec.mul_sub
protected theorem UInt32.mul_sub {a b c : UInt32} : a * (b - c) = a * b - a * c := UInt32.toBitVec_inj.1 BitVec.mul_sub
protected theorem UInt64.mul_sub {a b c : UInt64} : a * (b - c) = a * b - a * c := UInt64.toBitVec_inj.1 BitVec.mul_sub
protected theorem USize.mul_sub {a b c : USize} : a * (b - c) = a * b - a * c := USize.toBitVec_inj.1 BitVec.mul_sub

protected theorem UInt8.sub_mul {a b c : UInt8} : (a - b) * c = a * c - b * c := by
  rw [UInt8.mul_comm, UInt8.mul_sub, UInt8.mul_comm, UInt8.mul_comm c]
protected theorem UInt16.sub_mul {a b c : UInt16} : (a - b) * c = a * c - b * c := by
  rw [UInt16.mul_comm, UInt16.mul_sub, UInt16.mul_comm, UInt16.mul_comm c]
protected theorem UInt32.sub_mul {a b c : UInt32} : (a - b) * c = a * c - b * c := by
  rw [UInt32.mul_comm, UInt32.mul_sub, UInt32.mul_comm, UInt32.mul_comm c]
protected theorem UInt64.sub_mul {a b c : UInt64} : (a - b) * c = a * c - b * c := by
  rw [UInt64.mul_comm, UInt64.mul_sub, UInt64.mul_comm, UInt64.mul_comm c]
protected theorem USize.sub_mul {a b c : USize} : (a - b) * c = a * c - b * c := by
  rw [USize.mul_comm, USize.mul_sub, USize.mul_comm, USize.mul_comm c]

theorem UInt8.neg_add_mul_eq_mul_not {a b : UInt8} : -(a + a * b) = a * ~~~b :=
  UInt8.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem UInt16.neg_add_mul_eq_mul_not {a b : UInt16} : -(a + a * b) = a * ~~~b :=
  UInt16.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem UInt32.neg_add_mul_eq_mul_not {a b : UInt32} : -(a + a * b) = a * ~~~b :=
  UInt32.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem UInt64.neg_add_mul_eq_mul_not {a b : UInt64} : -(a + a * b) = a * ~~~b :=
  UInt64.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem USize.neg_add_mul_eq_mul_not {a b : USize} : -(a + a * b) = a * ~~~b :=
  USize.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem UInt8.neg_mul_not_eq_add_mul {a b : UInt8} : -(a * ~~~b) = a + a * b :=
  UInt8.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem UInt16.neg_mul_not_eq_add_mul {a b : UInt16} : -(a * ~~~b) = a + a * b :=
  UInt16.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem UInt32.neg_mul_not_eq_add_mul {a b : UInt32} : -(a * ~~~b) = a + a * b :=
  UInt32.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem UInt64.neg_mul_not_eq_add_mul {a b : UInt64} : -(a * ~~~b) = a + a * b :=
  UInt64.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem USize.neg_mul_not_eq_add_mul {a b : USize} : -(a * ~~~b) = a + a * b :=
  USize.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem UInt8.le_of_lt {a b : UInt8} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt
protected theorem UInt16.le_of_lt {a b : UInt16} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt
protected theorem UInt32.le_of_lt {a b : UInt32} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt
protected theorem UInt64.le_of_lt {a b : UInt64} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt
protected theorem USize.le_of_lt {a b : USize} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt

protected theorem UInt8.lt_of_le_of_ne {a b : UInt8} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt8.toNat_inj] using Nat.lt_of_le_of_ne
protected theorem UInt16.lt_of_le_of_ne {a b : UInt16} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt16.toNat_inj] using Nat.lt_of_le_of_ne
protected theorem UInt32.lt_of_le_of_ne {a b : UInt32} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt32.toNat_inj] using Nat.lt_of_le_of_ne
protected theorem UInt64.lt_of_le_of_ne {a b : UInt64} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt64.toNat_inj] using Nat.lt_of_le_of_ne
protected theorem USize.lt_of_le_of_ne {a b : USize} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize.toNat_inj] using Nat.lt_of_le_of_ne

protected theorem UInt8.lt_iff_le_and_ne {a b : UInt8} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt8.toNat_inj] using Nat.lt_iff_le_and_ne
protected theorem UInt16.lt_iff_le_and_ne {a b : UInt16} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt16.toNat_inj] using Nat.lt_iff_le_and_ne
protected theorem UInt32.lt_iff_le_and_ne {a b : UInt32} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt32.toNat_inj] using Nat.lt_iff_le_and_ne
protected theorem UInt64.lt_iff_le_and_ne {a b : UInt64} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt64.toNat_inj] using Nat.lt_iff_le_and_ne
protected theorem USize.lt_iff_le_and_ne {a b : USize} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize.toNat_inj] using Nat.lt_iff_le_and_ne

@[simp] protected theorem UInt8.not_lt_zero {a : UInt8} : ¬a < 0 := by simp [UInt8.lt_iff_toBitVec_lt]
@[simp] protected theorem UInt16.not_lt_zero {a : UInt16} : ¬a < 0 := by simp [UInt16.lt_iff_toBitVec_lt]
@[simp] protected theorem UInt32.not_lt_zero {a : UInt32} : ¬a < 0 := by simp [UInt32.lt_iff_toBitVec_lt]
@[simp] protected theorem UInt64.not_lt_zero {a : UInt64} : ¬a < 0 := by simp [UInt64.lt_iff_toBitVec_lt]
@[simp] protected theorem USize.not_lt_zero {a : USize} : ¬a < 0 := by simp [USize.lt_iff_toBitVec_lt]

@[simp] protected theorem UInt8.zero_le {a : UInt8} : 0 ≤ a := by simp [← UInt8.not_lt]
@[simp] protected theorem UInt16.zero_le {a : UInt16} : 0 ≤ a := by simp [← UInt16.not_lt]
@[simp] protected theorem UInt32.zero_le {a : UInt32} : 0 ≤ a := by simp [← UInt32.not_lt]
@[simp] protected theorem UInt64.zero_le {a : UInt64} : 0 ≤ a := by simp [← UInt64.not_lt]
@[simp] protected theorem USize.zero_le {a : USize} : 0 ≤ a := by simp [← USize.not_lt]

@[simp] protected theorem UInt8.le_zero_iff {a : UInt8} : a ≤ 0 ↔ a = 0 := by
  simp [UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.le_zero_iff {a : UInt16} : a ≤ 0 ↔ a = 0 := by
  simp [UInt16.le_iff_toBitVec_le, ← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.le_zero_iff {a : UInt32} : a ≤ 0 ↔ a = 0 := by
  simp [UInt32.le_iff_toBitVec_le, ← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.le_zero_iff {a : UInt64} : a ≤ 0 ↔ a = 0 := by
  simp [UInt64.le_iff_toBitVec_le, ← UInt64.toBitVec_inj]
@[simp] protected theorem USize.le_zero_iff {a : USize} : a ≤ 0 ↔ a = 0 := by
  simp [USize.le_iff_toBitVec_le, ← USize.toBitVec_inj]

@[simp] protected theorem UInt8.lt_one_iff {a : UInt8} : a < 1 ↔ a = 0 := by
  simp [UInt8.lt_iff_toBitVec_lt, ← UInt8.toBitVec_inj]
@[simp] protected theorem UInt16.lt_one_iff {a : UInt16} : a < 1 ↔ a = 0 := by
  simp [UInt16.lt_iff_toBitVec_lt, ← UInt16.toBitVec_inj]
@[simp] protected theorem UInt32.lt_one_iff {a : UInt32} : a < 1 ↔ a = 0 := by
  simp [UInt32.lt_iff_toBitVec_lt, ← UInt32.toBitVec_inj]
@[simp] protected theorem UInt64.lt_one_iff {a : UInt64} : a < 1 ↔ a = 0 := by
  simp [UInt64.lt_iff_toBitVec_lt, ← UInt64.toBitVec_inj]
@[simp] protected theorem USize.lt_one_iff {a : USize} : a < 1 ↔ a = 0 := by
  simp [USize.lt_iff_toBitVec_lt, ← USize.toBitVec_inj]

@[simp] protected theorem UInt8.zero_div {a : UInt8} : 0 / a = 0 := UInt8.toBitVec_inj.1 BitVec.zero_udiv
@[simp] protected theorem UInt16.zero_div {a : UInt16} : 0 / a = 0 := UInt16.toBitVec_inj.1 BitVec.zero_udiv
@[simp] protected theorem UInt32.zero_div {a : UInt32} : 0 / a = 0 := UInt32.toBitVec_inj.1 BitVec.zero_udiv
@[simp] protected theorem UInt64.zero_div {a : UInt64} : 0 / a = 0 := UInt64.toBitVec_inj.1 BitVec.zero_udiv
@[simp] protected theorem USize.zero_div {a : USize} : 0 / a = 0 := USize.toBitVec_inj.1 BitVec.zero_udiv

@[simp] protected theorem UInt8.div_zero {a : UInt8} : a / 0 = 0 := UInt8.toBitVec_inj.1 BitVec.udiv_zero
@[simp] protected theorem UInt16.div_zero {a : UInt16} : a / 0 = 0 := UInt16.toBitVec_inj.1 BitVec.udiv_zero
@[simp] protected theorem UInt32.div_zero {a : UInt32} : a / 0 = 0 := UInt32.toBitVec_inj.1 BitVec.udiv_zero
@[simp] protected theorem UInt64.div_zero {a : UInt64} : a / 0 = 0 := UInt64.toBitVec_inj.1 BitVec.udiv_zero
@[simp] protected theorem USize.div_zero {a : USize} : a / 0 = 0 := USize.toBitVec_inj.1 BitVec.udiv_zero

@[simp] protected theorem UInt8.div_one {a : UInt8} : a / 1 = a := UInt8.toBitVec_inj.1 BitVec.udiv_one
@[simp] protected theorem UInt16.div_one {a : UInt16} : a / 1 = a := UInt16.toBitVec_inj.1 BitVec.udiv_one
@[simp] protected theorem UInt32.div_one {a : UInt32} : a / 1 = a := UInt32.toBitVec_inj.1 BitVec.udiv_one
@[simp] protected theorem UInt64.div_one {a : UInt64} : a / 1 = a := UInt64.toBitVec_inj.1 BitVec.udiv_one
@[simp] protected theorem USize.div_one {a : USize} : a / 1 = a := USize.toBitVec_inj.1 BitVec.udiv_one

protected theorem UInt8.div_self {a : UInt8} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt8.toBitVec_inj, apply_ite]
protected theorem UInt16.div_self {a : UInt16} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt16.toBitVec_inj, apply_ite]
protected theorem UInt32.div_self {a : UInt32} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt32.toBitVec_inj, apply_ite]
protected theorem UInt64.div_self {a : UInt64} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt64.toBitVec_inj, apply_ite]
protected theorem USize.div_self {a : USize} : a / a = if a = 0 then 0 else 1 := by
  simp [← USize.toNat_inj]
  split
  · simp_all
  · simpa using Nat.div_self (by omega)

@[simp] protected theorem UInt8.mod_zero {a : UInt8} : a % 0 = a := UInt8.toBitVec_inj.1 BitVec.umod_zero
@[simp] protected theorem UInt16.mod_zero {a : UInt16} : a % 0 = a := UInt16.toBitVec_inj.1 BitVec.umod_zero
@[simp] protected theorem UInt32.mod_zero {a : UInt32} : a % 0 = a := UInt32.toBitVec_inj.1 BitVec.umod_zero
@[simp] protected theorem UInt64.mod_zero {a : UInt64} : a % 0 = a := UInt64.toBitVec_inj.1 BitVec.umod_zero
@[simp] protected theorem USize.mod_zero {a : USize} : a % 0 = a := USize.toBitVec_inj.1 BitVec.umod_zero

@[simp] protected theorem UInt8.zero_mod {a : UInt8} : 0 % a = 0 := UInt8.toBitVec_inj.1 BitVec.zero_umod
@[simp] protected theorem UInt16.zero_mod {a : UInt16} : 0 % a = 0 := UInt16.toBitVec_inj.1 BitVec.zero_umod
@[simp] protected theorem UInt32.zero_mod {a : UInt32} : 0 % a = 0 := UInt32.toBitVec_inj.1 BitVec.zero_umod
@[simp] protected theorem UInt64.zero_mod {a : UInt64} : 0 % a = 0 := UInt64.toBitVec_inj.1 BitVec.zero_umod
@[simp] protected theorem USize.zero_mod {a : USize} : 0 % a = 0 := USize.toBitVec_inj.1 BitVec.zero_umod

@[simp] protected theorem UInt8.mod_one {a : UInt8} : a % 1 = 0 := UInt8.toBitVec_inj.1 BitVec.umod_one
@[simp] protected theorem UInt16.mod_one {a : UInt16} : a % 1 = 0 := UInt16.toBitVec_inj.1 BitVec.umod_one
@[simp] protected theorem UInt32.mod_one {a : UInt32} : a % 1 = 0 := UInt32.toBitVec_inj.1 BitVec.umod_one
@[simp] protected theorem UInt64.mod_one {a : UInt64} : a % 1 = 0 := UInt64.toBitVec_inj.1 BitVec.umod_one
@[simp] protected theorem USize.mod_one {a : USize} : a % 1 = 0 := USize.toBitVec_inj.1 BitVec.umod_one

@[simp] protected theorem UInt8.mod_self {a : UInt8} : a % a = 0 := UInt8.toBitVec_inj.1 BitVec.umod_self
@[simp] protected theorem UInt16.mod_self {a : UInt16} : a % a = 0 := UInt16.toBitVec_inj.1 BitVec.umod_self
@[simp] protected theorem UInt32.mod_self {a : UInt32} : a % a = 0 := UInt32.toBitVec_inj.1 BitVec.umod_self
@[simp] protected theorem UInt64.mod_self {a : UInt64} : a % a = 0 := UInt64.toBitVec_inj.1 BitVec.umod_self
@[simp] protected theorem USize.mod_self {a : USize} : a % a = 0 := USize.toBitVec_inj.1 BitVec.umod_self

protected theorem UInt8.pos_iff_ne_zero {a : UInt8} : 0 < a ↔ a ≠ 0 := by simp [UInt8.lt_iff_le_and_ne, Eq.comm]
protected theorem UInt16.pos_iff_ne_zero {a : UInt16} : 0 < a ↔ a ≠ 0 := by simp [UInt16.lt_iff_le_and_ne, Eq.comm]
protected theorem UInt32.pos_iff_ne_zero {a : UInt32} : 0 < a ↔ a ≠ 0 := by simp [UInt32.lt_iff_le_and_ne, Eq.comm]
protected theorem UInt64.pos_iff_ne_zero {a : UInt64} : 0 < a ↔ a ≠ 0 := by simp [UInt64.lt_iff_le_and_ne, Eq.comm]
protected theorem USize.pos_iff_ne_zero {a : USize} : 0 < a ↔ a ≠ 0 := by simp [USize.lt_iff_le_and_ne, Eq.comm]

protected theorem UInt8.lt_of_le_of_lt {a b c : UInt8} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt
protected theorem UInt16.lt_of_le_of_lt {a b c : UInt16} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt
protected theorem UInt32.lt_of_le_of_lt {a b c : UInt32} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt
protected theorem UInt64.lt_of_le_of_lt {a b c : UInt64} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt
protected theorem USize.lt_of_le_of_lt {a b c : USize} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt

protected theorem UInt8.lt_of_lt_of_le {a b c : UInt8} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le
protected theorem UInt16.lt_of_lt_of_le {a b c : UInt16} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le
protected theorem UInt32.lt_of_lt_of_le {a b c : UInt32} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le
protected theorem UInt64.lt_of_lt_of_le {a b c : UInt64} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le
protected theorem USize.lt_of_lt_of_le {a b c : USize} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le

protected theorem UInt8.lt_or_lt_of_ne {a b : UInt8} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt8.toNat_inj] using Nat.lt_or_lt_of_ne
protected theorem UInt16.lt_or_lt_of_ne {a b : UInt16} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt16.toNat_inj] using Nat.lt_or_lt_of_ne
protected theorem UInt32.lt_or_lt_of_ne {a b : UInt32} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt32.toNat_inj] using Nat.lt_or_lt_of_ne
protected theorem UInt64.lt_or_lt_of_ne {a b : UInt64} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt64.toNat_inj] using Nat.lt_or_lt_of_ne
protected theorem USize.lt_or_lt_of_ne {a b : USize} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← USize.toNat_inj] using Nat.lt_or_lt_of_ne

protected theorem UInt8.lt_or_le (a b : UInt8) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega
protected theorem UInt16.lt_or_le (a b : UInt16) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega
protected theorem UInt32.lt_or_le (a b : UInt32) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega
protected theorem UInt64.lt_or_le (a b : UInt64) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega
protected theorem USize.lt_or_le (a b : USize) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega

protected theorem UInt8.le_or_lt (a b : UInt8) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem UInt16.le_or_lt (a b : UInt16) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem UInt32.le_or_lt (a b : UInt32) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem UInt64.le_or_lt (a b : UInt64) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem USize.le_or_lt (a b : USize) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem UInt8.le_of_eq {a b : UInt8} : a = b → a ≤ b := (· ▸ UInt8.le_rfl)
protected theorem UInt16.le_of_eq {a b : UInt16} : a = b → a ≤ b := (· ▸ UInt16.le_rfl)
protected theorem UInt32.le_of_eq {a b : UInt32} : a = b → a ≤ b := (· ▸ UInt32.le_rfl)
protected theorem UInt64.le_of_eq {a b : UInt64} : a = b → a ≤ b := (· ▸ UInt64.le_rfl)
protected theorem USize.le_of_eq {a b : USize} : a = b → a ≤ b := (· ▸ USize.le_rfl)

protected theorem UInt8.le_iff_lt_or_eq {a b : UInt8} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt8.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq
protected theorem UInt16.le_iff_lt_or_eq {a b : UInt16} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt16.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq
protected theorem UInt32.le_iff_lt_or_eq {a b : UInt32} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt32.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq
protected theorem UInt64.le_iff_lt_or_eq {a b : UInt64} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt64.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq
protected theorem USize.le_iff_lt_or_eq {a b : USize} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← USize.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq

protected theorem UInt8.lt_or_eq_of_le {a b : UInt8} : a ≤ b → a < b ∨ a = b := UInt8.le_iff_lt_or_eq.mp
protected theorem UInt16.lt_or_eq_of_le {a b : UInt16} : a ≤ b → a < b ∨ a = b := UInt16.le_iff_lt_or_eq.mp
protected theorem UInt32.lt_or_eq_of_le {a b : UInt32} : a ≤ b → a < b ∨ a = b := UInt32.le_iff_lt_or_eq.mp
protected theorem UInt64.lt_or_eq_of_le {a b : UInt64} : a ≤ b → a < b ∨ a = b := UInt64.le_iff_lt_or_eq.mp
protected theorem USize.lt_or_eq_of_le {a b : USize} : a ≤ b → a < b ∨ a = b := USize.le_iff_lt_or_eq.mp

protected theorem UInt8.sub_le {a b : UInt8} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt8.toNat_sub_of_le _ _ hab]
protected theorem UInt16.sub_le {a b : UInt16} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt16.toNat_sub_of_le _ _ hab]
protected theorem UInt32.sub_le {a b : UInt32} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ hab]
protected theorem UInt64.sub_le {a b : UInt64} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hab]
protected theorem USize.sub_le {a b : USize} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, USize.toNat_sub_of_le _ _ hab]

protected theorem UInt8.sub_lt {a b : UInt8} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt8.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt8.lt_iff_toNat_lt.1 hb)
  exact UInt8.lt_iff_toNat_lt.1 (UInt8.lt_of_lt_of_le hb hab)
protected theorem UInt16.sub_lt {a b : UInt16} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt16.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt16.lt_iff_toNat_lt.1 hb)
  exact UInt16.lt_iff_toNat_lt.1 (UInt16.lt_of_lt_of_le hb hab)
protected theorem UInt32.sub_lt {a b : UInt32} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt32.lt_iff_toNat_lt.1 hb)
  exact UInt32.lt_iff_toNat_lt.1 (UInt32.lt_of_lt_of_le hb hab)
protected theorem UInt64.sub_lt {a b : UInt64} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt64.lt_iff_toNat_lt.1 hb)
  exact UInt64.lt_iff_toNat_lt.1 (UInt64.lt_of_lt_of_le hb hab)
protected theorem USize.sub_lt {a b : USize} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (USize.lt_iff_toNat_lt.1 hb)
  exact USize.lt_iff_toNat_lt.1 (USize.lt_of_lt_of_le hb hab)
