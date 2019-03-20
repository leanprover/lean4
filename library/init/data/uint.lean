/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic init.platform

open nat

def uint8Sz : nat := 256
structure uint8 :=
(val : fin uint8Sz)

@[extern cpp "lean::uint8_of_nat"]
def uint8.ofNat (n : @& nat) : uint8 := ⟨fin.ofNat n⟩
@[extern cpp "lean::uint8_to_nat"]
def uint8.toNat (n : uint8) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def uint8.add (a b : uint8) : uint8 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def uint8.sub (a b : uint8) : uint8 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def uint8.mul (a b : uint8) : uint8 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def uint8.div (a b : uint8) : uint8 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def uint8.mod (a b : uint8) : uint8 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint8_modn"]
def uint8.modn (a : uint8) (n : @& nat) : uint8 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def uint8.land (a b : uint8) : uint8 := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def uint8.lor (a b : uint8) : uint8 := ⟨fin.lor a.val b.val⟩
def uint8.lt (a b : uint8) : Prop := a.val < b.val
def uint8.le (a b : uint8) : Prop := a.val ≤ b.val

instance : hasZero uint8     := ⟨uint8.ofNat 0⟩
instance : hasOne uint8      := ⟨uint8.ofNat 1⟩
instance : hasAdd uint8      := ⟨uint8.add⟩
instance : hasSub uint8      := ⟨uint8.sub⟩
instance : hasMul uint8      := ⟨uint8.mul⟩
instance : hasMod uint8      := ⟨uint8.mod⟩
instance : hasModn uint8     := ⟨uint8.modn⟩
instance : hasDiv uint8      := ⟨uint8.div⟩
instance : hasLt uint8       := ⟨uint8.lt⟩
instance : hasLe uint8       := ⟨uint8.le⟩
instance : inhabited uint8    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint8.decEq (a b : uint8) : decidable (a = b) :=
uint8.casesOn a $ λ n, uint8.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', uint8.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint8.decLt (a b : uint8) : decidable (a < b) :=
uint8.casesOn a $ λ n, uint8.casesOn b $ λ m,
  inferInstanceAs (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint8.decLe (a b : uint8) : decidable (a ≤ b) :=
uint8.casesOn a $ λ n, uint8.casesOn b $ λ m,
  inferInstanceAs (decidable (n <= m))

instance : decidableEq uint8 := {decEq := uint8.decEq}
instance uint8.hasDecidableLt (a b : uint8) : decidable (a < b) := uint8.decLt a b
instance uint8.hasDecidableLe (a b : uint8) : decidable (a ≤ b) := uint8.decLe a b

def uint16Sz : nat := 65536
structure uint16 :=
(val : fin uint16Sz)

@[extern cpp "lean::uint16_of_nat"]
def uint16.ofNat (n : @& nat) : uint16 := ⟨fin.ofNat n⟩
@[extern cpp "lean::uint16_to_nat"]
def uint16.toNat (n : uint16) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def uint16.add (a b : uint16) : uint16 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def uint16.sub (a b : uint16) : uint16 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def uint16.mul (a b : uint16) : uint16 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def uint16.div (a b : uint16) : uint16 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def uint16.mod (a b : uint16) : uint16 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint16_modn"]
def uint16.modn (a : uint16) (n : @& nat) : uint16 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def uint16.land (a b : uint16) : uint16 := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def uint16.lor (a b : uint16) : uint16 := ⟨fin.lor a.val b.val⟩
def uint16.lt (a b : uint16) : Prop := a.val < b.val
def uint16.le (a b : uint16) : Prop := a.val ≤ b.val

instance : hasZero uint16     := ⟨uint16.ofNat 0⟩
instance : hasOne uint16      := ⟨uint16.ofNat 1⟩
instance : hasAdd uint16      := ⟨uint16.add⟩
instance : hasSub uint16      := ⟨uint16.sub⟩
instance : hasMul uint16      := ⟨uint16.mul⟩
instance : hasMod uint16      := ⟨uint16.mod⟩
instance : hasModn uint16     := ⟨uint16.modn⟩
instance : hasDiv uint16      := ⟨uint16.div⟩
instance : hasLt uint16       := ⟨uint16.lt⟩
instance : hasLe uint16       := ⟨uint16.le⟩
instance : inhabited uint16    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint16.decEq (a b : uint16) : decidable (a = b) :=
uint16.casesOn a $ λ n, uint16.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', uint16.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint16.decLt (a b : uint16) : decidable (a < b) :=
uint16.casesOn a $ λ n, uint16.casesOn b $ λ m,
  inferInstanceAs (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint16.decLe (a b : uint16) : decidable (a ≤ b) :=
uint16.casesOn a $ λ n, uint16.casesOn b $ λ m,
  inferInstanceAs (decidable (n <= m))

instance : decidableEq uint16 := {decEq := uint16.decEq}
instance uint16.hasDecidableLt (a b : uint16) : decidable (a < b) := uint16.decLt a b
instance uint16.hasDecidableLe (a b : uint16) : decidable (a ≤ b) := uint16.decLe a b

def uint32Sz : nat := 4294967296
structure uint32 :=
(val : fin uint32Sz)

@[extern cpp "lean::uint32_of_nat"]
def uint32.ofNat (n : @& nat) : uint32 := ⟨fin.ofNat n⟩
@[extern cpp "lean::uint32_to_nat"]
def uint32.toNat (n : uint32) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def uint32.add (a b : uint32) : uint32 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def uint32.sub (a b : uint32) : uint32 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def uint32.mul (a b : uint32) : uint32 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def uint32.div (a b : uint32) : uint32 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def uint32.mod (a b : uint32) : uint32 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint32_modn"]
def uint32.modn (a : uint32) (n : @& nat) : uint32 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def uint32.land (a b : uint32) : uint32 := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def uint32.lor (a b : uint32) : uint32 := ⟨fin.lor a.val b.val⟩
def uint32.lt (a b : uint32) : Prop := a.val < b.val
def uint32.le (a b : uint32) : Prop := a.val ≤ b.val

instance : hasZero uint32     := ⟨uint32.ofNat 0⟩
instance : hasOne uint32      := ⟨uint32.ofNat 1⟩
instance : hasAdd uint32      := ⟨uint32.add⟩
instance : hasSub uint32      := ⟨uint32.sub⟩
instance : hasMul uint32      := ⟨uint32.mul⟩
instance : hasMod uint32      := ⟨uint32.mod⟩
instance : hasModn uint32     := ⟨uint32.modn⟩
instance : hasDiv uint32      := ⟨uint32.div⟩
instance : hasLt uint32       := ⟨uint32.lt⟩
instance : hasLe uint32       := ⟨uint32.le⟩
instance : inhabited uint32    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint32.decEq (a b : uint32) : decidable (a = b) :=
uint32.casesOn a $ λ n, uint32.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', uint32.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint32.decLt (a b : uint32) : decidable (a < b) :=
uint32.casesOn a $ λ n, uint32.casesOn b $ λ m,
  inferInstanceAs (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint32.decLe (a b : uint32) : decidable (a ≤ b) :=
uint32.casesOn a $ λ n, uint32.casesOn b $ λ m,
  inferInstanceAs (decidable (n <= m))

instance : decidableEq uint32 := {decEq := uint32.decEq}
instance uint32.hasDecidableLt (a b : uint32) : decidable (a < b) := uint32.decLt a b
instance uint32.hasDecidableLe (a b : uint32) : decidable (a ≤ b) := uint32.decLe a b

def uint64Sz : nat := 18446744073709551616
structure uint64 :=
(val : fin uint64Sz)

@[extern cpp "lean::uint64_of_nat"]
def uint64.ofNat (n : @& nat) : uint64 := ⟨fin.ofNat n⟩
@[extern cpp "lean::uint64_to_nat"]
def uint64.toNat (n : uint64) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def uint64.add (a b : uint64) : uint64 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def uint64.sub (a b : uint64) : uint64 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def uint64.mul (a b : uint64) : uint64 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def uint64.div (a b : uint64) : uint64 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def uint64.mod (a b : uint64) : uint64 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint64_modn"]
def uint64.modn (a : uint64) (n : @& nat) : uint64 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def uint64.land (a b : uint64) : uint64 := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def uint64.lor (a b : uint64) : uint64 := ⟨fin.lor a.val b.val⟩
def uint64.lt (a b : uint64) : Prop := a.val < b.val
def uint64.le (a b : uint64) : Prop := a.val ≤ b.val

instance : hasZero uint64     := ⟨uint64.ofNat 0⟩
instance : hasOne uint64      := ⟨uint64.ofNat 1⟩
instance : hasAdd uint64      := ⟨uint64.add⟩
instance : hasSub uint64      := ⟨uint64.sub⟩
instance : hasMul uint64      := ⟨uint64.mul⟩
instance : hasMod uint64      := ⟨uint64.mod⟩
instance : hasModn uint64     := ⟨uint64.modn⟩
instance : hasDiv uint64      := ⟨uint64.div⟩
instance : hasLt uint64       := ⟨uint64.lt⟩
instance : hasLe uint64       := ⟨uint64.le⟩
instance : inhabited uint64    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint64.decEq (a b : uint64) : decidable (a = b) :=
uint64.casesOn a $ λ n, uint64.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', uint64.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint64.decLt (a b : uint64) : decidable (a < b) :=
uint64.casesOn a $ λ n, uint64.casesOn b $ λ m,
  inferInstanceAs (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint64.decLe (a b : uint64) : decidable (a ≤ b) :=
uint64.casesOn a $ λ n, uint64.casesOn b $ λ m,
  inferInstanceAs (decidable (n <= m))

instance : decidableEq uint64 := {decEq := uint64.decEq}
instance uint64.hasDecidableLt (a b : uint64) : decidable (a < b) := uint64.decLt a b
instance uint64.hasDecidableLe (a b : uint64) : decidable (a ≤ b) := uint64.decLe a b

def usizeSz : nat := (2:nat) ^ system.platform.nbits
structure usize :=
(val : fin usizeSz)

@[extern cpp "lean::usize_of_nat"]
def usize.ofNat (n : @& nat) : usize := ⟨fin.ofNat n⟩
@[extern cpp "lean::usize_to_nat"]
def usize.toNat (n : usize) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def usize.add (a b : usize) : usize := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def usize.sub (a b : usize) : usize := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def usize.mul (a b : usize) : usize := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def usize.div (a b : usize) : usize := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def usize.mod (a b : usize) : usize := ⟨a.val % b.val⟩
@[extern cpp "lean::usize_modn"]
def usize.modn (a : usize) (n : @& nat) : usize := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def usize.land (a b : usize) : usize := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def usize.lor (a b : usize) : usize := ⟨fin.lor a.val b.val⟩
@[extern cpp inline "#1"]
def usize.ofUint32 (a : uint32) : usize := usize.ofNat (uint32.toNat a)
@[extern cpp inline "((lean::usize)#1)"]
def usize.ofUint64 (a : uint64) : usize := usize.ofNat (uint64.toNat a)
def usize.lt (a b : usize) : Prop := a.val < b.val
def usize.le (a b : usize) : Prop := a.val ≤ b.val

instance : hasZero usize     := ⟨usize.ofNat 0⟩
instance : hasOne usize      := ⟨usize.ofNat 1⟩
instance : hasAdd usize      := ⟨usize.add⟩
instance : hasSub usize      := ⟨usize.sub⟩
instance : hasMul usize      := ⟨usize.mul⟩
instance : hasMod usize      := ⟨usize.mod⟩
instance : hasModn usize     := ⟨usize.modn⟩
instance : hasDiv usize      := ⟨usize.div⟩
instance : hasLt usize       := ⟨usize.lt⟩
instance : hasLe usize       := ⟨usize.le⟩
instance : inhabited usize    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def usize.decEq (a b : usize) : decidable (a = b) :=
usize.casesOn a $ λ n, usize.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', usize.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def usize.decLt (a b : usize) : decidable (a < b) :=
usize.casesOn a $ λ n, usize.casesOn b $ λ m,
  inferInstanceAs (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def usize.decLe (a b : usize) : decidable (a ≤ b) :=
usize.casesOn a $ λ n, usize.casesOn b $ λ m,
  inferInstanceAs (decidable (n <= m))

instance : decidableEq usize := {decEq := usize.decEq}
instance usize.hasDecidableLt (a b : usize) : decidable (a < b) := usize.decLt a b
instance usize.hasDecidableLe (a b : usize) : decidable (a ≤ b) := usize.decLe a b

theorem usize.modnLt {m : nat} : ∀ (u : usize), m > 0 → usize.toNat (u %ₙ m) < m
| ⟨u⟩ h := fin.modnLt u h
