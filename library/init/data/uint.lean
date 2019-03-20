/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.Fin.basic init.platform

open Nat

def uint8Sz : Nat := 256
structure Uint8 :=
(val : Fin uint8Sz)

@[extern cpp "lean::uint8_of_nat"]
def Uint8.ofNat (n : @& Nat) : Uint8 := ⟨Fin.ofNat n⟩
@[extern cpp "lean::uint8_to_nat"]
def Uint8.toNat (n : Uint8) : Nat := n.val.val
@[extern cpp inline "#1 + #2"]
def Uint8.add (a b : Uint8) : Uint8 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def Uint8.sub (a b : Uint8) : Uint8 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def Uint8.mul (a b : Uint8) : Uint8 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def Uint8.div (a b : Uint8) : Uint8 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def Uint8.mod (a b : Uint8) : Uint8 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint8_modn"]
def Uint8.modn (a : Uint8) (n : @& Nat) : Uint8 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def Uint8.land (a b : Uint8) : Uint8 := ⟨Fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def Uint8.lor (a b : Uint8) : Uint8 := ⟨Fin.lor a.val b.val⟩
def Uint8.lt (a b : Uint8) : Prop := a.val < b.val
def Uint8.le (a b : Uint8) : Prop := a.val ≤ b.val

instance : HasZero Uint8     := ⟨Uint8.ofNat 0⟩
instance : HasOne Uint8      := ⟨Uint8.ofNat 1⟩
instance : HasAdd Uint8      := ⟨Uint8.add⟩
instance : HasSub Uint8      := ⟨Uint8.sub⟩
instance : HasMul Uint8      := ⟨Uint8.mul⟩
instance : HasMod Uint8      := ⟨Uint8.mod⟩
instance : HasModn Uint8     := ⟨Uint8.modn⟩
instance : HasDiv Uint8      := ⟨Uint8.div⟩
instance : HasLt Uint8       := ⟨Uint8.lt⟩
instance : HasLe Uint8       := ⟨Uint8.le⟩
instance : Inhabited Uint8    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def Uint8.decEq (a b : Uint8) : Decidable (a = b) :=
Uint8.casesOn a $ λ n, Uint8.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', Uint8.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def Uint8.decLt (a b : Uint8) : Decidable (a < b) :=
Uint8.casesOn a $ λ n, Uint8.casesOn b $ λ m,
  inferInstanceAs (Decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def Uint8.decLe (a b : Uint8) : Decidable (a ≤ b) :=
Uint8.casesOn a $ λ n, Uint8.casesOn b $ λ m,
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq Uint8 := {decEq := Uint8.decEq}
instance Uint8.hasDecidableLt (a b : Uint8) : Decidable (a < b) := Uint8.decLt a b
instance Uint8.hasDecidableLe (a b : Uint8) : Decidable (a ≤ b) := Uint8.decLe a b

def uint16Sz : Nat := 65536
structure Uint16 :=
(val : Fin uint16Sz)

@[extern cpp "lean::uint16_of_nat"]
def Uint16.ofNat (n : @& Nat) : Uint16 := ⟨Fin.ofNat n⟩
@[extern cpp "lean::uint16_to_nat"]
def Uint16.toNat (n : Uint16) : Nat := n.val.val
@[extern cpp inline "#1 + #2"]
def Uint16.add (a b : Uint16) : Uint16 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def Uint16.sub (a b : Uint16) : Uint16 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def Uint16.mul (a b : Uint16) : Uint16 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def Uint16.div (a b : Uint16) : Uint16 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def Uint16.mod (a b : Uint16) : Uint16 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint16_modn"]
def Uint16.modn (a : Uint16) (n : @& Nat) : Uint16 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def Uint16.land (a b : Uint16) : Uint16 := ⟨Fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def Uint16.lor (a b : Uint16) : Uint16 := ⟨Fin.lor a.val b.val⟩
def Uint16.lt (a b : Uint16) : Prop := a.val < b.val
def Uint16.le (a b : Uint16) : Prop := a.val ≤ b.val

instance : HasZero Uint16     := ⟨Uint16.ofNat 0⟩
instance : HasOne Uint16      := ⟨Uint16.ofNat 1⟩
instance : HasAdd Uint16      := ⟨Uint16.add⟩
instance : HasSub Uint16      := ⟨Uint16.sub⟩
instance : HasMul Uint16      := ⟨Uint16.mul⟩
instance : HasMod Uint16      := ⟨Uint16.mod⟩
instance : HasModn Uint16     := ⟨Uint16.modn⟩
instance : HasDiv Uint16      := ⟨Uint16.div⟩
instance : HasLt Uint16       := ⟨Uint16.lt⟩
instance : HasLe Uint16       := ⟨Uint16.le⟩
instance : Inhabited Uint16    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def Uint16.decEq (a b : Uint16) : Decidable (a = b) :=
Uint16.casesOn a $ λ n, Uint16.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', Uint16.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def Uint16.decLt (a b : Uint16) : Decidable (a < b) :=
Uint16.casesOn a $ λ n, Uint16.casesOn b $ λ m,
  inferInstanceAs (Decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def Uint16.decLe (a b : Uint16) : Decidable (a ≤ b) :=
Uint16.casesOn a $ λ n, Uint16.casesOn b $ λ m,
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq Uint16 := {decEq := Uint16.decEq}
instance Uint16.hasDecidableLt (a b : Uint16) : Decidable (a < b) := Uint16.decLt a b
instance Uint16.hasDecidableLe (a b : Uint16) : Decidable (a ≤ b) := Uint16.decLe a b

def uint32Sz : Nat := 4294967296
structure Uint32 :=
(val : Fin uint32Sz)

@[extern cpp "lean::uint32_of_nat"]
def Uint32.ofNat (n : @& Nat) : Uint32 := ⟨Fin.ofNat n⟩
@[extern cpp "lean::uint32_to_nat"]
def Uint32.toNat (n : Uint32) : Nat := n.val.val
@[extern cpp inline "#1 + #2"]
def Uint32.add (a b : Uint32) : Uint32 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def Uint32.sub (a b : Uint32) : Uint32 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def Uint32.mul (a b : Uint32) : Uint32 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def Uint32.div (a b : Uint32) : Uint32 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def Uint32.mod (a b : Uint32) : Uint32 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint32_modn"]
def Uint32.modn (a : Uint32) (n : @& Nat) : Uint32 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def Uint32.land (a b : Uint32) : Uint32 := ⟨Fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def Uint32.lor (a b : Uint32) : Uint32 := ⟨Fin.lor a.val b.val⟩
def Uint32.lt (a b : Uint32) : Prop := a.val < b.val
def Uint32.le (a b : Uint32) : Prop := a.val ≤ b.val

instance : HasZero Uint32     := ⟨Uint32.ofNat 0⟩
instance : HasOne Uint32      := ⟨Uint32.ofNat 1⟩
instance : HasAdd Uint32      := ⟨Uint32.add⟩
instance : HasSub Uint32      := ⟨Uint32.sub⟩
instance : HasMul Uint32      := ⟨Uint32.mul⟩
instance : HasMod Uint32      := ⟨Uint32.mod⟩
instance : HasModn Uint32     := ⟨Uint32.modn⟩
instance : HasDiv Uint32      := ⟨Uint32.div⟩
instance : HasLt Uint32       := ⟨Uint32.lt⟩
instance : HasLe Uint32       := ⟨Uint32.le⟩
instance : Inhabited Uint32    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def Uint32.decEq (a b : Uint32) : Decidable (a = b) :=
Uint32.casesOn a $ λ n, Uint32.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', Uint32.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def Uint32.decLt (a b : Uint32) : Decidable (a < b) :=
Uint32.casesOn a $ λ n, Uint32.casesOn b $ λ m,
  inferInstanceAs (Decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def Uint32.decLe (a b : Uint32) : Decidable (a ≤ b) :=
Uint32.casesOn a $ λ n, Uint32.casesOn b $ λ m,
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq Uint32 := {decEq := Uint32.decEq}
instance Uint32.hasDecidableLt (a b : Uint32) : Decidable (a < b) := Uint32.decLt a b
instance Uint32.hasDecidableLe (a b : Uint32) : Decidable (a ≤ b) := Uint32.decLe a b

def uint64Sz : Nat := 18446744073709551616
structure Uint64 :=
(val : Fin uint64Sz)

@[extern cpp "lean::uint64_of_nat"]
def Uint64.ofNat (n : @& Nat) : Uint64 := ⟨Fin.ofNat n⟩
@[extern cpp "lean::uint64_to_nat"]
def Uint64.toNat (n : Uint64) : Nat := n.val.val
@[extern cpp inline "#1 + #2"]
def Uint64.add (a b : Uint64) : Uint64 := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def Uint64.sub (a b : Uint64) : Uint64 := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def Uint64.mul (a b : Uint64) : Uint64 := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def Uint64.div (a b : Uint64) : Uint64 := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def Uint64.mod (a b : Uint64) : Uint64 := ⟨a.val % b.val⟩
@[extern cpp "lean::uint64_modn"]
def Uint64.modn (a : Uint64) (n : @& Nat) : Uint64 := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def Uint64.land (a b : Uint64) : Uint64 := ⟨Fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def Uint64.lor (a b : Uint64) : Uint64 := ⟨Fin.lor a.val b.val⟩
def Uint64.lt (a b : Uint64) : Prop := a.val < b.val
def Uint64.le (a b : Uint64) : Prop := a.val ≤ b.val

instance : HasZero Uint64     := ⟨Uint64.ofNat 0⟩
instance : HasOne Uint64      := ⟨Uint64.ofNat 1⟩
instance : HasAdd Uint64      := ⟨Uint64.add⟩
instance : HasSub Uint64      := ⟨Uint64.sub⟩
instance : HasMul Uint64      := ⟨Uint64.mul⟩
instance : HasMod Uint64      := ⟨Uint64.mod⟩
instance : HasModn Uint64     := ⟨Uint64.modn⟩
instance : HasDiv Uint64      := ⟨Uint64.div⟩
instance : HasLt Uint64       := ⟨Uint64.lt⟩
instance : HasLe Uint64       := ⟨Uint64.le⟩
instance : Inhabited Uint64    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def Uint64.decEq (a b : Uint64) : Decidable (a = b) :=
Uint64.casesOn a $ λ n, Uint64.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', Uint64.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def Uint64.decLt (a b : Uint64) : Decidable (a < b) :=
Uint64.casesOn a $ λ n, Uint64.casesOn b $ λ m,
  inferInstanceAs (Decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def Uint64.decLe (a b : Uint64) : Decidable (a ≤ b) :=
Uint64.casesOn a $ λ n, Uint64.casesOn b $ λ m,
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq Uint64 := {decEq := Uint64.decEq}
instance Uint64.hasDecidableLt (a b : Uint64) : Decidable (a < b) := Uint64.decLt a b
instance Uint64.hasDecidableLe (a b : Uint64) : Decidable (a ≤ b) := Uint64.decLe a b

def usizeSz : Nat := (2:Nat) ^ System.platform.nbits
structure Usize :=
(val : Fin usizeSz)

@[extern cpp "lean::usize_of_nat"]
def Usize.ofNat (n : @& Nat) : Usize := ⟨Fin.ofNat n⟩
@[extern cpp "lean::usize_to_nat"]
def Usize.toNat (n : Usize) : Nat := n.val.val
@[extern cpp inline "#1 + #2"]
def Usize.add (a b : Usize) : Usize := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def Usize.sub (a b : Usize) : Usize := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def Usize.mul (a b : Usize) : Usize := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def Usize.div (a b : Usize) : Usize := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def Usize.mod (a b : Usize) : Usize := ⟨a.val % b.val⟩
@[extern cpp "lean::usize_modn"]
def Usize.modn (a : Usize) (n : @& Nat) : Usize := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def Usize.land (a b : Usize) : Usize := ⟨Fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def Usize.lor (a b : Usize) : Usize := ⟨Fin.lor a.val b.val⟩
@[extern cpp inline "#1"]
def Usize.ofUint32 (a : Uint32) : Usize := Usize.ofNat (Uint32.toNat a)
@[extern cpp inline "((lean::usize)#1)"]
def Usize.ofUint64 (a : Uint64) : Usize := Usize.ofNat (Uint64.toNat a)
def Usize.lt (a b : Usize) : Prop := a.val < b.val
def Usize.le (a b : Usize) : Prop := a.val ≤ b.val

instance : HasZero Usize     := ⟨Usize.ofNat 0⟩
instance : HasOne Usize      := ⟨Usize.ofNat 1⟩
instance : HasAdd Usize      := ⟨Usize.add⟩
instance : HasSub Usize      := ⟨Usize.sub⟩
instance : HasMul Usize      := ⟨Usize.mul⟩
instance : HasMod Usize      := ⟨Usize.mod⟩
instance : HasModn Usize     := ⟨Usize.modn⟩
instance : HasDiv Usize      := ⟨Usize.div⟩
instance : HasLt Usize       := ⟨Usize.lt⟩
instance : HasLe Usize       := ⟨Usize.le⟩
instance : Inhabited Usize    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def Usize.decEq (a b : Usize) : Decidable (a = b) :=
Usize.casesOn a $ λ n, Usize.casesOn b $ λ m,
  if h : n = m then isTrue (h ▸ rfl) else isFalse (λ h', Usize.noConfusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def Usize.decLt (a b : Usize) : Decidable (a < b) :=
Usize.casesOn a $ λ n, Usize.casesOn b $ λ m,
  inferInstanceAs (Decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def Usize.decLe (a b : Usize) : Decidable (a ≤ b) :=
Usize.casesOn a $ λ n, Usize.casesOn b $ λ m,
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq Usize := {decEq := Usize.decEq}
instance Usize.hasDecidableLt (a b : Usize) : Decidable (a < b) := Usize.decLt a b
instance Usize.hasDecidableLe (a b : Usize) : Decidable (a ≤ b) := Usize.decLe a b

theorem Usize.modnLt {m : Nat} : ∀ (u : Usize), m > 0 → Usize.toNat (u %ₙ m) < m
| ⟨u⟩ h := Fin.modnLt u h
