/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic
import init.system.platform

open Nat

def uint8Sz : Nat := 256
structure UInt8 :=
(val : Fin uint8Sz)

@[extern "lean_uint8_of_nat"]
def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨Fin.ofNat n⟩
@[extern "lean_uint8_to_nat"]
def UInt8.toNat (n : UInt8) : Nat := n.val.val
@[extern c inline "#1 + #2"]
def UInt8.add (a b : UInt8) : UInt8 := ⟨a.val + b.val⟩
@[extern c inline "#1 - #2"]
def UInt8.sub (a b : UInt8) : UInt8 := ⟨a.val - b.val⟩
@[extern c inline "#1 * #2"]
def UInt8.mul (a b : UInt8) : UInt8 := ⟨a.val * b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 / #2"]
def UInt8.div (a b : UInt8) : UInt8 := ⟨a.val / b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 % #2"]
def UInt8.mod (a b : UInt8) : UInt8 := ⟨a.val % b.val⟩
@[extern "lean_uint8_modn"]
def UInt8.modn (a : UInt8) (n : @& Nat) : UInt8 := ⟨a.val %ₙ n⟩
@[extern c inline "#1 & #2"]
def UInt8.land (a b : UInt8) : UInt8 := ⟨Fin.land a.val b.val⟩
@[extern c inline "#1 | #2"]
def UInt8.lor (a b : UInt8) : UInt8 := ⟨Fin.lor a.val b.val⟩
def UInt8.lt (a b : UInt8) : Prop := a.val < b.val
def UInt8.le (a b : UInt8) : Prop := a.val ≤ b.val

instance : HasZero UInt8     := ⟨UInt8.ofNat 0⟩
instance : HasOne UInt8      := ⟨UInt8.ofNat 1⟩
instance : HasAdd UInt8      := ⟨UInt8.add⟩
instance : HasSub UInt8      := ⟨UInt8.sub⟩
instance : HasMul UInt8      := ⟨UInt8.mul⟩
instance : HasMod UInt8      := ⟨UInt8.mod⟩
instance : HasModn UInt8     := ⟨UInt8.modn⟩
instance : HasDiv UInt8      := ⟨UInt8.div⟩
instance : HasLess UInt8     := ⟨UInt8.lt⟩
instance : HasLessEq UInt8   := ⟨UInt8.le⟩
instance : Inhabited UInt8   := ⟨0⟩

@[extern c inline "#1 == #2"]
def UInt8.decEq (a b : UInt8) : Decidable (a = b) :=
UInt8.casesOn a $ fun n => UInt8.casesOn b $ fun m =>
  if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt8.noConfusion h' (fun h' => absurd h' h))

@[extern c inline "#1 < #2"]
def UInt8.decLt (a b : UInt8) : Decidable (a < b) :=
UInt8.casesOn a $ fun n => UInt8.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n < m))

@[extern c inline "#1 <= #2"]
def UInt8.decLe (a b : UInt8) : Decidable (a ≤ b) :=
UInt8.casesOn a $ fun n => UInt8.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq UInt8 := {decEq := UInt8.decEq}
instance UInt8.hasDecidableLt (a b : UInt8) : Decidable (a < b) := UInt8.decLt a b
instance UInt8.hasDecidableLe (a b : UInt8) : Decidable (a ≤ b) := UInt8.decLe a b

def uint16Sz : Nat := 65536
structure UInt16 :=
(val : Fin uint16Sz)

@[extern "lean_uint16_of_nat"]
def UInt16.ofNat (n : @& Nat) : UInt16 := ⟨Fin.ofNat n⟩
@[extern "lean_uint16_to_nat"]
def UInt16.toNat (n : UInt16) : Nat := n.val.val
@[extern c inline "#1 + #2"]
def UInt16.add (a b : UInt16) : UInt16 := ⟨a.val + b.val⟩
@[extern c inline "#1 - #2"]
def UInt16.sub (a b : UInt16) : UInt16 := ⟨a.val - b.val⟩
@[extern c inline "#1 * #2"]
def UInt16.mul (a b : UInt16) : UInt16 := ⟨a.val * b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 / #2"]
def UInt16.div (a b : UInt16) : UInt16 := ⟨a.val / b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 % #2"]
def UInt16.mod (a b : UInt16) : UInt16 := ⟨a.val % b.val⟩
@[extern "lean_uint16_modn"]
def UInt16.modn (a : UInt16) (n : @& Nat) : UInt16 := ⟨a.val %ₙ n⟩
@[extern c inline "#1 & #2"]
def UInt16.land (a b : UInt16) : UInt16 := ⟨Fin.land a.val b.val⟩
@[extern c inline "#1 | #2"]
def UInt16.lor (a b : UInt16) : UInt16 := ⟨Fin.lor a.val b.val⟩
def UInt16.lt (a b : UInt16) : Prop := a.val < b.val
def UInt16.le (a b : UInt16) : Prop := a.val ≤ b.val

instance : HasZero UInt16     := ⟨UInt16.ofNat 0⟩
instance : HasOne UInt16      := ⟨UInt16.ofNat 1⟩
instance : HasAdd UInt16      := ⟨UInt16.add⟩
instance : HasSub UInt16      := ⟨UInt16.sub⟩
instance : HasMul UInt16      := ⟨UInt16.mul⟩
instance : HasMod UInt16      := ⟨UInt16.mod⟩
instance : HasModn UInt16     := ⟨UInt16.modn⟩
instance : HasDiv UInt16      := ⟨UInt16.div⟩
instance : HasLess UInt16     := ⟨UInt16.lt⟩
instance : HasLessEq UInt16   := ⟨UInt16.le⟩
instance : Inhabited UInt16   := ⟨0⟩

@[extern c inline "#1 == #2"]
def UInt16.decEq (a b : UInt16) : Decidable (a = b) :=
UInt16.casesOn a $ fun n => UInt16.casesOn b $ fun m =>
  if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt16.noConfusion h' (fun h' => absurd h' h))

@[extern c inline "#1 < #2"]
def UInt16.decLt (a b : UInt16) : Decidable (a < b) :=
UInt16.casesOn a $ fun n => UInt16.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n < m))

@[extern c inline "#1 <= #2"]
def UInt16.decLe (a b : UInt16) : Decidable (a ≤ b) :=
UInt16.casesOn a $ fun n => UInt16.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq UInt16 := {decEq := UInt16.decEq}
instance UInt16.hasDecidableLt (a b : UInt16) : Decidable (a < b) := UInt16.decLt a b
instance UInt16.hasDecidableLe (a b : UInt16) : Decidable (a ≤ b) := UInt16.decLe a b

def uint32Sz : Nat := 4294967296
structure UInt32 :=
(val : Fin uint32Sz)

@[extern "lean_uint32_of_nat"]
def UInt32.ofNat (n : @& Nat) : UInt32 := ⟨Fin.ofNat n⟩
@[extern "lean_uint32_to_nat"]
def UInt32.toNat (n : UInt32) : Nat := n.val.val
@[extern c inline "#1 + #2"]
def UInt32.add (a b : UInt32) : UInt32 := ⟨a.val + b.val⟩
@[extern c inline "#1 - #2"]
def UInt32.sub (a b : UInt32) : UInt32 := ⟨a.val - b.val⟩
@[extern c inline "#1 * #2"]
def UInt32.mul (a b : UInt32) : UInt32 := ⟨a.val * b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 / #2"]
def UInt32.div (a b : UInt32) : UInt32 := ⟨a.val / b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 % #2"]
def UInt32.mod (a b : UInt32) : UInt32 := ⟨a.val % b.val⟩
@[extern "lean_uint32_modn"]
def UInt32.modn (a : UInt32) (n : @& Nat) : UInt32 := ⟨a.val %ₙ n⟩
@[extern c inline "#1 & #2"]
def UInt32.land (a b : UInt32) : UInt32 := ⟨Fin.land a.val b.val⟩
@[extern c inline "#1 | #2"]
def UInt32.lor (a b : UInt32) : UInt32 := ⟨Fin.lor a.val b.val⟩
def UInt32.lt (a b : UInt32) : Prop := a.val < b.val
def UInt32.le (a b : UInt32) : Prop := a.val ≤ b.val

instance : HasZero UInt32     := ⟨UInt32.ofNat 0⟩
instance : HasOne UInt32      := ⟨UInt32.ofNat 1⟩
instance : HasAdd UInt32      := ⟨UInt32.add⟩
instance : HasSub UInt32      := ⟨UInt32.sub⟩
instance : HasMul UInt32      := ⟨UInt32.mul⟩
instance : HasMod UInt32      := ⟨UInt32.mod⟩
instance : HasModn UInt32     := ⟨UInt32.modn⟩
instance : HasDiv UInt32      := ⟨UInt32.div⟩
instance : HasLess UInt32     := ⟨UInt32.lt⟩
instance : HasLessEq UInt32   := ⟨UInt32.le⟩
instance : Inhabited UInt32   := ⟨0⟩

@[extern c inline "#1 == #2"]
def UInt32.decEq (a b : UInt32) : Decidable (a = b) :=
UInt32.casesOn a $ fun n => UInt32.casesOn b $ fun m =>
  if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt32.noConfusion h' (fun h' => absurd h' h))

@[extern c inline "#1 < #2"]
def UInt32.decLt (a b : UInt32) : Decidable (a < b) :=
UInt32.casesOn a $ fun n => UInt32.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n < m))

@[extern c inline "#1 <= #2"]
def UInt32.decLe (a b : UInt32) : Decidable (a ≤ b) :=
UInt32.casesOn a $ fun n => UInt32.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq UInt32 := {decEq := UInt32.decEq}
instance UInt32.hasDecidableLt (a b : UInt32) : Decidable (a < b) := UInt32.decLt a b
instance UInt32.hasDecidableLe (a b : UInt32) : Decidable (a ≤ b) := UInt32.decLe a b

def uint64Sz : Nat := 18446744073709551616
structure UInt64 :=
(val : Fin uint64Sz)

@[extern "lean_uint64_of_nat"]
def UInt64.ofNat (n : @& Nat) : UInt64 := ⟨Fin.ofNat n⟩
@[extern "lean_uint64_to_nat"]
def UInt64.toNat (n : UInt64) : Nat := n.val.val
@[extern c inline "#1 + #2"]
def UInt64.add (a b : UInt64) : UInt64 := ⟨a.val + b.val⟩
@[extern c inline "#1 - #2"]
def UInt64.sub (a b : UInt64) : UInt64 := ⟨a.val - b.val⟩
@[extern c inline "#1 * #2"]
def UInt64.mul (a b : UInt64) : UInt64 := ⟨a.val * b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 / #2"]
def UInt64.div (a b : UInt64) : UInt64 := ⟨a.val / b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 % #2"]
def UInt64.mod (a b : UInt64) : UInt64 := ⟨a.val % b.val⟩
@[extern "lean_uint64_modn"]
def UInt64.modn (a : UInt64) (n : @& Nat) : UInt64 := ⟨a.val %ₙ n⟩
@[extern c inline "#1 & #2"]
def UInt64.land (a b : UInt64) : UInt64 := ⟨Fin.land a.val b.val⟩
@[extern c inline "#1 | #2"]
def UInt64.lor (a b : UInt64) : UInt64 := ⟨Fin.lor a.val b.val⟩
def UInt64.lt (a b : UInt64) : Prop := a.val < b.val
def UInt64.le (a b : UInt64) : Prop := a.val ≤ b.val

instance : HasZero UInt64     := ⟨UInt64.ofNat 0⟩
instance : HasOne UInt64      := ⟨UInt64.ofNat 1⟩
instance : HasAdd UInt64      := ⟨UInt64.add⟩
instance : HasSub UInt64      := ⟨UInt64.sub⟩
instance : HasMul UInt64      := ⟨UInt64.mul⟩
instance : HasMod UInt64      := ⟨UInt64.mod⟩
instance : HasModn UInt64     := ⟨UInt64.modn⟩
instance : HasDiv UInt64      := ⟨UInt64.div⟩
instance : HasLess UInt64     := ⟨UInt64.lt⟩
instance : HasLessEq UInt64   := ⟨UInt64.le⟩
instance : Inhabited UInt64   := ⟨0⟩

@[extern c inline "#1 == #2"]
def UInt64.decEq (a b : UInt64) : Decidable (a = b) :=
UInt64.casesOn a $ fun n => UInt64.casesOn b $ fun m =>
  if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt64.noConfusion h' (fun h' => absurd h' h))

@[extern c inline "#1 < #2"]
def UInt64.decLt (a b : UInt64) : Decidable (a < b) :=
UInt64.casesOn a $ fun n => UInt64.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n < m))

@[extern c inline "#1 <= #2"]
def UInt64.decLe (a b : UInt64) : Decidable (a ≤ b) :=
UInt64.casesOn a $ fun n => UInt64.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq UInt64 := {decEq := UInt64.decEq}
instance UInt64.hasDecidableLt (a b : UInt64) : Decidable (a < b) := UInt64.decLt a b
instance UInt64.hasDecidableLe (a b : UInt64) : Decidable (a ≤ b) := UInt64.decLe a b

def usizeSz : Nat := (2:Nat) ^ System.Platform.numBits
structure USize :=
(val : Fin usizeSz)

theorem usizeSzGt0 : usizeSz > 0 :=
Nat.posPowOfPos System.Platform.numBits (Nat.zeroLtSucc _)

@[extern "lean_usize_of_nat"]
def USize.ofNat (n : @& Nat) : USize := ⟨Fin.ofNat' n usizeSzGt0⟩
@[extern "lean_usize_to_nat"]
def USize.toNat (n : USize) : Nat := n.val.val
@[extern c inline "#1 + #2"]
def USize.add (a b : USize) : USize := ⟨a.val + b.val⟩
@[extern c inline "#1 - #2"]
def USize.sub (a b : USize) : USize := ⟨a.val - b.val⟩
@[extern c inline "#1 * #2"]
def USize.mul (a b : USize) : USize := ⟨a.val * b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 / #2"]
def USize.div (a b : USize) : USize := ⟨a.val / b.val⟩
@[extern c inline "#2 == 0 ? 0 : #1 % #2"]
def USize.mod (a b : USize) : USize := ⟨a.val % b.val⟩
@[extern "lean_usize_modn"]
def USize.modn (a : USize) (n : @& Nat) : USize := ⟨a.val %ₙ n⟩
@[extern c inline "#1 & #2"]
def USize.land (a b : USize) : USize := ⟨Fin.land a.val b.val⟩
@[extern c inline "#1 | #2"]
def USize.lor (a b : USize) : USize := ⟨Fin.lor a.val b.val⟩
@[extern c inline "#1"]
def USize.ofUInt32 (a : UInt32) : USize := USize.ofNat (UInt32.toNat a)
@[extern c inline "((size_t)#1)"]
def USize.ofUInt64 (a : UInt64) : USize := USize.ofNat (UInt64.toNat a)
-- TODO(Leo): give reference implementation for shift_left and shift_right, and define them for other UInt types
@[extern c inline "#1 << #2"]
constant USize.shift_left (a b : USize) : USize := USize.ofNat (default _)
@[extern c inline "#1 >> #2"]
constant USize.shift_right (a b : USize) : USize := USize.ofNat (default _)
def USize.lt (a b : USize) : Prop := a.val < b.val
def USize.le (a b : USize) : Prop := a.val ≤ b.val

instance : HasZero USize     := ⟨USize.ofNat 0⟩
instance : HasOne USize      := ⟨USize.ofNat 1⟩
instance : HasAdd USize      := ⟨USize.add⟩
instance : HasSub USize      := ⟨USize.sub⟩
instance : HasMul USize      := ⟨USize.mul⟩
instance : HasMod USize      := ⟨USize.mod⟩
instance : HasModn USize     := ⟨USize.modn⟩
instance : HasDiv USize      := ⟨USize.div⟩
instance : HasLess USize     := ⟨USize.lt⟩
instance : HasLessEq USize   := ⟨USize.le⟩
instance : Inhabited USize   := ⟨0⟩

@[extern c inline "#1 == #2"]
def USize.decEq (a b : USize) : Decidable (a = b) :=
USize.casesOn a $ fun n => USize.casesOn b $ fun m =>
  if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => USize.noConfusion h' (fun h' => absurd h' h))

@[extern c inline "#1 < #2"]
def USize.decLt (a b : USize) : Decidable (a < b) :=
USize.casesOn a $ fun n => USize.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n < m))

@[extern c inline "#1 <= #2"]
def USize.decLe (a b : USize) : Decidable (a ≤ b) :=
USize.casesOn a $ fun n => USize.casesOn b $ fun m =>
  inferInstanceAs (Decidable (n <= m))

instance : DecidableEq USize := {decEq := USize.decEq}
instance USize.hasDecidableLt (a b : USize) : Decidable (a < b) := USize.decLt a b
instance USize.hasDecidableLe (a b : USize) : Decidable (a ≤ b) := USize.decLe a b

theorem USize.modnLt {m : Nat} : ∀ (u : USize), m > 0 → USize.toNat (u %ₙ m) < m
| ⟨u⟩, h => Fin.modnLt u h
