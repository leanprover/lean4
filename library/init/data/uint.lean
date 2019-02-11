/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic

open nat

def uint8_sz : nat := 256
structure uint8 :=
(val : fin uint8_sz)

@[extern cpp "lean::uint8_of_nat"]
def uint8.of_nat (n : @& nat) : uint8 := ⟨fin.of_nat n⟩
@[extern cpp "lean::uint8_to_nat"]
def uint8.to_nat (n : uint8) : nat := n.val.val
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
def uint8.lt (a b : uint8) : Prop := a.val < b.val
def uint8.le (a b : uint8) : Prop := a.val ≤ b.val

instance : has_zero uint8     := ⟨uint8.of_nat 0⟩
instance : has_one uint8      := ⟨uint8.of_nat 1⟩
instance : has_add uint8      := ⟨uint8.add⟩
instance : has_sub uint8      := ⟨uint8.sub⟩
instance : has_mul uint8      := ⟨uint8.mul⟩
instance : has_mod uint8      := ⟨uint8.mod⟩
instance : has_modn uint8     := ⟨uint8.modn⟩
instance : has_div uint8      := ⟨uint8.div⟩
instance : has_lt uint8       := ⟨uint8.lt⟩
instance : has_le uint8       := ⟨uint8.le⟩
instance : inhabited uint8    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint8.dec_eq (a b : uint8) : decidable (a = b) :=
uint8.cases_on a $ λ n, uint8.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', uint8.no_confusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint8.dec_lt (a b : uint8) : decidable (a < b) :=
uint8.cases_on a $ λ n, uint8.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint8.dec_le (a b : uint8) : decidable (a ≤ b) :=
uint8.cases_on a $ λ n, uint8.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq uint8 := {dec_eq := uint8.dec_eq}
instance uint8.has_decidable_lt (a b : uint8) : decidable (a < b) := uint8.dec_lt a b
instance uint8.has_decidable_le (a b : uint8) : decidable (a ≤ b) := uint8.dec_le a b

def uint16_sz : nat := 65536
structure uint16 :=
(val : fin uint16_sz)

@[extern cpp "lean::uint16_of_nat"]
def uint16.of_nat (n : @& nat) : uint16 := ⟨fin.of_nat n⟩
@[extern cpp "lean::uint16_to_nat"]
def uint16.to_nat (n : uint16) : nat := n.val.val
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
def uint16.lt (a b : uint16) : Prop := a.val < b.val
def uint16.le (a b : uint16) : Prop := a.val ≤ b.val

instance : has_zero uint16     := ⟨uint16.of_nat 0⟩
instance : has_one uint16      := ⟨uint16.of_nat 1⟩
instance : has_add uint16      := ⟨uint16.add⟩
instance : has_sub uint16      := ⟨uint16.sub⟩
instance : has_mul uint16      := ⟨uint16.mul⟩
instance : has_mod uint16      := ⟨uint16.mod⟩
instance : has_modn uint16     := ⟨uint16.modn⟩
instance : has_div uint16      := ⟨uint16.div⟩
instance : has_lt uint16       := ⟨uint16.lt⟩
instance : has_le uint16       := ⟨uint16.le⟩
instance : inhabited uint16    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint16.dec_eq (a b : uint16) : decidable (a = b) :=
uint16.cases_on a $ λ n, uint16.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', uint16.no_confusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint16.dec_lt (a b : uint16) : decidable (a < b) :=
uint16.cases_on a $ λ n, uint16.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint16.dec_le (a b : uint16) : decidable (a ≤ b) :=
uint16.cases_on a $ λ n, uint16.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq uint16 := {dec_eq := uint16.dec_eq}
instance uint16.has_decidable_lt (a b : uint16) : decidable (a < b) := uint16.dec_lt a b
instance uint16.has_decidable_le (a b : uint16) : decidable (a ≤ b) := uint16.dec_le a b

def uint32_sz : nat := 4294967296
structure uint32 :=
(val : fin uint32_sz)

@[extern cpp "lean::uint32_of_nat"]
def uint32.of_nat (n : @& nat) : uint32 := ⟨fin.of_nat n⟩
@[extern cpp "lean::uint32_to_nat"]
def uint32.to_nat (n : uint32) : nat := n.val.val
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
def uint32.lt (a b : uint32) : Prop := a.val < b.val
def uint32.le (a b : uint32) : Prop := a.val ≤ b.val

instance : has_zero uint32     := ⟨uint32.of_nat 0⟩
instance : has_one uint32      := ⟨uint32.of_nat 1⟩
instance : has_add uint32      := ⟨uint32.add⟩
instance : has_sub uint32      := ⟨uint32.sub⟩
instance : has_mul uint32      := ⟨uint32.mul⟩
instance : has_mod uint32      := ⟨uint32.mod⟩
instance : has_modn uint32     := ⟨uint32.modn⟩
instance : has_div uint32      := ⟨uint32.div⟩
instance : has_lt uint32       := ⟨uint32.lt⟩
instance : has_le uint32       := ⟨uint32.le⟩
instance : inhabited uint32    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint32.dec_eq (a b : uint32) : decidable (a = b) :=
uint32.cases_on a $ λ n, uint32.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', uint32.no_confusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint32.dec_lt (a b : uint32) : decidable (a < b) :=
uint32.cases_on a $ λ n, uint32.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint32.dec_le (a b : uint32) : decidable (a ≤ b) :=
uint32.cases_on a $ λ n, uint32.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq uint32 := {dec_eq := uint32.dec_eq}
instance uint32.has_decidable_lt (a b : uint32) : decidable (a < b) := uint32.dec_lt a b
instance uint32.has_decidable_le (a b : uint32) : decidable (a ≤ b) := uint32.dec_le a b

def uint64_sz : nat := 18446744073709551616
structure uint64 :=
(val : fin uint64_sz)

@[extern cpp "lean::uint64_of_nat"]
def uint64.of_nat (n : @& nat) : uint64 := ⟨fin.of_nat n⟩
@[extern cpp "lean::uint64_to_nat"]
def uint64.to_nat (n : uint64) : nat := n.val.val
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
def uint64.lt (a b : uint64) : Prop := a.val < b.val
def uint64.le (a b : uint64) : Prop := a.val ≤ b.val

instance : has_zero uint64     := ⟨uint64.of_nat 0⟩
instance : has_one uint64      := ⟨uint64.of_nat 1⟩
instance : has_add uint64      := ⟨uint64.add⟩
instance : has_sub uint64      := ⟨uint64.sub⟩
instance : has_mul uint64      := ⟨uint64.mul⟩
instance : has_mod uint64      := ⟨uint64.mod⟩
instance : has_modn uint64     := ⟨uint64.modn⟩
instance : has_div uint64      := ⟨uint64.div⟩
instance : has_lt uint64       := ⟨uint64.lt⟩
instance : has_le uint64       := ⟨uint64.le⟩
instance : inhabited uint64    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def uint64.dec_eq (a b : uint64) : decidable (a = b) :=
uint64.cases_on a $ λ n, uint64.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', uint64.no_confusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def uint64.dec_lt (a b : uint64) : decidable (a < b) :=
uint64.cases_on a $ λ n, uint64.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def uint64.dec_le (a b : uint64) : decidable (a ≤ b) :=
uint64.cases_on a $ λ n, uint64.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq uint64 := {dec_eq := uint64.dec_eq}
instance uint64.has_decidable_lt (a b : uint64) : decidable (a < b) := uint64.dec_lt a b
instance uint64.has_decidable_le (a b : uint64) : decidable (a ≤ b) := uint64.dec_le a b
