/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic

open nat

def uint8_sz : nat := 65536
structure uint8 :=
(val : fin uint8_sz)

def uint8.of_nat (n : nat) : uint8 := ⟨fin.of_nat n⟩
def uint8.to_nat : uint8 → nat | ⟨a⟩ := a.val
def uint8.add  : uint8 → uint8 → uint8 | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
def uint8.sub  : uint8 → uint8 → uint8 | ⟨a⟩ ⟨b⟩ := ⟨a - b⟩
def uint8.mul  : uint8 → uint8 → uint8 | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
def uint8.div  : uint8 → uint8 → uint8 | ⟨a⟩ ⟨b⟩ := ⟨a / b⟩
def uint8.mod  : uint8 → uint8 → uint8 | ⟨a⟩ ⟨b⟩ := ⟨a % b⟩
def uint8.modn : uint8 → nat → uint8   | ⟨a⟩  b  := ⟨a %ₙ b⟩
def uint8.lt   : uint8 → uint8 → Prop  | ⟨a⟩ ⟨b⟩ := a < b
def uint8.le   : uint8 → uint8 → Prop  | ⟨a⟩ ⟨b⟩ := a ≤ b

instance : has_zero uint8     := ⟨⟨fin.of_nat 0⟩⟩
instance : has_one uint8      := ⟨⟨fin.of_nat 1⟩⟩
instance : has_add uint8      := ⟨uint8.add⟩
instance : has_sub uint8      := ⟨uint8.sub⟩
instance : has_mul uint8      := ⟨uint8.mul⟩
instance : has_mod uint8      := ⟨uint8.mod⟩
instance : has_modn uint8     := ⟨uint8.modn⟩
instance : has_div uint8      := ⟨uint8.div⟩
instance : has_lt uint8       := ⟨uint8.lt⟩
instance : has_le uint8       := ⟨uint8.le⟩
instance : inhabited uint8    := ⟨0⟩

def uint8.dec_eq : Π (a b : uint8), decidable (a = b)
| ⟨a⟩ ⟨b⟩ := if h : a = b then is_true (h ▸ rfl) else is_false (λ h', uint8.no_confusion h' (λ h', absurd h' h))

def uint8.dec_lt : Π (a b : uint8), decidable (a < b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a < b))

def uint8.dec_le : Π (a b : uint8), decidable (a ≤ b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a ≤ b))

instance : decidable_eq uint8 := {dec_eq := uint8.dec_eq}
instance uint8.has_decidable_lt (a b : uint8) : decidable (a < b) := uint8.dec_lt a b
instance uint8.has_decidable_le (a b : uint8) : decidable (a ≤ b) := uint8.dec_le a b

def uint16_sz : nat := 65536
structure uint16 :=
(val : fin uint16_sz)

def uint16.of_nat (n : nat) : uint16 := ⟨fin.of_nat n⟩
def uint16.to_nat : uint16 → nat | ⟨a⟩ := a.val
def uint16.add  : uint16 → uint16 → uint16 | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
def uint16.sub  : uint16 → uint16 → uint16 | ⟨a⟩ ⟨b⟩ := ⟨a - b⟩
def uint16.mul  : uint16 → uint16 → uint16 | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
def uint16.div  : uint16 → uint16 → uint16 | ⟨a⟩ ⟨b⟩ := ⟨a / b⟩
def uint16.mod  : uint16 → uint16 → uint16 | ⟨a⟩ ⟨b⟩ := ⟨a % b⟩
def uint16.modn : uint16 → nat → uint16    | ⟨a⟩  b  := ⟨a %ₙ b⟩
def uint16.lt   : uint16 → uint16 → Prop   | ⟨a⟩ ⟨b⟩ := a < b
def uint16.le   : uint16 → uint16 → Prop   | ⟨a⟩ ⟨b⟩ := a ≤ b

instance : has_zero uint16     := ⟨⟨fin.of_nat 0⟩⟩
instance : has_one uint16      := ⟨⟨fin.of_nat 1⟩⟩
instance : has_add uint16      := ⟨uint16.add⟩
instance : has_sub uint16      := ⟨uint16.sub⟩
instance : has_mul uint16      := ⟨uint16.mul⟩
instance : has_mod uint16      := ⟨uint16.mod⟩
instance : has_modn uint16     := ⟨uint16.modn⟩
instance : has_div uint16      := ⟨uint16.div⟩
instance : has_lt uint16       := ⟨uint16.lt⟩
instance : has_le uint16       := ⟨uint16.le⟩
instance : inhabited uint16    := ⟨0⟩

def uint16.dec_eq : Π (a b : uint16), decidable (a = b)
| ⟨a⟩ ⟨b⟩ := if h : a = b then is_true (h ▸ rfl) else is_false (λ h', uint16.no_confusion h' (λ h', absurd h' h))

def uint16.dec_lt : Π (a b : uint16), decidable (a < b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a < b))

def uint16.dec_le : Π (a b : uint16), decidable (a ≤ b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a ≤ b))

instance : decidable_eq uint16 := {dec_eq := uint16.dec_eq}
instance uint16.has_decidable_lt (a b : uint16) : decidable (a < b) := uint16.dec_lt a b
instance uint16.has_decidable_le (a b : uint16) : decidable (a ≤ b) := uint16.dec_le a b

def uint32_sz : nat := 4294967296
structure uint32 :=
(val : fin uint32_sz)

def uint32.of_nat (n : nat) : uint32 := ⟨fin.of_nat n⟩
def uint32.to_nat : uint32 → nat | ⟨a⟩ := a.val
def uint32.add  : uint32 → uint32 → uint32 | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
def uint32.sub  : uint32 → uint32 → uint32 | ⟨a⟩ ⟨b⟩ := ⟨a - b⟩
def uint32.mul  : uint32 → uint32 → uint32 | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
def uint32.div  : uint32 → uint32 → uint32 | ⟨a⟩ ⟨b⟩ := ⟨a / b⟩
def uint32.mod  : uint32 → uint32 → uint32 | ⟨a⟩ ⟨b⟩ := ⟨a % b⟩
def uint32.modn : uint32 → nat → uint32    | ⟨a⟩  b  := ⟨a %ₙ b⟩
def uint32.lt   : uint32 → uint32 → Prop   | ⟨a⟩ ⟨b⟩ := a < b
def uint32.le   : uint32 → uint32 → Prop   | ⟨a⟩ ⟨b⟩ := a ≤ b

instance : has_zero uint32     := ⟨⟨fin.of_nat 0⟩⟩
instance : has_one uint32      := ⟨⟨fin.of_nat 1⟩⟩
instance : has_add uint32      := ⟨uint32.add⟩
instance : has_sub uint32      := ⟨uint32.sub⟩
instance : has_mul uint32      := ⟨uint32.mul⟩
instance : has_mod uint32      := ⟨uint32.mod⟩
instance : has_modn uint32     := ⟨uint32.modn⟩
instance : has_div uint32      := ⟨uint32.div⟩
instance : has_lt uint32       := ⟨uint32.lt⟩
instance : has_le uint32       := ⟨uint32.le⟩
instance : inhabited uint32    := ⟨0⟩

def uint32.dec_eq : Π (a b : uint32), decidable (a = b)
| ⟨a⟩ ⟨b⟩ := if h : a = b then is_true (h ▸ rfl) else is_false (λ h', uint32.no_confusion h' (λ h', absurd h' h))

def uint32.dec_lt : Π (a b : uint32), decidable (a < b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a < b))

def uint32.dec_le : Π (a b : uint32), decidable (a ≤ b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a ≤ b))

instance : decidable_eq uint32 := {dec_eq := uint32.dec_eq}
instance uint32.has_decidable_lt (a b : uint32) : decidable (a < b) := uint32.dec_lt a b
instance uint32.has_decidable_le (a b : uint32) : decidable (a ≤ b) := uint32.dec_le a b

def uint64_sz : nat := 18446744073709551616
structure uint64 :=
(val : fin uint64_sz)

def uint64.of_nat (n : nat) : uint64 := ⟨fin.of_nat n⟩
def uint64.to_nat : uint64 → nat | ⟨a⟩ := a.val
def uint64.add  : uint64 → uint64 → uint64 | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
def uint64.sub  : uint64 → uint64 → uint64 | ⟨a⟩ ⟨b⟩ := ⟨a - b⟩
def uint64.mul  : uint64 → uint64 → uint64 | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
def uint64.div  : uint64 → uint64 → uint64 | ⟨a⟩ ⟨b⟩ := ⟨a / b⟩
def uint64.mod  : uint64 → uint64 → uint64 | ⟨a⟩ ⟨b⟩ := ⟨a % b⟩
def uint64.modn : uint64 → nat → uint64    | ⟨a⟩  b  := ⟨a %ₙ b⟩
def uint64.lt   : uint64 → uint64 → Prop   | ⟨a⟩ ⟨b⟩ := a < b
def uint64.le   : uint64 → uint64 → Prop   | ⟨a⟩ ⟨b⟩ := a ≤ b

instance : has_zero uint64     := ⟨⟨fin.of_nat 0⟩⟩
instance : has_one uint64      := ⟨⟨fin.of_nat 1⟩⟩
instance : has_add uint64      := ⟨uint64.add⟩
instance : has_sub uint64      := ⟨uint64.sub⟩
instance : has_mul uint64      := ⟨uint64.mul⟩
instance : has_mod uint64      := ⟨uint64.mod⟩
instance : has_modn uint64     := ⟨uint64.modn⟩
instance : has_div uint64      := ⟨uint64.div⟩
instance : has_lt uint64       := ⟨uint64.lt⟩
instance : has_le uint64       := ⟨uint64.le⟩
instance : inhabited uint64    := ⟨0⟩

def uint64.dec_eq : Π (a b : uint64), decidable (a = b)
| ⟨a⟩ ⟨b⟩ := if h : a = b then is_true (h ▸ rfl) else is_false (λ h', uint64.no_confusion h' (λ h', absurd h' h))

def uint64.dec_lt : Π (a b : uint64), decidable (a < b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a < b))

def uint64.dec_le : Π (a b : uint64), decidable (a ≤ b)
| ⟨a⟩ ⟨b⟩ := infer_instance_as (decidable (a ≤ b))

instance : decidable_eq uint64 := {dec_eq := uint64.dec_eq}
instance uint64.has_decidable_lt (a b : uint64) : decidable (a < b) := uint64.dec_lt a b
instance uint64.has_decidable_le (a b : uint64) : decidable (a ≤ b) := uint64.dec_le a b
