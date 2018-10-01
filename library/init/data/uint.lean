/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic

open nat
def uint8_sz : nat := 65536
def uint8 := fin uint8_sz

def uint16_sz : nat := 65536
def uint16 := fin uint16_sz

def uint32_sz : nat := 4294967296
def uint32 := fin uint32_sz

def uint64_sz : nat := 18446744073709551616
def uint64 := fin uint64_sz

instance : decidable_eq uint8 := infer_instance_as (decidable_eq (fin uint8_sz))
instance : decidable_eq uint16 := infer_instance_as (decidable_eq (fin uint16_sz))
instance : decidable_eq uint32 := infer_instance_as (decidable_eq (fin uint32_sz))
instance : decidable_eq uint64 := infer_instance_as (decidable_eq (fin uint64_sz))

instance : has_zero uint8  := ⟨fin.of_nat 0⟩
instance : has_one uint8   := ⟨fin.of_nat 1⟩
instance : has_add uint8   := ⟨fin.add⟩
instance : has_sub uint8   := ⟨fin.sub⟩
instance : has_mul uint8   := ⟨fin.mul⟩
instance : has_mod uint8   := ⟨fin.mod⟩
instance : has_modn uint8  := ⟨fin.modn⟩
instance : has_div uint8   := ⟨fin.div⟩
instance : has_lt uint8    := ⟨fin.lt⟩
instance : has_le uint8    := ⟨fin.le⟩
instance : inhabited uint8 := ⟨0⟩

instance : has_zero uint16  := ⟨fin.of_nat 0⟩
instance : has_one uint16   := ⟨fin.of_nat 1⟩
instance : has_add uint16   := ⟨fin.add⟩
instance : has_sub uint16   := ⟨fin.sub⟩
instance : has_mul uint16   := ⟨fin.mul⟩
instance : has_mod uint16   := ⟨fin.mod⟩
instance : has_modn uint16  := ⟨fin.modn⟩
instance : has_div uint16   := ⟨fin.div⟩
instance : has_lt uint16    := ⟨fin.lt⟩
instance : has_le uint16    := ⟨fin.le⟩
instance : inhabited uint16 := ⟨0⟩

instance : has_zero uint32  := ⟨fin.of_nat 0⟩
instance : has_one uint32   := ⟨fin.of_nat 1⟩
instance : has_add uint32   := ⟨fin.add⟩
instance : has_sub uint32   := ⟨fin.sub⟩
instance : has_mul uint32   := ⟨fin.mul⟩
instance : has_mod uint32   := ⟨fin.mod⟩
instance : has_modn uint32  := ⟨fin.modn⟩
instance : has_div uint32   := ⟨fin.div⟩
instance : has_lt uint32    := ⟨fin.lt⟩
instance : has_le uint32    := ⟨fin.le⟩
instance : inhabited uint32 := ⟨0⟩

instance : has_zero uint64  := ⟨fin.of_nat 0⟩
instance : has_one uint64   := ⟨fin.of_nat 1⟩
instance : has_add uint64   := ⟨fin.add⟩
instance : has_sub uint64   := ⟨fin.sub⟩
instance : has_mul uint64   := ⟨fin.mul⟩
instance : has_mod uint64   := ⟨fin.mod⟩
instance : has_modn uint64  := ⟨fin.modn⟩
instance : has_div uint64   := ⟨fin.div⟩
instance : has_lt uint64    := ⟨fin.lt⟩
instance : has_le uint64    := ⟨fin.le⟩
instance : inhabited uint64 := ⟨0⟩

def uint8.of_nat (n : nat) : uint8 := fin.of_nat n
def uint8.to_nat (u : uint8) : nat := u.val
def uint16.of_nat (n : nat) : uint16 := fin.of_nat n
def uint16.to_nat (u : uint16) : nat := u.val
def uint32.of_nat (n : nat) : uint32 := fin.of_nat n
def uint32.to_nat (u : uint32) : nat := u.val
def uint64.of_nat (n : nat) : uint64 := fin.of_nat n
def uint64.to_nat (u : uint64) : nat := u.val

attribute [irreducible] uint8 uint16 uint32 uint64
