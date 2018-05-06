/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.platform init.data.fin

def usize_sz : nat := (2:nat) ^ system.platform.nbits
def usize : Type := fin usize_sz

instance : decidable_eq usize :=
fin.decidable_eq usize_sz

theorem usize_sz_pos : usize_sz > 0 :=
show 0 < (2:nat) ^ system.platform.nbits, from
nat.pos_pow_of_pos _ (nat.zero_lt_bit0 nat.one_ne_zero)

def usize.of_nat (a : nat) : usize :=
⟨a % usize_sz, nat.mod_lt _ usize_sz_pos⟩

instance : has_zero usize  := ⟨usize.of_nat 0⟩
instance : has_one usize   := ⟨usize.of_nat 1⟩
instance : has_add usize   := ⟨fin.add⟩
instance : has_sub usize   := ⟨fin.sub⟩
instance : has_mul usize   := ⟨fin.mul⟩
instance : has_mod usize   := ⟨fin.mod⟩
instance : has_modn usize  := ⟨fin.modn⟩
instance : has_div usize   := ⟨fin.div⟩
instance : has_lt usize    := ⟨fin.lt⟩
instance : has_le usize    := ⟨fin.le⟩
instance : inhabited usize := ⟨0⟩
