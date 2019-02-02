/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.platform init.data.fin

def usize_sz : nat := (2:nat) ^ system.platform.nbits
structure usize :=
(val : fin usize_sz)

def usize.of_nat (n : nat) : usize := ⟨fin.of_nat n⟩
def usize.to_nat (n : usize) : nat := n.val.val
def usize.add (a b : usize) : usize := ⟨a.val + b.val⟩
def usize.sub (a b : usize) : usize := ⟨a.val - b.val⟩
def usize.mul (a b : usize) : usize := ⟨a.val * b.val⟩
def usize.div (a b : usize) : usize := ⟨a.val / b.val⟩
def usize.mod (a b : usize) : usize := ⟨a.val % b.val⟩
def usize.modn (a : usize) (n : nat) : usize := ⟨a.val %ₙ n⟩
def usize.lt (a b : usize) : Prop := a.val < b.val
def usize.le (a b : usize) : Prop := a.val ≤ b.val

instance : has_zero usize     := ⟨usize.of_nat 0⟩
instance : has_one usize      := ⟨usize.of_nat 1⟩
instance : has_add usize      := ⟨usize.add⟩
instance : has_sub usize      := ⟨usize.sub⟩
instance : has_mul usize      := ⟨usize.mul⟩
instance : has_mod usize      := ⟨usize.mod⟩
instance : has_modn usize     := ⟨usize.modn⟩
instance : has_div usize      := ⟨usize.div⟩
instance : has_lt usize       := ⟨usize.lt⟩
instance : has_le usize       := ⟨usize.le⟩
instance : inhabited usize    := ⟨0⟩

def usize.dec_eq (a b : usize) : decidable (a = b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', usize.no_confusion h' (λ h', absurd h' h))

def usize.dec_lt (a b : usize) : decidable (a < b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

def usize.dec_le (a b : usize) : decidable (a ≤ b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq usize := {dec_eq := usize.dec_eq}
instance usize.has_decidable_lt (a b : usize) : decidable (a < b) := usize.dec_lt a b
instance usize.has_decidable_le (a b : usize) : decidable (a ≤ b) := usize.dec_le a b

theorem usize.modn_lt {m : nat} : ∀ (u : usize), m > 0 → usize.to_nat (u %ₙ m) < m
| ⟨u⟩ h := fin.modn_lt u h
