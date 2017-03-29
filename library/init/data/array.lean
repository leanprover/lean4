/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat
universes u w

structure array (α : Type u) (n : nat) :=
(data : fin n → α)

def mk_array {α} (n) (v : α) : array α n :=
{data := λ _, v}

namespace array
variables {α : Type u} {β : Type w} {n : nat}

def read (a : array α n) (i : fin n) : α :=
a.data i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
if h : i < n then a.read ⟨i,h⟩ else default α

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := λ j, if i = j then v else a.read j}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
if h : i < n then a.write ⟨i, h⟩ v else a

lemma push_back_idx {j n} : j < n + 1 → j ≠ n → j < n :=
λ h₁ h₂, nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} : j < n → j < n + 1 :=
λ h, nat.lt.step h

def pop_back (a : array α (n+1)) : array α n :=
{data := λ ⟨j, h⟩, a.read ⟨j, pop_back_idx h⟩}

lemma lt_aux_1 {a b c : nat} : a + c < b → a < b :=
λ h, lt_of_le_of_lt (nat.le_add_right a c) h

lemma lt_aux_2 {n} : n > 0 → n - 1 < n :=
assume h,
  have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma lt_aux_3 {n i} : i + 1 < n → n - 2 - i < n  :=
assume h,
have n > 0,     from lt.trans (nat.zero_lt_succ i) h,
have n - 2 < n, from nat.sub_lt this (dec_trivial),
lt_of_le_of_lt (nat.sub_le _ _) this

def foreach_aux (f : fin n → α → α) : Π (i : nat), i < n → array α n → array α n
| 0     h a :=
  let i : fin n := ⟨n - 1, lt_aux_2 h⟩ in
  a.write i (f i (a.read i))
| (j+1) h a :=
  let i : fin n := ⟨n - 2 - j, lt_aux_3 h⟩ in
  foreach_aux j (lt_aux_1 h) (a.write i (f i (a.read i)))

def foreach : Π {n}, array α n → (fin n → α → α) → array α n
| 0     a f:= a
| (n+1) a f := foreach_aux f n  (nat.lt_succ_self _) a

def map {α} {n} (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ {α} {n} (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a.read i))

def iterate_aux (f : fin n → α → β → β) : Π (i : nat), i < n → array α n → β → β
| 0     h a b :=
  let i : fin n := ⟨n - 1, lt_aux_2 h⟩ in
  f i (a.read i) b
| (j+1) h a b :=
  let i : fin n := ⟨n - 2 - j, lt_aux_3 h⟩ in
  iterate_aux j (lt_aux_1 h) a (f i (a.read i) b)

def iterate : Π {n}, array α n → β → (fin n → α → β → β) → β
| 0     a b fn := b
| (n+1) a b fn := iterate_aux fn n (nat.lt_succ_self _) a b

def foldl {n} (a : array α n) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_iterate_aux (f : fin n → α → β → β) : Π (i : nat), i < n → array α n → β → β
| 0 h a b :=
  let z : fin n := ⟨0, h⟩ in
  f z (a.read z) b
| (j+1) h a b :=
  let i : fin n := ⟨j+1, h⟩ in
  rev_iterate_aux j (lt_aux_1 h) a (f i (a.read i) b)

def rev_iterate : Π {n : nat}, array α n → β → (fin n → α → β → β) → β
| 0     a b fn := b
| (n+1) a b fn := rev_iterate_aux fn n (nat.lt_succ_self _) a b

def to_list (a : array α n) : list α :=
a.rev_iterate [] (λ _ v l, v :: l)

instance [has_to_string α] : has_to_string (array α n) :=
⟨to_string ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array α n) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array α n) :=
⟨tactic.pp ∘ to_list⟩

end array
