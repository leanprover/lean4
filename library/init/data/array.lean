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
a^.data i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
if h : i < n then a^.read ⟨i,h⟩ else default α

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := λ j, if i = j then v else a^.read j}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
if h : i < n then a^.write ⟨i, h⟩ v else a

lemma push_back_idx {j n} : j < n + 1 → j ≠ n → j < n :=
λ h₁ h₂, nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a^.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} : j < n → j < n + 1 :=
λ h, nat.lt.step h

def pop_back (a : array α (n+1)) : array α n :=
{data := λ ⟨j, h⟩, a^.read ⟨j, pop_back_idx h⟩}

lemma foreach_lt {a b c : nat} : a + c < b → a < b :=
λ h, lt_of_le_of_lt (nat.le_add_right a c) h

def foreach_aux (f : fin n → α → α) : Π (i : nat), i < n → array α n → array α n
| 0     h a :=
  let z : fin n := ⟨0, h⟩ in
  a^.write z (f z (a^.read z))
| (j+1) h a :=
  let i : fin n := ⟨j+1, h⟩ in
  have h' : j < n, from foreach_lt h,
  foreach_aux j h' (a^.write i (f i (a^.read i)))

def foreach : Π {n}, array α n → (fin n → α → α) → array α n
| 0     a f:= a
| (n+1) a f := foreach_aux f n  (nat.lt_succ_self _) a

def map {α} {n} (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ {α} {n} (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a^.read i))

lemma fold_lt₁ {n} : n > 0 → n - 1 < n :=
assume h,
  have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma fold_lt₂ {n i} : i + 1 < n → n - 2 - i < n  :=
assume h,
  have h₁ : 2 > 0,             from dec_trivial,
  have h₂ : n > 0,             from lt.trans (nat.zero_lt_succ i) h,
  have h₃ : n - 2 < n,         from nat.sub_lt h₂ h₁,
  have h₄ : n - 2 - i ≤ n - 2, from nat.sub_le _ _,
lt_of_le_of_lt h₄ h₃

def fold_aux (f : α → β → β) : Π (i : nat), i < n → array α n → β → β
| 0     h a b := f (a^.read ⟨n - 1, fold_lt₁ h⟩) b
| (i+1) h a b := fold_aux i (foreach_lt h) a (f (a^.read ⟨n - 2 - i, fold_lt₂ h⟩) b)

def fold : Π {n}, array α n → β → (α → β → β) → β
| 0     a b fn := b
| (n+1) a b fn := fold_aux fn n (nat.lt_succ_self _) a b

protected def to_string [has_to_string α] (a : array α n) : string :=
let p : string × bool := a^.fold ("", tt) (λ v ⟨r, first⟩, (r ++ if first then to_string v else ", " ++ to_string v, ff))
in "[" ++ p.1 ++ "]"

instance [has_to_string α] : has_to_string (array α n) :=
⟨array.to_string⟩

end array
