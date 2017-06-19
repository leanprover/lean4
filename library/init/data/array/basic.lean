/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
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

def nil {α} : array α 0 :=
{data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x)}

def read (a : array α n) (i : fin n) : α :=
a.data i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
if h : i < n then a.read ⟨i,h⟩ else default α

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := λ j, if i = j then v else a.read j}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
if h : i < n then a.write ⟨i, h⟩ v else a

lemma push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} (h : j < n) : j < n + 1 :=
nat.lt.step h

def pop_back (a : array α (n+1)) : array α n :=
{data := λ ⟨j, h⟩, a.read ⟨j, pop_back_idx h⟩}

lemma lt_aux_1 {a b c : nat} (h : a + c < b) : a < b :=
lt_of_le_of_lt (nat.le_add_right a c) h

lemma lt_aux_2 {n} (h : n > 0) : n - 1 < n :=
have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n  :=
have n > 0,     from lt.trans (nat.zero_lt_succ i) h,
have n - 2 < n, from nat.sub_lt this (dec_trivial),
lt_of_le_of_lt (nat.sub_le _ _) this

@[elab_as_eliminator]
theorem write_ind (a : array α n) (i : fin n) (v : α) (C : fin n → α → Sort w)
  (Hi : C i v) (Hj : ∀j, i ≠ j → C j (a.read j)) (j) : C j ((a.write i v).read j) :=
show C j (if i = j then v else read a j), from
if h : i = j then by rwa [if_pos h, -h]
else by rw [if_neg h]; exact Hj j h

def foreach_aux (f : fin n → α → α) : Π (i : nat), i ≤ n → array α n → array α n
| 0     h a := a
| (j+1) h a :=
  let i : fin n := ⟨n - 1 - j, nat.sub_one_sub_lt h⟩ in
  foreach_aux j (le_of_lt h) (a.write i (f i (a.read i)))

def foreach (a : array α n) (f : fin n → α → α) : array α n :=
foreach_aux f n (le_refl _) a

def map (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a.read i))

def iterate_aux (a : array α n) (f : fin n → α → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  f i (a.read i) (iterate_aux j (le_of_lt h) b)

def iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
iterate_aux a fn n (le_refl _) b

def foldl (a : array α n) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_list (a : array α n) : list α :=
a.foldl [] (λ v l, v :: l)

def foldl_eq_aux (a : array α n) (b : β) (f : α → β → β) :
  Π (i : nat) (h : i ≤ n), iterate_aux a (λ _, f) i h b = (iterate_aux a (λ _ v l, v :: l) i h []).foldr f b
| 0     h := rfl
| (j+1) h := congr_arg (f (read a ⟨j, h⟩)) (foldl_eq_aux j _)

def foldl_eq (a : array α n) (b : β) (f : α → β → β) : a.foldl b f = a.rev_list.foldr f b :=
foldl_eq_aux a b f _ _

def rev_iterate_aux (a : array α n) (f : fin n → α → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  rev_iterate_aux j (le_of_lt h) (f i (a.read i) b)

def rev_iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
rev_iterate_aux a fn n (le_refl _) b

def to_list (a : array α n) : list α :=
a.rev_iterate [] (λ _ v l, v :: l)

protected def mem (v : α) (a : array α n) : Prop := ∃i, read a i = v

instance : has_mem α (array α n) := ⟨array.mem⟩

theorem read_mem (a : array α n) (i) : read a i ∈ a := exists.intro i rfl

instance [has_repr α] : has_repr (array α n) :=
⟨repr ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array α n) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array α n) :=
⟨tactic.pp ∘ to_list⟩

end array

def list.to_array {α} (l : list α) : array α l.length :=
{data := λ v, l.nth_le v.1 v.2}
