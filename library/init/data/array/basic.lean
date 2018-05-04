/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.usize init.data.repr init.function
universes u v w

/-
The compiler has special support for arrays.
They are implemented as a dynamic array.
-/

structure array (α : Type u) :=
(sz   : nat)
(data : fin sz → α)

/- TODO: mark as builtin -/
def mk_array {α : Type u} (n : nat) (v : α) : array α :=
{ sz   := n,
  data := λ _, v}

theorem sz_mk_array_eq {α : Type u} (n : nat) (v : α) : (mk_array n v).sz = n :=
rfl

namespace array
variables {α : Type u} {β : Type v}

/- TODO: mark as builtin -/
def nil : array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x) }

def empty (a : array α) : bool :=
a.sz = 0

/- TODO: mark as builtin -/
def read (a : array α) (i : fin a.sz) : α :=
a.data i

/- TODO: mark as builtin -/
def write (a : array α) (i : fin a.sz) (v : α) : array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

theorem sz_write_eq (a : array α) (i : fin a.sz) (v : α) : (write a i v).sz = a.sz :=
rfl

/- TODO: add builtin -/
def read' [inhabited α] (a : array α) (i : nat) : α :=
if h : i < a.sz then a.read ⟨i, h⟩ else default α

/- TODO: add builtin -/
def write' (a : array α) (i : nat) (v : α) : array α :=
if h : i < a.sz then a.write ⟨i, h⟩ v else a

/- TODO: add builtin -/
def uread (a : array α) (i : usize) (h : i.val < a.sz) : α :=
a.read ⟨i.val, h⟩

/- TODO: add builtin -/
def uwrite (a : array α) (i : usize) (v : α) (h : i.val < a.sz) : array α :=
a.write ⟨i.val, h⟩ v

/- TODO: add builtin -/
def uread' [inhabited α] (a : array α) (i : usize) : α :=
if h : i.val < a.sz then a.read ⟨i.val, h⟩ else default α

/- TODO: add builtin -/
def uwrite' (a : array α) (i : usize) (v : α) : array α :=
if h : i.val < a.sz then a.write ⟨i.val, h⟩ v else a

/- TODO: mark as builtin -/
def push (a : array α) (v : α) : array α :=
{ sz   := nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, nat.lt_of_le_of_ne (nat.le_of_lt_succ h₁) h₂⟩ }

/- TODO: mark as builtin -/
def pop (a : array α) : array α :=
{ sz   := nat.pred a.sz,
  data := λ ⟨j, h⟩, a.read ⟨j, nat.lt_of_lt_of_le h (nat.pred_le _)⟩ }

private def iterate_aux (a : array α) (f : Π i : fin a.sz, α → β → β) : Π (i : nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin a.sz := ⟨j, h⟩ in
  f i (a.read i) (iterate_aux j (nat.le_of_lt h) b)

/- TODO : mark as builtin -/
def iterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
iterate_aux a f a.sz (nat.le_refl _) b

def foldl (a : array α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

private def rev_iterate_aux (a : array α) (f : Π i : fin a.sz, α → β → β) : Π (i : nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin a.sz := ⟨j, h⟩ in
  rev_iterate_aux j (nat.le_of_lt h) (f i (a.read i) b)

/- TODO: mark as builtin -/
def rev_iterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
rev_iterate_aux a f a.sz (nat.le_refl _) b

def rev_foldl (a : array α) (b : β) (f : α → β → β) : β :=
rev_iterate a b (λ _, f)

def to_list (a : array α) : list α :=
a.rev_foldl [] (::)

instance [has_repr α] : has_repr (array α) :=
⟨repr ∘ to_list⟩

private def foreach_aux (a : array α) (f : Π i : fin a.sz, α → α) : { a' : array α // a'.sz = a.sz } :=
iterate a ⟨a, rfl⟩ $ λ i v ⟨a', h⟩,
  let i' : fin a'.sz := eq.rec_on h.symm i in
  ⟨a'.write i' (f i v), (sz_write_eq a' i' (f i v)) ▸ h⟩

/- TODO : mark as builtin -/
def foreach (a : array α) (f : Π i : fin a.sz, α → α) : array α :=
(foreach_aux a f).val

theorem sz_foreach_eq (a : array α) (f : Π i : fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(foreach_aux a f).property

def map (f : α → α) (a : array α) : array α :=
foreach a (λ _, f)

def map₂ (f : α → α → α) (a b : array α) : array α :=
if h : a.sz ≤ b.sz
then foreach a (λ ⟨i, h'⟩, f (b.read ⟨i, nat.lt_of_lt_of_le h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.read ⟨i, nat.lt_trans h' (nat.gt_of_not_le h)⟩))

end array

def list.to_array_aux {α : Type u} : list α → array α → array α
| []      r := r
| (a::as) r := list.to_array_aux as (r.push a)

def list.to_array {α : Type u} (l : list α) : array α :=
l.to_array_aux array.nil
