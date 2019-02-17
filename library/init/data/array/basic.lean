/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.fin.basic init.data.usize init.data.repr init.function
import init.data.to_string
universes u v w

/-
The compiler has special support for arrays.
They are implemented as a dynamic array.
-/

-- TODO(Leo): mark as opaque
structure array (α : Type u) :=
(sz   : nat)
(data : fin sz → α)

attribute [extern cpp inline "lean::array_sz(#2)"] array.sz

@[extern cpp inline "lean::array_get_size(#2)"]
def array.size {α : Type u} (a : @& array α) : nat :=
a.sz

@[extern cpp inline "lean::mk_array(#2, #3)"]
def mk_array {α : Type u} (n : nat) (v : α) : array α :=
{ sz   := n,
  data := λ _, v}

theorem sz_mk_array_eq {α : Type u} (n : nat) (v : α) : (mk_array n v).sz = n :=
rfl

namespace array
variables {α : Type u} {β : Type v}

@[extern cpp inline "lean::mk_nil_array()"]
def mk_nil (_ : unit) : array α :=
{ sz   := 0,
  data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x) }

def nil : array α :=
mk_nil ()

def empty (a : array α) : bool :=
a.size = 0

@[extern cpp inline "lean::array_read(#2, #3)"]
def read (a : @& array α) (i : @& fin a.sz) : α :=
a.data i

@[extern cpp inline "lean::array_write(#2, #3, #4)"]
def write (a : array α) (i : @& fin a.sz) (v : α) : array α :=
{ sz   := a.sz,
  data := λ j, if h : i = j then v else a.data j }

theorem sz_write_eq (a : array α) (i : fin a.sz) (v : α) : (write a i v).sz = a.sz :=
rfl

@[extern cpp inline "lean::array_safe_read(#2, #3, #4)"]
def read' [inhabited α] (a : @& array α) (i : @& nat) : α :=
if h : i < a.sz then a.read ⟨i, h⟩ else default α

@[extern cpp inline "lean::array_safe_write(#2, #3, #4)"]
def write' (a : array α) (i : @& nat) (v : α) : array α :=
if h : i < a.sz then a.write ⟨i, h⟩ v else a

@[extern cpp inline "lean::array_uread(#2, #3)"]
def uread (a : @& array α) (i : usize) (h : i.to_nat < a.sz) : α :=
a.read ⟨i.to_nat, h⟩

@[extern cpp inline "lean::array_uwrite(#2, #3, #4)"]
def uwrite (a : @& array α) (i : usize) (v : @& α) (h : i.to_nat < a.sz) : array α :=
a.write ⟨i.to_nat, h⟩ v

@[extern cpp inline "lean::array_safe_uread(#2, #3, #4)"]
def uread' [inhabited α] (a : array α) (i : usize) : α :=
if h : i.to_nat < a.sz then a.read ⟨i.to_nat, h⟩ else default α

@[extern cpp inline "lean::array_safe_uwrite(#2, #3, #4)"]
def uwrite' (a : array α) (i : usize) (v : α) : array α :=
if h : i.to_nat < a.sz then a.write ⟨i.to_nat, h⟩ v else a

@[extern cpp inline "lean::array_push(#2, #3)"]
def push (a : array α) (v : α) : array α :=
{ sz   := nat.succ a.sz,
  data := λ ⟨j, h₁⟩,
    if h₂ : j = a.sz then v
    else a.data ⟨j, nat.lt_of_le_of_ne (nat.le_of_lt_succ h₁) h₂⟩ }

@[extern cpp inline "lean::array_pop(#2)"]
def pop (a : array α) : array α :=
{ sz   := nat.pred a.sz,
  data := λ ⟨j, h⟩, a.read ⟨j, nat.lt_of_lt_of_le h (nat.pred_le _)⟩ }

-- TODO(Leo): justify termination using wf-rec
@[specialize] private def iterate_aux (a : array α) (f : Π i : fin a.sz, α → β → β) : nat → β → β
| i b :=
  if h : i < a.sz then
     let idx : fin a.sz := ⟨i, h⟩ in
     iterate_aux (i+1) (f idx (a.read idx) b)
  else b

@[inline] def iterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
iterate_aux a f 0 b

@[inline] def foldl (a : array α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

@[specialize] private def rev_iterate_aux (a : array α) (f : Π i : fin a.sz, α → β → β) : Π (i : nat), i ≤ a.sz → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin a.sz := ⟨j, h⟩ in
  rev_iterate_aux j (nat.le_of_lt h) (f i (a.read i) b)

@[inline] def rev_iterate (a : array α) (b : β) (f : Π i : fin a.sz, α → β → β) : β :=
rev_iterate_aux a f a.size (nat.le_refl _) b

@[inline] def rev_foldl (a : array α) (b : β) (f : α → β → β) : β :=
rev_iterate a b (λ _, f)

def to_list (a : array α) : list α :=
a.rev_foldl [] (::)

instance [has_repr α] : has_repr (array α) :=
⟨repr ∘ to_list⟩

instance [has_to_string α] : has_to_string (array α) :=
⟨to_string ∘ to_list⟩

@[inline] private def foreach_aux (a : array α) (f : Π i : fin a.sz, α → α) : { a' : array α // a'.sz = a.sz } :=
iterate a ⟨a, rfl⟩ $ λ i v ⟨a', h⟩,
  let i' : fin a'.sz := eq.rec_on h.symm i in
  ⟨a'.write i' (f i v), (sz_write_eq a' i' (f i v)) ▸ h⟩

@[inline] def foreach (a : array α) (f : Π i : fin a.sz, α → α) : array α :=
(foreach_aux a f).val

theorem sz_foreach_eq (a : array α) (f : Π i : fin a.sz, α → α) : (foreach a f).sz = a.sz :=
(foreach_aux a f).property

@[inline] def map (f : α → α) (a : array α) : array α :=
foreach a (λ _, f)

@[inline] def map₂ (f : α → α → α) (a b : array α) : array α :=
if h : a.size ≤ b.size
then foreach a (λ ⟨i, h'⟩, f (b.read ⟨i, nat.lt_of_lt_of_le h' h⟩))
else foreach b (λ ⟨i, h'⟩, f (a.read ⟨i, nat.lt_trans h' (nat.gt_of_not_le h)⟩))

end array

def list.to_array_aux {α : Type u} : list α → array α → array α
| []      r := r
| (a::as) r := list.to_array_aux as (r.push a)

def list.to_array {α : Type u} (l : list α) : array α :=
l.to_array_aux array.nil
