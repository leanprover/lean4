/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import init.data.nat.basic init.data.fin.basic
universes u v w

/- In the VM, d_array is implemented a persistent array. -/
structure d_array (n : nat) (α : fin n → Type u) :=
(data : Π i : fin n, α i)

namespace d_array
variables {n : nat} {α : fin n → Type u} {β : Type v}

def nil {α} : d_array 0 α :=
{data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x)}

/- has builtin VM implementation -/
def read (a : d_array n α) (i : fin n) : α i :=
a.data i

/- has builtin VM implementation -/
def write (a : d_array n α) (i : fin n) (v : α i) : d_array n α :=
{data := λ j, if h : i = j then eq.rec_on h v else a.read j}

def iterate_aux (a : d_array n α) (f : Π i : fin n, α i → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  f i (a.read i) (iterate_aux j (nat.le_of_lt h) b)

/- has builtin VM implementation -/
def iterate (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
iterate_aux a f n (nat.le_refl _) b

/- has builtin VM implementation -/
def foreach (a : d_array n α) (f : Π i : fin n, α i → α i) : d_array n α :=
iterate a a $ λ i v a', a'.write i (f i v)

def map (f : Π i : fin n, α i → α i) (a : d_array n α) : d_array n α :=
foreach a f

def map₂ (f : Π i : fin n, α i → α i → α i) (a b : d_array n α) : d_array n α :=
foreach b (λ i, f i (a.read i))

def foldl (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
iterate a b f

def rev_iterate_aux (a : d_array n α) (f : Π i : fin n, α i → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  rev_iterate_aux j (nat.le_of_lt h) (f i (a.read i) b)

def rev_iterate (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
rev_iterate_aux a f n (nat.le_refl _) b

end d_array

def array (n : nat) (α : Type u) : Type u :=
d_array n (λ _, α)

/- has builtin VM implementation -/
def mk_array {α} (n) (v : α) : array n α :=
{data := λ _, v}

namespace array
variables {n : nat} {α : Type u} {β : Type v}

def nil {α} : array 0 α :=
d_array.nil

def read (a : array n α) (i : fin n) : α :=
d_array.read a i

def write (a : array n α) (i : fin n) (v : α) : array n α :=
d_array.write a i v

def iterate (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
d_array.iterate a b f

def foreach (a : array n α) (f : fin n → α → α) : array n α :=
iterate a a (λ i v a', a'.write i (f i v))

def map (f : α → α) (a : array n α) : array n α :=
foreach a (λ _, f)

def map₂ (f : α → α → α) (a b : array n α) : array n α :=
foreach b (λ i, f (a.read i))

def foldl (a : array n α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_list (a : array n α) : list α :=
a.foldl [] (::)

def rev_iterate (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
d_array.rev_iterate a b f

def rev_foldl (a : array n α) (b : β) (f : α → β → β) : β :=
rev_iterate a b (λ _, f)

def to_list (a : array n α) : list α :=
a.rev_foldl [] (::)

theorem push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
nat.lt_of_le_of_ne (nat.le_of_lt_succ h₁) h₂

/- has builtin VM implementation -/
def push_back (a : array n α) (v : α) : array (n+1) α :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩}

theorem pop_back_idx {j n} (h : j < n) : j < n + 1 :=
nat.lt.step h

/- has builtin VM implementation -/
def pop_back (a : array (n+1) α) : array n α :=
{data := λ ⟨j, h⟩, a.read ⟨j, pop_back_idx h⟩}

protected def mem (v : α) (a : array n α) : Prop :=
∃ i : fin n, read a i = v

instance : has_mem α (array n α) := ⟨array.mem⟩

def read' [inhabited β] (a : array n β) (i : nat) : β :=
if h : i < n then a.read ⟨i,h⟩ else default β

def write' (a : array n α) (i : nat) (v : α) : array n α :=
if h : i < n then a.write ⟨i, h⟩ v else a

end array
