/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universes u w

def buffer (α : Type u) := Σ n, array n α

def mk_buffer {α : Type u} : buffer α :=
⟨0, {data := λ i, fin.elim0 i}⟩

def array.to_buffer {α : Type u} {n : nat} (a : array n α) : buffer α :=
⟨n, a⟩

namespace buffer
variables {α : Type u} {β : Type w}

def nil : buffer α :=
mk_buffer

def size (b : buffer α) : nat :=
b.1

def to_array (b : buffer α) : array (b.size) α :=
b.2

def push_back : buffer α → α → buffer α
| ⟨n, a⟩ v := ⟨n+1, a.push_back v⟩

def pop_back : buffer α → buffer α
| ⟨0, a⟩   := ⟨0, a⟩
| ⟨n+1, a⟩ := ⟨n, a.pop_back⟩

def read : Π (b : buffer α), fin b.size → α
| ⟨n, a⟩ i := a.read i

def write : Π (b : buffer α), fin b.size → α → buffer α
| ⟨n, a⟩ i v := ⟨n, a.write i v⟩

def read' [inhabited α] : buffer α → nat → α
| ⟨n, a⟩ i := a.read' i

def write' : buffer α → nat → α → buffer α
| ⟨n, a⟩ i v := ⟨n, a.write' i v⟩

lemma read_eq_read' [inhabited α] (b : buffer α) (i : nat) (h : i < b.size) : read b ⟨i, h⟩ = read' b i :=
by cases b; unfold read read'; simp [array.read_eq_read']

lemma write_eq_write' (b : buffer α) (i : nat) (h : i < b.size) (v : α) : write b ⟨i, h⟩ v = write' b i v :=
by cases b; unfold write write'; simp [array.write_eq_write']

def to_list (b : buffer α) : list α :=
b.to_array.to_list

protected def to_string (b : buffer char) : string :=
b.to_array.to_list.as_string

def append_list {α : Type u} : buffer α → list α → buffer α
| b []      := b
| b (v::vs) := append_list (b.push_back v) vs

def append_string (b : buffer char) (s : string) : buffer char :=
b.append_list s.to_list

lemma lt_aux_1 {a b c : nat} (h : a + c < b) : a < b :=
lt_of_le_of_lt (nat.le_add_right a c) h

lemma lt_aux_2 {n} (h : n > 0) : n - 1 < n :=
have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n  :=
have n > 0,     from lt.trans (nat.zero_lt_succ i) h,
have n - 2 < n, from nat.sub_lt this (dec_trivial),
lt_of_le_of_lt (nat.sub_le _ _) this

def append_array {α : Type u} {n : nat} (nz : n > 0) : buffer α → array n α → ∀ i : nat, i < n → buffer α
| ⟨m, b⟩ a 0     _ :=
  let i : fin n := ⟨n - 1, lt_aux_2 nz⟩ in
  ⟨m+1, b.push_back (a.read i)⟩
| ⟨m, b⟩ a (j+1) h :=
  let i : fin n := ⟨n - 2 - j, lt_aux_3 h⟩ in
  append_array ⟨m+1, b.push_back (a.read i)⟩ a j (lt_aux_1 h)

protected def append {α : Type u} : buffer α → buffer α → buffer α
| b ⟨0, a⟩   := b
| b ⟨n+1, a⟩ := append_array (nat.zero_lt_succ _) b a n (nat.lt_succ_self _)

def iterate : Π b : buffer α, β → (fin b.size → α → β → β) → β
| ⟨_, a⟩ b f := a.iterate b f

def foreach : Π b : buffer α, (fin b.size → α → α) → buffer α
| ⟨n, a⟩ f := ⟨n, a.foreach f⟩

def map (f : α → α) : buffer α → buffer α
| ⟨n, a⟩ := ⟨n, a.map f⟩

def foldl : buffer α → β → (α → β → β) → β
| ⟨_, a⟩ b f := a.foldl b f

def rev_iterate : Π (b : buffer α), β → (fin b.size → α → β → β) → β
| ⟨_, a⟩ b f := a.rev_iterate b f

def take (b : buffer α) (n : nat) : buffer α :=
if h : n ≤ b.size then ⟨n, b.to_array.take n h⟩ else b

def take_right (b : buffer α) (n : nat) : buffer α :=
if h : n ≤ b.size then ⟨n, b.to_array.take_right n h⟩ else b

def drop (b : buffer α) (n : nat) : buffer α :=
if h : n ≤ b.size then ⟨_, b.to_array.drop n h⟩ else b

def reverse (b : buffer α) : buffer α :=
⟨b.size, b.to_array.reverse⟩

protected def mem (v : α) (a : buffer α) : Prop := ∃i, read a i = v

instance : has_mem α (buffer α) := ⟨buffer.mem⟩

instance : has_append (buffer α) :=
⟨buffer.append⟩

instance [has_repr α] : has_repr (buffer α) :=
⟨repr ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (buffer α) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (buffer α) :=
⟨tactic.pp ∘ to_list⟩

end buffer

def list.to_buffer {α : Type u} (l : list α) : buffer α :=
mk_buffer.append_list l

@[reducible] def char_buffer := buffer char

/-- Convert a format object into a character buffer with the provided
    formatting options. -/
meta constant format.to_buffer : format → options → buffer char

def string.to_char_buffer (s : string) : char_buffer :=
buffer.nil.append_string s
