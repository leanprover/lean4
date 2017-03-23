/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universes u w

def buffer (α : Type u) := Σ n, array α n

def mk_buffer {α : Type u} : buffer α :=
⟨0, {data := λ i, fin.elim0 i}⟩

def array.to_buffer {α : Type u} {n : nat} (a : array α n) : buffer α :=
⟨n, a⟩

namespace buffer
variables {α : Type u} {β : Type w}

def nil : buffer α :=
mk_buffer

def size (b : buffer α) : nat :=
b.1

def to_array (b : buffer α) : array α (b^.size) :=
b.2

def push_back : buffer α → α → buffer α
| ⟨n, a⟩ v := ⟨n+1, a^.push_back v⟩

def pop_back : buffer α → buffer α
| ⟨0, a⟩   := ⟨0, a⟩
| ⟨n+1, a⟩ := ⟨n, a^.pop_back⟩

def read : Π (b : buffer α), fin b^.size → α
| ⟨n, a⟩ i := a^.read i

def write : Π (b : buffer α), fin b^.size → α → buffer α
| ⟨n, a⟩ i v := ⟨n, a^.write i v⟩

def read' [inhabited α] : buffer α → nat → α
| ⟨n, a⟩ i := a^.read' i

def write' : buffer α → nat → α → buffer α
| ⟨n, a⟩ i v := ⟨n, a^.write' i v⟩

def to_list (b : buffer α) : list α :=
b^.to_array^.to_list

def append_list {α : Type u} : buffer α → list α → buffer α
| b []      := b
| b (v::vs) := append_list (b^.push_back v) vs

def append_string (b : buffer char) (s : string) : buffer char :=
b^.append_list s^.reverse

def append_array {α : Type u} {n : nat} (nz : n > 0) : buffer α → array α n → ∀ i : nat, i < n → buffer α
| ⟨m, b⟩ a 0     _ :=
  let i : fin n := ⟨n - 1, array.lt_aux_2 nz⟩ in
  ⟨m+1, b^.push_back (a^.read i)⟩
| ⟨m, b⟩ a (j+1) h :=
  let i : fin n := ⟨n - 2 - j, array.lt_aux_3 h⟩ in
  append_array ⟨m+1, b^.push_back (a^.read i)⟩ a j (array.lt_aux_1 h)

protected def append {α : Type u} : buffer α → buffer α → buffer α
| b ⟨0, a⟩   := b
| b ⟨n+1, a⟩ := append_array (nat.zero_lt_succ _) b a n (nat.lt_succ_self _)

def iterate : Π b : buffer α, β → (fin b^.size → α → β → β) → β
| ⟨_, a⟩ b f := a^.iterate b f

def foreach : Π b : buffer α, (fin b^.size → α → α) → buffer α
| ⟨n, a⟩ f := ⟨n, a^.foreach f⟩

def map (f : α → α) : buffer α → buffer α
| ⟨n, a⟩ := ⟨n, a^.map f⟩

def foldl : buffer α → β → (α → β → β) → β
| ⟨_, a⟩ b f := a^.foldl b f

def rev_iterate : Π (b : buffer α), β → (fin b^.size → α → β → β) → β
| ⟨_, a⟩ b f := a^.rev_iterate b f

instance : has_append (buffer α) :=
⟨buffer.append⟩

instance [has_to_string α] : has_to_string (buffer α) :=
⟨to_string ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (buffer α) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (buffer α) :=
⟨tactic.pp ∘ to_list⟩

end buffer

def list.to_buffer {α : Type u} (l : list α) : buffer α :=
mk_buffer^.append_list l

@[reducible] def char_buffer := buffer char
