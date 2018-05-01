/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array.basic init.meta
universes u v w

namespace d_array
variables {n : nat} {α : fin n → Type u} {β : Type v}

@[simp] theorem read_write (a : d_array n α) (i : fin n) (v : α i) : read (write a i v) i = v :=
by simp [read, write]

@[simp] theorem read_write_of_ne (a : d_array n α) {i j : fin n} (v : α i) : i ≠ j → read (write a i v) j = read a j :=
by intro h; simp [read, write, h]

protected theorem ext {a b : d_array n α} (h : ∀ i, read a i = read b i) : a = b :=
by cases a; cases b; congr; exact funext h

protected theorem ext' {a b : d_array n α} (h : ∀ (i : nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
begin cases a, cases b, congr, funext i, cases i, apply h end

end d_array

namespace array
variables {n : nat} {α : Type u} {β : Type v}

theorem read_mem (a : array n α) (i) : read a i ∈ a :=
exists.intro i rfl

@[simp] theorem read_write (a : array n α) (i : fin n) (v : α) : read (write a i v) i = v :=
d_array.read_write a i v

@[simp] theorem read_write_of_ne (a : array n α) {i j : fin n} (v : α) : i ≠ j → read (write a i v) j = read a j :=
d_array.read_write_of_ne a v

theorem read_eq_read' [inhabited α] (a : array n α) {i : nat} (h : i < n) : read a ⟨i, h⟩ = read' a i :=
by simp [read', h]

theorem write_eq_write' (a : array n α) {i : nat} (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v :=
by simp [write', h]

protected theorem ext {a b : array n α} (h : ∀ i, read a i = read b i) : a = b :=
d_array.ext h

protected theorem ext' {a b : array n α} (h : ∀ (i : nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
d_array.ext' h

end array
