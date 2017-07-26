/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
prelude
import init.data.list init.data.subtype init.meta.interactive init.data.fin

universes u v w

def vector (α : Type u) (n : ℕ) := { l : list α // l.length = n }

namespace vector
variables {α : Type u} {β : Type v} {φ : Type w}
variable {n : ℕ}

instance [decidable_eq α] : decidable_eq (vector α n) :=
begin unfold vector, apply_instance end

@[pattern] def nil : vector α 0 := ⟨[],  rfl⟩

@[pattern] def cons : α → vector α n → vector α (nat.succ n)
| a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

@[reducible] def length (v : vector α n) : ℕ := n

notation a :: b := cons a b

open nat

def head : vector α (nat.succ n) → α
| ⟨ [],    h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := a

theorem head_cons (a : α) : Π (v : vector α n), head (a :: v) = a
| ⟨ l, h ⟩ := rfl

def tail : vector α n → vector α (n - 1)
| ⟨ [],     h ⟩ := ⟨ [], congr_arg pred h ⟩
| ⟨ a :: v, h ⟩ := ⟨ v, congr_arg pred h ⟩

theorem tail_cons (a : α) : Π (v : vector α n), tail (a :: v) = v
| ⟨ l, h ⟩ := rfl

@[simp] theorem cons_head_tail : ∀ v : vector α (succ n), (head v :: tail v) = v
| ⟨ [],     h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := rfl

def to_list (v : vector α n) : list α := v.1

def nth : Π (v : vector α n), fin n → α | ⟨ l, h ⟩ i := l.nth_le i.1 (by rw h; exact i.2)

def append {n m : nat} : vector α n → vector α m → vector α (n + m)
| ⟨ l₁, h₁ ⟩ ⟨ l₂, h₂ ⟩ := ⟨ l₁ ++ l₂, by simp * ⟩

@[elab_as_eliminator] def elim {α} {C : Π {n}, vector α n → Sort u} (H : ∀l : list α, C ⟨l, rfl⟩)
  {n : nat} : Π (v : vector α n), C v
| ⟨l, h⟩ := match n, h with ._, rfl := H l end

/- map -/

def map (f : α → β) : vector α n → vector β n
| ⟨ l, h ⟩  := ⟨ list.map f l, by simp * ⟩

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

theorem map_cons (f : α → β) (a : α) : Π (v : vector α n), map f (a::v) = f a :: map f v
| ⟨l,h⟩ := rfl

def map₂ (f : α → β → φ) : vector α n → vector β n → vector φ n
| ⟨ x, _ ⟩ ⟨ y, _ ⟩ := ⟨ list.map₂ f x y, by simp * ⟩

def repeat (a : α) (n : ℕ) : vector α n :=
⟨ list.repeat a n, list.length_repeat a n ⟩

def drop (i : ℕ) : vector α n → vector α (n - i)
| ⟨l, p⟩ := ⟨ list.drop i l, by simp * ⟩

def take (i : ℕ) : vector α n → vector α (min i n)
| ⟨l, p⟩ := ⟨ list.take i l, by simp * ⟩

def remove_nth (i : fin n) : vector α n → vector α (n - 1)
| ⟨l, p⟩ := ⟨ list.remove_nth l i.1, by rw [l.length_remove_nth i.1]; rw p; exact i.2 ⟩

def of_fn : Π {n}, (fin n → α) → vector α n
| 0 f := nil
| (n+1) f := f 0 :: of_fn (λi, f i.succ)

section accum
  open prod
  variable {σ : Type}

  def map_accumr (f : α → σ → σ × β) : vector α n → σ → σ × vector β n
  | ⟨ x, px ⟩ c :=
    let res := list.map_accumr f x c in
    ⟨ res.1, res.2, by simp * ⟩

  def map_accumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ)
   : vector α n → vector β n → σ → σ × vector φ n
  | ⟨ x, px ⟩ ⟨ y, py ⟩ c :=
    let res := list.map_accumr₂ f x y c in
    ⟨ res.1, res.2, by simp * ⟩

end accum

protected theorem eq {n : ℕ} : ∀ (a1 a2 : vector α n), to_list a1 = to_list a2 → a1 = a2
| ⟨x, h1⟩ ⟨._, h2⟩ rfl := rfl

protected theorem eq_nil (v : vector α 0) : v = nil :=
v.eq nil (list.eq_nil_of_length_eq_zero v.2)

@[simp] theorem to_list_mk (v : list α) (P : list.length v = n) : to_list (subtype.mk v P) = v :=
rfl

@[simp] theorem to_list_nil : to_list nil = @list.nil α :=
rfl

@[simp] theorem to_list_length (v : vector α n) : (to_list v).length = n := v.2

@[simp] theorem to_list_cons (a : α) (v : vector α n) : to_list (a :: v) = a :: to_list v :=
begin cases v, reflexivity end

@[simp] theorem to_list_append {n m : nat} (v : vector α n) (w : vector α m) : to_list (append v w) = to_list v ++ to_list w :=
begin cases v, cases w, reflexivity end

@[simp] theorem to_list_drop {n m : ℕ} (v : vector α m) : to_list (drop n v) = list.drop n (to_list v) :=
begin cases v, reflexivity end

@[simp] theorem to_list_take {n m : ℕ} (v : vector α m) : to_list (take n v) = list.take n (to_list v) :=
begin cases v, reflexivity end

end vector
