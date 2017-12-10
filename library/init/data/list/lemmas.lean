/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import init.data.list.basic init.function init.meta init.data.nat.lemmas
import init.meta.interactive init.meta.smt.rsimp

universes u v w w₁ w₂
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
open nat

/- append -/

@[simp] lemma nil_append (s : list α) : [] ++ s = s :=
rfl

@[simp] lemma cons_append (x : α) (s t : list α) : (x::s) ++ t = x::(s ++ t) :=
rfl

@[simp] lemma append_nil (t : list α) : t ++ [] = t :=
by induction t; simp [*]

@[simp] lemma append_assoc (s t u : list α) : s ++ t ++ u = s ++ (t ++ u) :=
by induction s; simp [*]

/- length -/

lemma length_cons (a : α) (l : list α) : length (a :: l) = length l + 1 :=
rfl

@[simp] lemma length_append (s t : list α) : length (s ++ t) = length s + length t :=
by induction s; simp [*]

@[simp] lemma length_repeat (a : α) (n : ℕ) : length (repeat a n) = n :=
by induction n; simp [*]; refl

@[simp] lemma length_tail (l : list α) : length (tail l) = length l - 1 :=
by cases l; refl

-- TODO(Leo): cleanup proof after arith dec proc
@[simp] lemma length_drop : ∀ (i : ℕ) (l : list α), length (drop i l) = length l - i
| 0 l         := rfl
| (succ i) [] := eq.symm (nat.zero_sub (succ i))
| (succ i) (x::l) := calc
  length (drop (succ i) (x::l))
          = length l - i             : length_drop i l
      ... = succ (length l) - succ i : (nat.succ_sub_succ_eq_sub (length l) i).symm

/- map -/

lemma map_cons (f : α → β) (a l) : map f (a::l) = f a :: map f l :=
rfl

@[simp] lemma map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = (map f l₁) ++ (map f l₂) :=
by intro l₁; induction l₁; intros; simp [*]

lemma map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
rfl

@[simp] lemma map_id (l : list α) : map id l = l :=
by induction l; simp [*]

@[simp] lemma map_map (g : β → γ) (f : α → β) (l : list α) : map g (map f l) = map (g ∘ f) l :=
by induction l; simp [*]

@[simp] lemma length_map (f : α → β) (l : list α) : length (map f l) = length l :=
by induction l; simp [*]

/- bind -/

@[simp] lemma nil_bind (f : α → list β) : list.bind [] f = [] :=
by simp [join, list.bind]

@[simp] lemma cons_bind (x xs) (f : α → list β) : list.bind (x :: xs) f = f x ++ list.bind xs f :=
by simp [join, list.bind]

@[simp] lemma append_bind (xs ys) (f : α → list β) : list.bind (xs ++ ys) f = list.bind xs f ++ list.bind ys f :=
by induction xs; [refl, simp [*, cons_bind]]

/- mem -/

@[simp] lemma mem_nil_iff (a : α) : a ∈ ([] : list α) ↔ false :=
iff.rfl

@[simp] lemma not_mem_nil (a : α) : a ∉ ([] : list α) :=
iff.mp $ mem_nil_iff a

@[simp] lemma mem_cons_self (a : α) (l : list α) : a ∈ a :: l :=
or.inl rfl

@[simp] lemma mem_cons_iff (a y : α) (l : list α) : a ∈ y :: l ↔ (a = y ∨ a ∈ l) :=
iff.rfl

@[rsimp] lemma mem_cons_eq (a y : α) (l : list α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
rfl

lemma mem_cons_of_mem (y : α) {a : α} {l : list α} : a ∈ l → a ∈ y :: l :=
assume H, or.inr H

lemma eq_or_mem_of_mem_cons {a y : α} {l : list α} : a ∈ y::l → a = y ∨ a ∈ l :=
assume h, h

@[simp] lemma mem_append {a : α} {s t : list α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t :=
by induction s; simp [*, or_assoc]

@[rsimp] lemma mem_append_eq (a : α) (s t : list α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
propext mem_append

lemma mem_append_left {a : α} {l₁ : list α} (l₂ : list α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
mem_append.2 (or.inl h)

lemma mem_append_right {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
mem_append.2 (or.inr h)

@[simp] lemma not_bex_nil (p : α → Prop) : ¬ (∃ x ∈ @nil α, p x) :=
λ⟨x, hx, px⟩, hx

@[simp] lemma ball_nil (p : α → Prop) : ∀ x ∈ @nil α, p x :=
λx, false.elim

@[simp] lemma bex_cons (p : α → Prop) (a : α) (l : list α) : (∃ x ∈ (a :: l), p x) ↔ (p a ∨ ∃ x ∈ l, p x) :=
⟨λ⟨x, h, px⟩, by {
  simp at h, cases h with h h, {cases h, exact or.inl px}, {exact or.inr ⟨x, h, px⟩}},
λo, o.elim (λpa, ⟨a, mem_cons_self _ _, pa⟩)
  (λ⟨x, h, px⟩, ⟨x, mem_cons_of_mem _ h, px⟩)⟩

@[simp] lemma ball_cons (p : α → Prop) (a : α) (l : list α) : (∀ x ∈ (a :: l), p x) ↔ (p a ∧ ∀ x ∈ l, p x) :=
⟨λal, ⟨al a (mem_cons_self _ _), λx h, al x (mem_cons_of_mem _ h)⟩,
 λ⟨pa, al⟩ x o, o.elim (λe, e.symm ▸ pa) (al x)⟩

/- list subset -/

protected def subset (l₁ l₂ : list α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : has_subset (list α) := ⟨list.subset⟩

@[simp] lemma nil_subset (l : list α) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil_iff b) i)

@[refl, simp] lemma subset.refl (l : list α) : l ⊆ l :=
λ b i, i

@[trans] lemma subset.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, h₂ (h₁ i)

@[simp] lemma subset_cons (a : α) (l : list α) : l ⊆ a::l :=
λ b i, or.inr i

lemma subset_of_cons_subset {a : α} {l₁ l₂ : list α} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s (mem_cons_of_mem _ i)

lemma cons_subset_cons {l₁ l₂ : list α} (a : α) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b hin, or.elim (eq_or_mem_of_mem_cons hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

@[simp] lemma subset_append_left (l₁ l₂ : list α) : l₁ ⊆ l₁++l₂ :=
λ b, mem_append_left _

@[simp] lemma subset_append_right (l₁ l₂ : list α) : l₂ ⊆ l₁++l₂ :=
λ b, mem_append_right _

lemma subset_cons_of_subset (a : α) {l₁ l₂ : list α} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁), or.inr (s i)

theorem eq_nil_of_length_eq_zero {l : list α} : length l = 0 → l = [] :=
by {induction l; intros, refl, contradiction}

theorem ne_nil_of_length_eq_succ {l : list α} : ∀ {n : nat}, length l = succ n → l ≠ [] :=
by induction l; intros; contradiction

@[simp] theorem length_map₂ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) :=
by {induction l₁; intro l₂; cases l₂; simp [*, add_one, min_succ_succ]}

@[simp] theorem length_take : ∀ (i : ℕ) (l : list α), length (take i l) = min i (length l)
| 0        l      := by simp
| (succ n) []     := by simp
| (succ n) (a::l) := by simp [*, nat.min_succ_succ, add_one]

theorem length_take_le (n) (l : list α) : length (take n l) ≤ n :=
by simp [min_le_left]

theorem length_remove_nth : ∀ (l : list α) (i : ℕ), i < length l → length (remove_nth l i) = length l - 1
| []      _     h := rfl
| (x::xs) 0     h := by simp [remove_nth, -add_comm]
| (x::xs) (i+1) h := have i < length xs, from lt_of_succ_lt_succ h,
  by dsimp [remove_nth]; rw [length_remove_nth xs i this, nat.sub_add_cancel (lt_of_le_of_lt (nat.zero_le _) this)]; refl

@[simp] lemma partition_eq_filter_filter (p : α → Prop) [decidable_pred p] : ∀ (l : list α), partition p l = (filter p l, filter (not ∘ p) l)
| []     := rfl
| (a::l) := by { by_cases pa : p a; simp [partition, filter, pa, partition_eq_filter_filter l] }

/- sublists -/

inductive sublist : list α → list α → Prop
| slnil : sublist [] []
| cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a::l₂)
| cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a::l₁) (a::l₂)

infix ` <+ `:50 := sublist

lemma length_le_of_sublist : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → length l₁ ≤ length l₂
| _ _ sublist.slnil             := le_refl 0
| _ _ (sublist.cons  l₁ l₂ a s) := le_succ_of_le (length_le_of_sublist s)
| _ _ (sublist.cons2 l₁ l₂ a s) := succ_le_succ (length_le_of_sublist s)

/- filter -/
@[simp] theorem filter_nil (p : α → Prop) [h : decidable_pred p] : filter p [] = [] := rfl

@[simp] theorem filter_cons_of_pos {p : α → Prop} [h : decidable_pred p] {a : α} :
   ∀ l, p a → filter p (a::l) = a :: filter p l :=
λ l pa, if_pos pa

@[simp] theorem filter_cons_of_neg {p : α → Prop} [h : decidable_pred p] {a : α} :
  ∀ l, ¬ p a → filter p (a::l) = filter p l :=
λ l pa, if_neg pa

@[simp] theorem filter_append {p : α → Prop} [h : decidable_pred p] :
  ∀ (l₁ l₂ : list α), filter p (l₁++l₂) = filter p l₁ ++ filter p l₂
| []      l₂ := rfl
| (a::l₁) l₂ := by by_cases pa : p a; simp [pa, filter_append]

@[simp] theorem filter_sublist {p : α → Prop} [h : decidable_pred p] : Π (l : list α), filter p l <+ l
| []     := sublist.slnil
| (a::l) := if pa : p a
  then by simp [pa]; apply sublist.cons2; apply filter_sublist l
  else by simp [pa]; apply sublist.cons; apply filter_sublist l

/- map_accumr -/
section map_accumr
variables {φ : Type w₁} {σ : Type w₂}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def map_accumr (f : α → σ → σ × β) : list α → σ → (σ × list β)
| [] c := (c, [])
| (y::yr) c :=
  let r := map_accumr yr c in
  let z := f y r.1 in
  (z.1, z.2 :: r.2)

@[simp] theorem length_map_accumr
: ∀ (f : α → σ → σ × β) (x : list α) (s : σ),
  length (map_accumr f x s).2 = length x
| f (a::x) s := congr_arg succ (length_map_accumr f x s)
| f [] s := rfl

end map_accumr

section map_accumr₂
variables {φ : Type w₁} {σ : Type w₂}
-- This runs a function over two lists returning the intermediate results and a
-- a final result.
def map_accumr₂ (f : α → β → σ → σ × φ)
  : list α → list β → σ → σ × list φ
| [] _ c := (c,[])
| _ [] c := (c,[])
| (x::xr) (y::yr) c :=
  let r := map_accumr₂ xr yr c in
  let q := f x y r.1 in
  (q.1, q.2 :: r.2)

@[simp] theorem length_map_accumr₂ : ∀ (f : α → β → σ → σ × φ) x y c,
  length (map_accumr₂ f x y c).2 = min (length x) (length y)
| f (a::x) (b::y) c := calc
    succ (length (map_accumr₂ f x y c).2)
              = succ (min (length x) (length y))
              : congr_arg succ (length_map_accumr₂ f x y c)
          ... = min (succ (length x)) (succ (length y))
              : eq.symm (min_succ_succ (length x) (length y))
| f (a::x) [] c := rfl
| f [] (b::y) c := rfl
| f [] []     c := rfl
end map_accumr₂

end list
