/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.comb
Authors: Leonardo de Moura

List combinators
-/
import data.list.basic
open nat prod decidable function helper_tactics

namespace list
variables {A B C : Type}

definition map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

theorem map_nil (f : A → B) : map f [] = []

theorem map_cons (f : A → B) (a : A) (l : list A) : map f (a :: l) = f a :: map f l

theorem map_id : ∀ l : list A, map id l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, map_id] end

theorem map_map (g : B → C) (f : A → B) : ∀ l, map g (map f l) = map (g ∘ f) l
| []       := rfl
| (a :: l) :=
  show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
  by rewrite (map_map l)

theorem len_map (f : A → B) : ∀ l : list A, length (map f l) = length l
| []       := by esimp
| (a :: l) :=
  show length (map f l) + 1 = length l + 1,
  by rewrite (len_map l)

theorem mem_map {A B : Type} (f : A → B) : ∀ {a l}, a ∈ l → f a ∈ map f l
| a []      i := absurd i !not_mem_nil
| a (x::xs) i := or.elim (eq_or_mem_of_mem_cons i)
   (λ aeqx  : a = x, by rewrite [aeqx, map_cons]; apply mem_cons)
   (λ ainxs : a ∈ xs, or.inr (mem_map ainxs))

definition map₂ (f : A → B → C) : list A → list B → list C
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

definition foldl (f : A → B → A) : A → list B → A
| a []       := a
| a (b :: l) := foldl (f a b) l

theorem foldl_nil (f : A → B → A) (a : A) : foldl f a [] = a

theorem foldl_cons (f : A → B → A) (a : A) (b : B) (l : list B) : foldl f a (b::l) = foldl f (f a b) l

definition foldr (f : A → B → B) : B → list A → B
| b []       := b
| b (a :: l) := f a (foldr b l)

theorem foldr_nil (f : A → B → B) (b : B) : foldr f b [] = b

theorem foldr_cons (f : A → B → B) (b : B) (a : A) (l : list A) : foldr f b (a::l) = f a (foldr f b l)

section foldl_eq_foldr
  -- foldl and foldr coincide when f is commutative and associative
  parameters {α : Type} {f : α → α → α}
  hypothesis (Hcomm  : ∀ a b, f a b = f b a)
  hypothesis (Hassoc : ∀ a b c, f (f a b) c = f a (f b c))
  include Hcomm Hassoc

  theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
  | a b  nil    := Hcomm a b
  | a b  (c::l) :=
    begin
      change (foldl f (f (f a b) c) l = f b (foldl f (f a c) l)),
      rewrite -foldl_eq_of_comm_of_assoc,
      change (foldl f (f (f a b) c) l = foldl f (f (f a c) b) l),
      have H₁ : f (f a b) c = f (f a c) b, by rewrite [Hassoc, Hassoc, Hcomm b c],
      rewrite H₁
    end

  theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a nil      := rfl
  | a (b :: l) :=
    begin
      rewrite foldl_eq_of_comm_of_assoc,
      esimp,
      change (f b (foldl f a l) = f b (foldr f a l)),
      rewrite foldl_eq_foldr
    end
end foldl_eq_foldr

theorem foldl_append (f : B → A → B) : ∀ (b : B) (l₁ l₂ : list A), foldl f b (l₁++l₂) = foldl f (foldl f b l₁) l₂
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldl_cons, foldl_append]

theorem foldr_append (f : A → B → B) : ∀ (b : B) (l₁ l₂ : list A), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldr_cons, foldr_append]

definition all (p : A → Prop) (l : list A) : Prop :=
foldr (λ a r, p a ∧ r) true l

definition any (p : A → Prop) (l : list A) : Prop :=
foldr (λ a r, p a ∨ r) false l

definition decidable_all (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (all p l)
| []       := decidable_true
| (a :: l) :=
  match H a with
  | inl Hp₁ :=
    match decidable_all l with
    | inl Hp₂ := inl (and.intro Hp₁ Hp₂)
    | inr Hn₂ := inr (not_and_of_not_right (p a) Hn₂)
    end
  | inr Hn := inr (not_and_of_not_left (all p l) Hn)
  end

definition decidable_any (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (any p l)
| []       := decidable_false
| (a :: l) :=
  match H a with
  | inl Hp := inl (or.inl Hp)
  | inr Hn₁ :=
    match decidable_any l with
    | inl Hp₂ := inl (or.inr Hp₂)
    | inr Hn₂ := inr (not_or Hn₁ Hn₂)
    end
  end

definition zip (l₁ : list A) (l₂ : list B) : list (A × B) :=
map₂ (λ a b, (a, b)) l₁ l₂

definition unzip : list (A × B) → list A × list B
| []            := ([], [])
| ((a, b) :: l) :=
  match unzip l with
  | (la, lb) := (a :: la, b :: lb)
  end

theorem unzip_nil : unzip (@nil (A × B)) = ([], [])

theorem unzip_cons (a : A) (b : B) (l : list (A × B)) :
   unzip ((a, b) :: l) = match unzip l with (la, lb) := (a :: la, b :: lb) end :=
rfl

theorem zip_unzip : ∀ (l : list (A × B)), zip (pr₁ (unzip l)) (pr₂ (unzip l)) = l
| []            := rfl
| ((a, b) :: l) :=
  begin
    rewrite unzip_cons,
    have r : zip (pr₁ (unzip l)) (pr₂ (unzip l)) = l, from zip_unzip l,
    revert r,
    apply (prod.cases_on (unzip l)),
    intros [la, lb, r],
    rewrite -r
  end

/- flat -/
definition flat (l : list (list A)) : list A :=
foldl append nil l
end list

attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
