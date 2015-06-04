/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

List combinators.
-/
import data.list.basic
open nat prod decidable function helper_tactics

namespace list
variables {A B C : Type}
/- map -/
definition map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

theorem map_nil (f : A → B) : map f [] = []

theorem map_cons (f : A → B) (a : A) (l : list A) : map f (a :: l) = f a :: map f l

theorem map_id : ∀ l : list A, map id l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, map_id] end

theorem map_id' {f : A → A} (H : ∀x, f x = x) : ∀ l : list A, map f l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, H, map_id'] end

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

theorem exists_of_mem_map {A B : Type} {f : A → B} {b : B} :
    ∀{l}, b ∈ map f l → ∃a, a ∈ l ∧ f a = b
| []     H := false.elim H
| (c::l) H := or.elim (iff.mp !mem_cons_iff H)
                (assume H1 : b = f c,
                  exists.intro c (and.intro !mem_cons (eq.symm H1)))
                (assume H1 : b ∈ map f l,
                  obtain a (Hl : a ∈ l) (Hr : f a = b), from exists_of_mem_map H1,
                  exists.intro a (and.intro (mem_cons_of_mem _ Hl) Hr))

theorem eq_of_map_const {A B : Type} {b₁ b₂ : B} : ∀ {l : list A}, b₁ ∈ map (const A b₂) l → b₁ = b₂
| []     h := absurd h !not_mem_nil
| (a::l) h :=
  or.elim (eq_or_mem_of_mem_cons h)
    (λ b₁eqb₂ : b₁ = b₂, b₁eqb₂)
    (λ b₁inl  : b₁ ∈ map (const A b₂) l, eq_of_map_const b₁inl)

definition map₂ (f : A → B → C) : list A → list B → list C
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

/- filter -/
definition filter (p : A → Prop) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

theorem filter_nil (p : A → Prop) [h : decidable_pred p] : filter p [] = []

theorem filter_cons_of_pos {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ l, p a → filter p (a::l) = a :: filter p l :=
λ l pa, if_pos pa

theorem filter_cons_of_neg {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ l, ¬ p a → filter p (a::l) = filter p l :=
λ l pa, if_neg pa

theorem of_mem_filter {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ filter p l → p a
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (λ pb  : p b,
    have aux : a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, by rewrite [-aeqb at pb]; exact pb)
      (λ ainl, of_mem_filter ainl))
  (λ npb : ¬ p b, by rewrite [filter_cons_of_neg _ npb at ain]; exact (of_mem_filter ain))

theorem mem_of_mem_filter {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ filter p l → a ∈ l
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (λ pb  : p b,
    have aux : a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, by rewrite [aeqb]; exact !mem_cons)
      (λ ainl, mem_cons_of_mem _ (mem_of_mem_filter ainl)))
  (λ npb : ¬ p b, by rewrite [filter_cons_of_neg _ npb at ain]; exact (mem_cons_of_mem _ (mem_of_mem_filter ain)))

theorem mem_filter_of_mem {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
| []     ain pa := absurd ain !not_mem_nil
| (b::l) ain pa := by_cases
  (λ pb  : p b, or.elim (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, by rewrite [filter_cons_of_pos _ pb, aeqb]; exact !mem_cons)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_pos _ pb]; exact (mem_cons_of_mem _ (mem_filter_of_mem ainl pa))))
  (λ npb : ¬ p b, or.elim (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, absurd (eq.rec_on aeqb pa) npb)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_neg _ npb]; exact (mem_filter_of_mem ainl pa)))

theorem filter_sub {p : A → Prop} [h : decidable_pred p] (l : list A) : filter p l ⊆ l :=
λ a ain, mem_of_mem_filter ain

theorem filter_append {p : A → Prop} [h : decidable_pred p] : ∀ (l₁ l₂ : list A), filter p (l₁++l₂) = filter p l₁ ++ filter p l₂
| []      l₂ := rfl
| (a::l₁) l₂ := by_cases
  (λ pa  : p a, by rewrite [append_cons, *filter_cons_of_pos _ pa, filter_append])
  (λ npa : ¬ p a, by rewrite [append_cons, *filter_cons_of_neg _ npa, filter_append])

/- foldl & foldr -/
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
      change foldl f (f (f a b) c) l = f b (foldl f (f a c) l),
      rewrite -foldl_eq_of_comm_of_assoc,
      change foldl f (f (f a b) c) l = foldl f (f (f a c) b) l,
      have H₁ : f (f a b) c = f (f a c) b, by rewrite [Hassoc, Hassoc, Hcomm b c],
      rewrite H₁
    end

  theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a nil      := rfl
  | a (b :: l) :=
    begin
      rewrite foldl_eq_of_comm_of_assoc,
      esimp,
      change f b (foldl f a l) = f b (foldr f a l),
      rewrite foldl_eq_foldr
    end
end foldl_eq_foldr

theorem foldl_append (f : B → A → B) : ∀ (b : B) (l₁ l₂ : list A), foldl f b (l₁++l₂) = foldl f (foldl f b l₁) l₂
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldl_cons, foldl_append]

theorem foldr_append (f : A → B → B) : ∀ (b : B) (l₁ l₂ : list A), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldr_cons, foldr_append]

/- all & any -/
definition all (l : list A) (p : A → Prop) : Prop :=
foldr (λ a r, p a ∧ r) true l

definition any (l : list A) (p : A → Prop) : Prop :=
foldr (λ a r, p a ∨ r) false l

theorem all_nil_eq (p : A → Prop) : all [] p = true

theorem all_nil (p : A → Prop) : all [] p := trivial

theorem all_cons_eq (p : A → Prop) (a : A) (l : list A) : all (a::l) p = (p a ∧ all l p)

theorem all_cons {p : A → Prop} {a : A} {l : list A} (H1 : p a) (H2 : all l p) : all (a::l) p :=
and.intro H1 H2

theorem all_of_all_cons {p : A → Prop} {a : A} {l : list A} : all (a::l) p → all l p :=
assume h, by rewrite [all_cons_eq at h]; exact (and.elim_right h)

theorem of_all_cons {p : A → Prop} {a : A} {l : list A} : all (a::l) p → p a :=
assume h, by rewrite [all_cons_eq at h]; exact (and.elim_left h)

theorem all_cons_of_all {p : A → Prop} {a : A} {l : list A} : p a → all l p → all (a::l) p :=
assume pa alllp, and.intro pa alllp

theorem all_implies {p q : A → Prop} : ∀ {l}, all l p → (∀ x, p x → q x) → all l q
| []     h₁ h₂ := trivial
| (a::l) h₁ h₂ :=
  have allq : all l q, from all_implies (all_of_all_cons h₁) h₂,
  have qa : q a, from h₂ a (of_all_cons h₁),
  all_cons_of_all qa allq

theorem of_mem_of_all {p : A → Prop} {a : A} : ∀ {l}, a ∈ l → all l p → p a
| []     h₁ h₂ := absurd h₁ !not_mem_nil
| (b::l) h₁ h₂ :=
  or.elim (eq_or_mem_of_mem_cons h₁)
    (λ aeqb : a = b,
      by rewrite [all_cons_eq at h₂, -aeqb at h₂]; exact (and.elim_left h₂))
    (λ ainl : a ∈ l,
      have allp : all l p, by rewrite [all_cons_eq at h₂]; exact (and.elim_right h₂),
      of_mem_of_all ainl allp)

theorem all_of_forall {p : A → Prop} : ∀ {l}, (∀a, a ∈ l → p a) → all l p
| []     H := !all_nil
| (a::l) H := all_cons (H a !mem_cons)
                       (all_of_forall (λ a' H', H a' (mem_cons_of_mem _ H')))

theorem any_nil (p : A → Prop) : any [] p = false

theorem any_cons (p : A → Prop) (a : A) (l : list A) : any (a::l) p = (p a ∨ any l p)

theorem any_of_mem {p : A → Prop} {a : A} : ∀ {l}, a ∈ l → p a → any l p
| []     i h := absurd i !not_mem_nil
| (b::l) i h :=
  or.elim (eq_or_mem_of_mem_cons i)
    (λ aeqb : a = b, by rewrite [-aeqb]; exact (or.inl h))
    (λ ainl : a ∈ l,
      have anyl : any l p, from any_of_mem ainl h,
      or.inr anyl)

theorem exists_of_any {p : A → Prop} : ∀{l : list A}, any l p → ∃a, a ∈ l ∧ p a
| []     H := false.elim H
| (b::l) H := or.elim H
                (assume H1 : p b, exists.intro b (and.intro !mem_cons H1))
                (assume H1 : any l p,
                  obtain a (H2l : a ∈ l) (H2r : p a), from exists_of_any H1,
                  exists.intro a (and.intro (mem_cons_of_mem b H2l) H2r))

definition decidable_all (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (all l p)
| []       := decidable_true
| (a :: l) :=
  match H a with
  | inl Hp₁ :=
    match decidable_all l with
    | inl Hp₂ := inl (and.intro Hp₁ Hp₂)
    | inr Hn₂ := inr (not_and_of_not_right (p a) Hn₂)
    end
  | inr Hn := inr (not_and_of_not_left (all l p) Hn)
  end

definition decidable_any (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (any l p)
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

/- zip & unzip -/
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
    eapply prod.cases_on (unzip l),
    intro la lb r,
    rewrite -r
  end

/- flat -/
definition flat (l : list (list A)) : list A :=
foldl append nil l

/- product -/
section product

definition product : list A → list B → list (A × B)
| []      l₂ := []
| (a::l₁) l₂ := map (λ b, (a, b)) l₂ ++ product l₁ l₂

theorem nil_product (l : list B) : product (@nil A) l = []

theorem product_cons (a : A) (l₁ : list A) (l₂ : list B)
        : product (a::l₁) l₂ = map (λ b, (a, b)) l₂ ++ product l₁ l₂

theorem product_nil : ∀ (l : list A), product l (@nil B) = []
| []     := rfl
| (a::l) := by rewrite [product_cons, map_nil, product_nil]

theorem eq_of_mem_map_pair₁  {a₁ a : A} {b₁ : B} {l : list B} : (a₁, b₁) ∈ map (λ b, (a, b)) l → a₁ = a :=
assume ain,
assert h₁ : pr1 (a₁, b₁) ∈ map pr1 (map (λ b, (a, b)) l), from mem_map pr1 ain,
assert h₂ : a₁ ∈ map (λb, a) l, by rewrite [map_map at h₁, ↑pr1 at h₁]; exact h₁,
eq_of_map_const h₂

theorem mem_of_mem_map_pair₁ {a₁ a : A} {b₁ : B} {l : list B} : (a₁, b₁) ∈ map (λ b, (a, b)) l → b₁ ∈ l :=
assume ain,
assert h₁ : pr2 (a₁, b₁) ∈ map pr2 (map (λ b, (a, b)) l), from mem_map pr2 ain,
assert h₂ : b₁ ∈ map (λx, x) l, by rewrite [map_map at h₁, ↑pr2 at h₁]; exact h₁,
by rewrite [map_id at h₂]; exact h₂

theorem mem_product {a : A} {b : B} : ∀ {l₁ l₂}, a ∈ l₁ → b ∈ l₂ → (a, b) ∈ product l₁ l₂
| []      l₂ h₁ h₂ := absurd h₁ !not_mem_nil
| (x::l₁) l₂ h₁ h₂ :=
  or.elim (eq_or_mem_of_mem_cons h₁)
    (λ aeqx  : a = x,
      assert aux : (a, b) ∈ map (λ b, (a, b)) l₂, from mem_map _ h₂,
      by rewrite [-aeqx]; exact (mem_append_left _ aux))
    (λ ainl₁ : a ∈ l₁,
      have inl₁l₂ : (a, b) ∈ product l₁ l₂, from mem_product ainl₁ h₂,
      mem_append_right _ inl₁l₂)

theorem mem_of_mem_product_left {a : A} {b : B} : ∀ {l₁ l₂}, (a, b) ∈ product l₁ l₂ → a ∈ l₁
| []      l₂ h := absurd h !not_mem_nil
| (x::l₁) l₂ h :=
  or.elim (mem_or_mem_of_mem_append h)
    (λ ain : (a, b) ∈ map (λ b, (x, b)) l₂,
       assert aeqx : a = x, from eq_of_mem_map_pair₁ ain,
       by rewrite [aeqx]; exact !mem_cons)
    (λ ain : (a, b) ∈ product l₁ l₂,
      have ainl₁ : a ∈ l₁, from mem_of_mem_product_left ain,
      mem_cons_of_mem _ ainl₁)

theorem mem_of_mem_product_right {a : A} {b : B} : ∀ {l₁ l₂}, (a, b) ∈ product l₁ l₂ → b ∈ l₂
| []      l₂ h := absurd h !not_mem_nil
| (x::l₁) l₂ h :=
  or.elim (mem_or_mem_of_mem_append h)
    (λ abin : (a, b) ∈ map (λ b, (x, b)) l₂,
      mem_of_mem_map_pair₁ abin)
    (λ abin : (a, b) ∈ product l₁ l₂,
      mem_of_mem_product_right abin)
end product
end list

attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
