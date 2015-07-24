/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Haitao Zhang

List combinators.
-/
import data.list.basic data.equiv
open nat prod decidable function helper_tactics

namespace list
variables {A B C : Type}
/- map -/
definition map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

theorem map_nil (f : A → B) : map f [] = []

theorem map_cons (f : A → B) (a : A) (l : list A) : map f (a :: l) = f a :: map f l

lemma map_append (f : A → B) : ∀ l₁ l₂, map f (l₁++l₂) = (map f l₁)++(map f l₂)
| nil    := take l, rfl
| (a::l) := take l', begin rewrite [append_cons, *map_cons, append_cons, map_append] end

lemma map_singleton (f : A → B) (a : A) : map f [a] = [f a] := rfl

theorem map_id [simp] : ∀ l : list A, map id l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, map_id] end

theorem map_id' {f : A → A} (H : ∀x, f x = x) : ∀ l : list A, map f l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, H, map_id'] end

theorem map_map [simp] (g : B → C) (f : A → B) : ∀ l, map g (map f l) = map (g ∘ f) l
| []       := rfl
| (a :: l) :=
  show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
  by rewrite (map_map l)

theorem length_map [simp] (f : A → B) : ∀ l : list A, length (map f l) = length l
| []       := by esimp
| (a :: l) :=
  show length (map f l) + 1 = length l + 1,
  by rewrite (length_map l)

theorem mem_map {A B : Type} (f : A → B) : ∀ {a l}, a ∈ l → f a ∈ map f l
| a []      i := absurd i !not_mem_nil
| a (x::xs) i := or.elim (eq_or_mem_of_mem_cons i)
   (suppose a = x, by rewrite [this, map_cons]; apply mem_cons)
   (suppose a ∈ xs, or.inr (mem_map this))

theorem exists_of_mem_map {A B : Type} {f : A → B} {b : B} :
    ∀{l}, b ∈ map f l → ∃a, a ∈ l ∧ f a = b
| []     H := false.elim H
| (c::l) H := or.elim (iff.mp !mem_cons_iff H)
                (suppose b = f c,
                  exists.intro c (and.intro !mem_cons (eq.symm this)))
                (suppose b ∈ map f l,
                  obtain a (Hl : a ∈ l) (Hr : f a = b), from exists_of_mem_map this,
                  exists.intro a (and.intro (mem_cons_of_mem _ Hl) Hr))

theorem eq_of_map_const {A B : Type} {b₁ b₂ : B} : ∀ {l : list A}, b₁ ∈ map (const A b₂) l → b₁ = b₂
| []     h := absurd h !not_mem_nil
| (a::l) h :=
  or.elim (eq_or_mem_of_mem_cons h)
    (suppose b₁ = b₂, this)
    (suppose b₁ ∈ map (const A b₂) l, eq_of_map_const this)

definition map₂ (f : A → B → C) : list A → list B → list C
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

/- filter -/
definition filter (p : A → Prop) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

theorem filter_nil [simp] (p : A → Prop) [h : decidable_pred p] : filter p [] = []

theorem filter_cons_of_pos [simp] {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ l, p a → filter p (a::l) = a :: filter p l :=
λ l pa, if_pos pa

theorem filter_cons_of_neg [simp] {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ l, ¬ p a → filter p (a::l) = filter p l :=
λ l pa, if_neg pa

theorem of_mem_filter {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ filter p l → p a
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (assume pb  : p b,
    have a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = b, by rewrite [-this at pb]; exact pb)
      (suppose a ∈ filter p l, of_mem_filter this))
  (suppose ¬ p b, by rewrite [filter_cons_of_neg _ this at ain]; exact (of_mem_filter ain))

theorem mem_of_mem_filter {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ filter p l → a ∈ l
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (λ pb  : p b,
    have a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = b, by rewrite this; exact !mem_cons)
      (suppose a ∈ filter p l, mem_cons_of_mem _ (mem_of_mem_filter this)))
  (suppose ¬ p b, by rewrite [filter_cons_of_neg _ this at ain]; exact (mem_cons_of_mem _ (mem_of_mem_filter ain)))

theorem mem_filter_of_mem {p : A → Prop} [h : decidable_pred p] {a : A} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
| []     ain pa := absurd ain !not_mem_nil
| (b::l) ain pa := by_cases
  (λ pb  : p b, or.elim (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, by rewrite [filter_cons_of_pos _ pb, aeqb]; exact !mem_cons)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_pos _ pb]; exact (mem_cons_of_mem _ (mem_filter_of_mem ainl pa))))
  (λ npb : ¬ p b, or.elim (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, absurd (eq.rec_on aeqb pa) npb)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_neg _ npb]; exact (mem_filter_of_mem ainl pa)))

theorem filter_sub [simp] {p : A → Prop} [h : decidable_pred p] (l : list A) : filter p l ⊆ l :=
λ a ain, mem_of_mem_filter ain

theorem filter_append {p : A → Prop} [h : decidable_pred p] : ∀ (l₁ l₂ : list A), filter p (l₁++l₂) = filter p l₁ ++ filter p l₂
| []      l₂ := rfl
| (a::l₁) l₂ := by_cases
  (suppose p a, by rewrite [append_cons, *filter_cons_of_pos _ this, filter_append])
  (suppose ¬ p a, by rewrite [append_cons, *filter_cons_of_neg _ this, filter_append])

/- foldl & foldr -/
definition foldl (f : A → B → A) : A → list B → A
| a []       := a
| a (b :: l) := foldl (f a b) l

theorem foldl_nil [simp] (f : A → B → A) (a : A) : foldl f a [] = a

theorem foldl_cons [simp] (f : A → B → A) (a : A) (b : B) (l : list B) : foldl f a (b::l) = foldl f (f a b) l

definition foldr (f : A → B → B) : B → list A → B
| b []       := b
| b (a :: l) := f a (foldr b l)

theorem foldr_nil [simp] (f : A → B → B) (b : B) : foldr f b [] = b

theorem foldr_cons [simp] (f : A → B → B) (b : B) (a : A) (l : list A) : foldr f b (a::l) = f a (foldr f b l)

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

theorem foldl_append [simp] (f : B → A → B) : ∀ (b : B) (l₁ l₂ : list A), foldl f b (l₁++l₂) = foldl f (foldl f b l₁) l₂
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldl_cons, foldl_append]

theorem foldr_append [simp] (f : A → B → B) : ∀ (b : B) (l₁ l₂ : list A), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldr_cons, foldr_append]

/- all & any -/
definition all (l : list A) (p : A → Prop) : Prop :=
foldr (λ a r, p a ∧ r) true l

definition any (l : list A) (p : A → Prop) : Prop :=
foldr (λ a r, p a ∨ r) false l

theorem all_nil_eq [simp] (p : A → Prop) : all [] p = true

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
  have all l q, from all_implies (all_of_all_cons h₁) h₂,
  have q a, from h₂ a (of_all_cons h₁),
  all_cons_of_all this `all l q`

theorem of_mem_of_all {p : A → Prop} {a : A} : ∀ {l}, a ∈ l → all l p → p a
| []     h₁ h₂ := absurd h₁ !not_mem_nil
| (b::l) h₁ h₂ :=
  or.elim (eq_or_mem_of_mem_cons h₁)
    (suppose a = b,
      by rewrite [all_cons_eq at h₂, -this at h₂]; exact (and.elim_left h₂))
    (suppose a ∈ l,
      have all l p, by rewrite [all_cons_eq at h₂]; exact (and.elim_right h₂),
      of_mem_of_all `a ∈ l` this)

theorem all_of_forall {p : A → Prop} : ∀ {l}, (∀a, a ∈ l → p a) → all l p
| []     H := !all_nil
| (a::l) H := all_cons (H a !mem_cons)
                       (all_of_forall (λ a' H', H a' (mem_cons_of_mem _ H')))

theorem any_nil [simp] (p : A → Prop) : any [] p = false

theorem any_cons [simp] (p : A → Prop) (a : A) (l : list A) : any (a::l) p = (p a ∨ any l p)

theorem any_of_mem {p : A → Prop} {a : A} : ∀ {l}, a ∈ l → p a → any l p
| []     i h := absurd i !not_mem_nil
| (b::l) i h :=
  or.elim (eq_or_mem_of_mem_cons i)
    (suppose a = b, by rewrite [-this]; exact (or.inl h))
    (suppose a ∈ l,
      have any l p, from any_of_mem this h,
      or.inr this)

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

theorem unzip_nil [simp] : unzip (@nil (A × B)) = ([], [])

theorem unzip_cons [simp] (a : A) (b : B) (l : list (A × B)) :
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
assert pr1 (a₁, b₁) ∈ map pr1 (map (λ b, (a, b)) l), from mem_map pr1 ain,
assert a₁ ∈ map (λb, a) l, by revert this; rewrite [map_map, ↑pr1]; intro this; assumption,
eq_of_map_const this

theorem mem_of_mem_map_pair₁ {a₁ a : A} {b₁ : B} {l : list B} : (a₁, b₁) ∈ map (λ b, (a, b)) l → b₁ ∈ l :=
assume ain,
assert pr2 (a₁, b₁) ∈ map pr2 (map (λ b, (a, b)) l), from mem_map pr2 ain,
assert b₁ ∈ map (λx, x) l, by rewrite [map_map at this, ↑pr2 at this]; exact this,
by rewrite [map_id at this]; exact this

theorem mem_product {a : A} {b : B} : ∀ {l₁ l₂}, a ∈ l₁ → b ∈ l₂ → (a, b) ∈ product l₁ l₂
| []      l₂ h₁ h₂ := absurd h₁ !not_mem_nil
| (x::l₁) l₂ h₁ h₂ :=
  or.elim (eq_or_mem_of_mem_cons h₁)
    (assume aeqx  : a = x,
      assert (a, b) ∈ map (λ b, (a, b)) l₂, from mem_map _ h₂,
      begin rewrite [-aeqx, product_cons], exact mem_append_left _ this end)
    (assume ainl₁ : a ∈ l₁,
      assert (a, b) ∈ product l₁ l₂, from mem_product ainl₁ h₂,
      begin rewrite [product_cons], exact mem_append_right _ this end)

theorem mem_of_mem_product_left {a : A} {b : B} : ∀ {l₁ l₂}, (a, b) ∈ product l₁ l₂ → a ∈ l₁
| []      l₂ h := absurd h !not_mem_nil
| (x::l₁) l₂ h :=
  or.elim (mem_or_mem_of_mem_append h)
    (suppose (a, b) ∈ map (λ b, (x, b)) l₂,
       assert a = x, from eq_of_mem_map_pair₁ this,
       by rewrite this; exact !mem_cons)
    (suppose (a, b) ∈ product l₁ l₂,
      have a ∈ l₁, from mem_of_mem_product_left this,
      mem_cons_of_mem _ this)

theorem mem_of_mem_product_right {a : A} {b : B} : ∀ {l₁ l₂}, (a, b) ∈ product l₁ l₂ → b ∈ l₂
| []      l₂ h := absurd h !not_mem_nil
| (x::l₁) l₂ h :=
  or.elim (mem_or_mem_of_mem_append h)
    (suppose (a, b) ∈ map (λ b, (x, b)) l₂,
      mem_of_mem_map_pair₁ this)
    (suppose (a, b) ∈ product l₁ l₂,
      mem_of_mem_product_right this)

theorem length_product : ∀ (l₁ : list A) (l₂ : list B), length (product l₁ l₂) = length l₁ * length l₂
| []      l₂ := by rewrite [length_nil, zero_mul]
| (x::l₁) l₂ :=
  assert length (product l₁ l₂) = length l₁ * length l₂, from length_product l₁ l₂,
  by rewrite [product_cons, length_append, length_cons,
              length_map, this, mul.right_distrib, one_mul, add.comm]
end product

-- new for list/comb dependent map theory
definition dinj₁ (p : A → Prop) (f : Π a, p a → B) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), a1 ≠ a2 → (f a1 h1) ≠ (f a2 h2)
definition dinj (p : A → Prop) (f : Π a, p a → B) := ∀ ⦃a1 a2⦄ (h1 : p a1) (h2 : p a2), (f a1 h1) = (f a2 h2) → a1 = a2

definition dmap (p : A → Prop) [h : decidable_pred p] (f : Π a, p a → B) : list A → list B
| []       := []
| (a::l)   := if P : (p a) then cons (f a P) (dmap l) else (dmap l)

-- properties of dmap
section dmap

variable {p : A → Prop}
variable [h : decidable_pred p]
include h
variable {f : Π a, p a → B}

lemma dmap_nil : dmap p f [] = [] := rfl
lemma dmap_cons_of_pos {a : A} (P : p a) : ∀ l, dmap p f (a::l) = (f a P) :: dmap p f l :=
      λ l, dif_pos P
lemma dmap_cons_of_neg {a : A} (P : ¬ p a) : ∀ l, dmap p f (a::l) = dmap p f l :=
      λ l, dif_neg P

lemma mem_dmap : ∀ {l : list A} {a} (Pa : p a), a ∈ l → (f a Pa) ∈ dmap p f l
| []     := take a Pa Pinnil, by contradiction
| (a::l) := take b Pb Pbin, or.elim (eq_or_mem_of_mem_cons Pbin)
              (assume Pbeqa, begin
                rewrite [eq.symm Pbeqa, dmap_cons_of_pos Pb],
                exact !mem_cons
              end)
              (assume Pbinl,
                decidable.rec_on (h a)
                (assume Pa, begin
                  rewrite [dmap_cons_of_pos Pa],
                  apply mem_cons_of_mem,
                  exact mem_dmap Pb Pbinl
                end)
                (assume nPa, begin
                  rewrite [dmap_cons_of_neg nPa],
                  exact mem_dmap Pb Pbinl
                end))

lemma exists_of_mem_dmap : ∀ {l : list A} {b : B}, b ∈ dmap p f l → ∃ a P, a ∈ l ∧ b = f a P
| []     := take b, by rewrite dmap_nil; contradiction
| (a::l) := take b, decidable.rec_on (h a)
  (assume Pa, begin
  rewrite [dmap_cons_of_pos Pa, mem_cons_iff],
  intro Pb, cases Pb with Peq Pin,
    exact exists.intro a (exists.intro Pa (and.intro !mem_cons Peq)),
    assert Pex : ∃ (a : A) (P : p a), a ∈ l ∧ b = f a P, exact exists_of_mem_dmap Pin,
    cases Pex with a' Pex', cases Pex' with Pa' P',
    exact exists.intro a' (exists.intro Pa' (and.intro (mem_cons_of_mem a (and.left P')) (and.right P')))
  end)
  (assume nPa,  begin
  rewrite [dmap_cons_of_neg nPa],
  intro Pin,
  assert Pex : ∃ (a : A) (P : p a), a ∈ l ∧ b = f a P, exact exists_of_mem_dmap Pin,
  cases Pex with a' Pex', cases Pex' with Pa' P',
  exact exists.intro a' (exists.intro Pa' (and.intro (mem_cons_of_mem a (and.left P')) (and.right P')))
  end)

lemma map_dmap_of_inv_of_pos {g : B → A} (Pinv : ∀ a (Pa : p a), g (f a Pa) = a) :
                          ∀ {l : list A}, (∀ ⦃a⦄, a ∈ l → p a) → map g (dmap p f l) = l
| []     := assume Pl, by rewrite [dmap_nil, map_nil]
| (a::l) := assume Pal,
            assert Pa : p a, from Pal a !mem_cons,
            assert Pl : ∀ a, a ∈ l → p a,
              from take x Pxin, Pal x (mem_cons_of_mem a Pxin),
            by rewrite [dmap_cons_of_pos Pa, map_cons, Pinv, map_dmap_of_inv_of_pos Pl]

lemma mem_of_dinj_of_mem_dmap (Pdi : dinj p f) :
      ∀ {l : list A} {a} (Pa : p a), (f a Pa) ∈ dmap p f l → a ∈ l
| []     := take a Pa Pinnil, by contradiction
| (b::l) := take a Pa Pmap,
              decidable.rec_on (h b)
              (λ Pb, begin
                rewrite (dmap_cons_of_pos Pb) at Pmap,
                rewrite mem_cons_iff at Pmap,
                rewrite mem_cons_iff,
                apply (or_of_or_of_imp_of_imp Pmap),
                  apply Pdi,
                  apply mem_of_dinj_of_mem_dmap Pa
              end)
              (λ nPb, begin
                 rewrite (dmap_cons_of_neg nPb) at Pmap,
                 apply mem_cons_of_mem,
                 exact mem_of_dinj_of_mem_dmap Pa Pmap
              end)

lemma not_mem_dmap_of_dinj_of_not_mem (Pdi : dinj p f) {l : list A} {a} (Pa : p a) :
  a ∉ l → (f a Pa) ∉ dmap p f l :=
not.mto (mem_of_dinj_of_mem_dmap Pdi Pa)

end dmap

section
open equiv
lemma list_equiv_of_equiv {A B : Type} : A ≃ B → list A ≃ list B
| (mk f g l r) :=
  mk (map f) (map g)
   begin intros, rewrite [map_map, id_of_left_inverse l, map_id] end
   begin intros, rewrite [map_map, id_of_righ_inverse r, map_id] end
end
end list

attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
