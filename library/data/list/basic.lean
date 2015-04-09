/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.basic
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura

Basic properties of lists.
-/
import logic tools.helper_tactics data.nat.basic algebra.function

open eq.ops helper_tactics nat prod function

inductive list (T : Type) : Type :=
| nil {} : list T
| cons   : T → list T → list T

namespace list
notation h :: t  := cons h t
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

variable {T : Type}

/- append -/

definition append : list T → list T → list T
| []       l := l
| (h :: s) t := h :: (append s t)

notation l₁ ++ l₂ := append l₁ l₂

theorem append_nil_left (t : list T) : [] ++ t = t

theorem append_cons (x : T) (s t : list T) : (x::s) ++ t = x::(s ++ t)

theorem append_nil_right : ∀ (t : list T), t ++ [] = t
| []       := rfl
| (a :: l) := calc
  (a :: l) ++ [] = a :: (l ++ []) : rfl
             ... = a :: l         : append_nil_right l


theorem append.assoc : ∀ (s t u : list T), s ++ t ++ u = s ++ (t ++ u)
| []       t u := rfl
| (a :: l) t u :=
  show a :: (l ++ t ++ u) = (a :: l) ++ (t ++ u),
  by rewrite (append.assoc l t u)

/- length -/

definition length : list T → nat
| []       := 0
| (a :: l) := length l + 1

theorem length_nil : length (@nil T) = 0

theorem length_cons (x : T) (t : list T) : length (x::t) = length t + 1

theorem length_append : ∀ (s t : list T), length (s ++ t) = length s + length t
| []       t := calc
    length ([] ++ t)  = length t : rfl
                   ... = length [] + length t : zero_add
| (a :: s) t := calc
    length (a :: s ++ t) = length (s ++ t) + 1        : rfl
                    ...  = length s + length t + 1    : length_append
                    ...  = (length s + 1) + length t  : add.succ_left
                    ...  = length (a :: s) + length t : rfl

theorem eq_nil_of_length_eq_zero : ∀ {l : list T}, length l = 0 → l = []
| []     H := rfl
| (a::s) H := nat.no_confusion H

-- add_rewrite length_nil length_cons

/- concat -/

definition concat : Π (x : T), list T → list T
| a []       := [a]
| a (b :: l) := b :: concat a l

theorem concat_nil (x : T) : concat x [] = [x]

theorem concat_cons (x y : T) (l : list T) : concat x (y::l)  = y::(concat x l)

theorem concat_eq_append (a : T) : ∀ (l : list T), concat a l = l ++ [a]
| []       := rfl
| (b :: l) :=
  show b :: (concat a l) = (b :: l) ++ (a :: []),
  by rewrite concat_eq_append

-- add_rewrite append_nil append_cons

/- reverse -/

definition reverse : list T → list T
| []       := []
| (a :: l) := concat a (reverse l)

theorem reverse_nil : reverse (@nil T) = []

theorem reverse_cons (x : T) (l : list T) : reverse (x::l) = concat x (reverse l)

theorem reverse_singleton (x : T) : reverse [x] = [x]

theorem reverse_append : ∀ (s t : list T), reverse (s ++ t) = (reverse t) ++ (reverse s)
| []         t2 := calc
    reverse ([] ++ t2) = reverse t2                    : rfl
                ...    = (reverse t2) ++ []           : append_nil_right
                ...    = (reverse t2) ++ (reverse []) : by rewrite reverse_nil
| (a2 :: s2) t2 := calc
    reverse ((a2 :: s2) ++ t2) = concat a2 (reverse (s2 ++ t2))         : rfl
                        ...    = concat a2 (reverse t2 ++ reverse s2)   : reverse_append
                        ...    = (reverse t2 ++ reverse s2) ++ [a2]     : concat_eq_append
                        ...    = reverse t2 ++ (reverse s2 ++ [a2])     : append.assoc
                        ...    = reverse t2 ++ concat a2 (reverse s2)   : concat_eq_append
                        ...    = reverse t2 ++ reverse (a2 :: s2)       : rfl

theorem reverse_reverse : ∀ (l : list T), reverse (reverse l) = l
| []       := rfl
| (a :: l) := calc
    reverse (reverse (a :: l)) = reverse (concat a (reverse l))     : rfl
                          ...  = reverse (reverse l ++ [a])         : concat_eq_append
                          ...  = reverse [a] ++ reverse (reverse l) : reverse_append
                          ...  = reverse [a] ++ l                   : reverse_reverse
                          ...  = a :: l                             : rfl

theorem concat_eq_reverse_cons (x : T) (l : list T) : concat x l = reverse (x :: reverse l) :=
calc
  concat x l = concat x (reverse (reverse l)) : reverse_reverse
         ... = reverse (x :: reverse l)       : rfl

/- head and tail -/

definition head [h : inhabited T] : list T → T
| []       := arbitrary T
| (a :: l) := a

theorem head_cons [h : inhabited T] (a : T) (l : list T) : head (a::l) = a

theorem head_append [h : inhabited T] (t : list T) : ∀ {s : list T}, s ≠ [] → head (s ++ t) = head s
| []       H := absurd rfl H
| (a :: s) H :=
  show head (a :: (s ++ t)) = head (a :: s),
  by  rewrite head_cons

definition tail : list T → list T
| []       := []
| (a :: l) := l

theorem tail_nil : tail (@nil T) = []

theorem tail_cons (a : T) (l : list T) : tail (a::l) = l

theorem cons_head_tail [h : inhabited T] {l : list T} : l ≠ [] → (head l)::(tail l) = l :=
list.cases_on l
  (assume H : [] ≠ [], absurd rfl H)
  (take x l, assume H : x::l ≠ [], rfl)

/- list membership -/

definition mem : T → list T → Prop
| a []       := false
| a (b :: l) := a = b ∨ mem a l

notation e ∈ s := mem e s
notation e ∉ s := ¬ e ∈ s

theorem mem_nil (x : T) : x ∈ [] ↔ false :=
iff.rfl

theorem not_mem_nil (x : T) : x ∉ [] :=
iff.mp !mem_nil

theorem mem_cons (x : T) (l : list T) : x ∈ x :: l :=
or.inl rfl

theorem mem_cons_of_mem (y : T) {x : T} {l : list T} : x ∈ l → x ∈ y :: l :=
assume H, or.inr H

theorem mem_cons_iff (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

theorem eq_or_mem_of_mem_cons {x y : T} {l : list T} : x ∈ y::l → x = y ∨ x ∈ l :=
assume h, h

theorem mem_singleton {x a : T} : x ∈ [a] → x = a :=
assume h : x ∈ [a], or.elim (eq_or_mem_of_mem_cons h)
  (λ xeqa : x = a, xeqa)
  (λ xinn : x ∈ [], absurd xinn !not_mem_nil)

theorem mem_of_mem_cons_of_mem {a b : T} {l : list T} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (λ aeqb : a = b, by rewrite [aeqb]; exact binl)
  (λ ainl : a ∈ l, ainl)

theorem mem_or_mem_of_mem_append {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
list.induction_on s or.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ y::s ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or_of_or_of_imp_right H2 IH,
    iff.elim_right or.assoc H3)

theorem mem_append_of_mem_or_mem {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
list.induction_on s
  (take H, or.elim H false.elim (assume H, H))
  (take y s,
    assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
    assume H : x ∈ y::s ∨ x ∈ t,
      or.elim H
        (assume H1,
          or.elim (eq_or_mem_of_mem_cons H1)
            (take H2 : x = y, or.inl H2)
            (take H2 : x ∈ s, or.inr (IH (or.inl H2))))
        (assume H1 : x ∈ t, or.inr (IH (or.inr H1))))

theorem mem_append_iff (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

theorem not_mem_of_not_mem_append_left {x : T} {s t : list T} : x ∉ s++t → x ∉ s :=
λ nxinst xins, absurd (mem_append_of_mem_or_mem (or.inl xins)) nxinst

theorem not_mem_of_not_mem_append_right {x : T} {s t : list T} : x ∉ s++t → x ∉ t :=
λ nxinst xint, absurd (mem_append_of_mem_or_mem (or.inr xint)) nxinst

theorem not_mem_append {x : T} {s t : list T} : x ∉ s → x ∉ t → x ∉ s++t :=
λ nxins nxint xinst, or.elim (mem_or_mem_of_mem_append xinst)
  (λ xins, absurd xins nxins)
  (λ xint, absurd xint nxint)

local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
list.induction_on l
  (take H : x ∈ [], false.elim (iff.elim_left !mem_nil H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim (eq_or_mem_of_mem_cons H)
      (assume H1 : x = y,
        exists.intro [] (!exists.intro (H1 ▸ rfl)))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x::t)), from IH H1,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have H4 : y :: l = (y::s) ++ (x::t),
          from H3 ▸ rfl,
        !exists.intro (!exists.intro H4)))

theorem mem_append_left {a : T} {l₁ : list T} (l₂ : list T) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (or.inl ainl₁)

theorem mem_append_right {a : T} (l₁ : list T) {l₂ : list T} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (or.inr ainl₂)

definition decidable_mem [instance] [H : decidable_eq T] (x : T) (l : list T) : decidable (x ∈ l) :=
list.rec_on l
  (decidable.inr (not_of_iff_false !mem_nil))
  (take (h : T) (l : list T) (iH : decidable (x ∈ l)),
    show decidable (x ∈ h::l), from
    decidable.rec_on iH
      (assume Hp : x ∈ l,
        decidable.rec_on (H x h)
          (assume Heq : x = h,
            decidable.inl (or.inl Heq))
          (assume Hne : x ≠ h,
            decidable.inl (or.inr Hp)))
      (assume Hn : ¬x ∈ l,
        decidable.rec_on (H x h)
          (assume Heq : x = h,
            decidable.inl (or.inl Heq))
          (assume Hne : x ≠ h,
            have H1 : ¬(x = h ∨ x ∈ l), from
              assume H2 : x = h ∨ x ∈ l, or.elim H2
                (assume Heq, absurd Heq Hne)
                (assume Hp,  absurd Hp Hn),
            have H2 : ¬x ∈ h::l, from
              iff.elim_right (not_iff_not_of_iff !mem_cons_iff) H1,
            decidable.inr H2)))

theorem mem_of_ne_of_mem {x y : T} {l : list T} (H₁ : x ≠ y) (H₂ : x ∈ y :: l) : x ∈ l :=
or.elim (eq_or_mem_of_mem_cons H₂) (λe, absurd e H₁) (λr, r)

theorem not_eq_of_not_mem {a b : T} {l : list T} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem {a b : T} {l : list T} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

definition sublist (l₁ l₂ : list T) := ∀ ⦃a : T⦄, a ∈ l₁ → a ∈ l₂

infix `⊆`:50 := sublist

lemma nil_sub (l : list T) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil b) i)

lemma sub.refl (l : list T) : l ⊆ l :=
λ b i, i

lemma sub.trans {l₁ l₂ l₃ : list T} (H₁ : l₁ ⊆ l₂) (H₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, H₂ (H₁ i)

lemma sub_cons (a : T) (l : list T) : l ⊆ a::l :=
λ b i, or.inr i

lemma cons_sub_cons  {l₁ l₂ : list T} (a : T) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b Hin, or.elim (eq_or_mem_of_mem_cons Hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

lemma sub_append_left (l₁ l₂ : list T) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mp' (mem_append_iff b l₁ l₂) (or.inl i)

lemma sub_append_right (l₁ l₂ : list T) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mp' (mem_append_iff b l₁ l₂) (or.inr i)

lemma sub_cons_of_sub (a : T) {l₁ l₂ : list T} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (x : T) (i : x ∈ l₁), or.inr (s i)

lemma sub_app_of_sub_left (l l₁ l₂ : list T) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (x : T) (xinl : x ∈ l),
  have xinl₁ : x ∈ l₁, from s xinl,
  mem_append_of_mem_or_mem (or.inl xinl₁)

lemma sub_app_of_sub_right (l l₁ l₂ : list T) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (x : T) (xinl : x ∈ l),
  have xinl₁ : x ∈ l₂, from s xinl,
  mem_append_of_mem_or_mem (or.inr xinl₁)

lemma cons_sub_of_sub_of_mem {a : T} {l m : list T} : a ∈ m → l ⊆ m → a::l ⊆ m :=
λ (ainm : a ∈ m) (lsubm : l ⊆ m) (x : T) (xinal : x ∈ a::l), or.elim (eq_or_mem_of_mem_cons xinal)
  (assume xeqa : x = a, eq.rec_on (eq.symm xeqa) ainm)
  (assume xinl : x ∈ l, lsubm xinl)

lemma app_sub_of_sub_of_sub {l₁ l₂ l : list T} : l₁ ⊆ l → l₂ ⊆ l → l₁++l₂ ⊆ l :=
λ (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) (x : T) (xinl₁l₂ : x ∈ l₁++l₂),
  or.elim (mem_or_mem_of_mem_append xinl₁l₂)
    (λ xinl₁ : x ∈ l₁, l₁subl xinl₁)
    (λ xinl₂ : x ∈ l₂, l₂subl xinl₂)

/- find -/

section
variable [H : decidable_eq T]
include H

definition find : T → list T → nat
| a []       := 0
| a (b :: l) := if a = b then 0 else succ (find a l)

theorem find_nil (x : T) : find x [] = 0

theorem find_cons (x y : T) (l : list T) : find x (y::l) = if x = y then 0 else succ (find x l)

theorem find.not_mem {l : list T} {x : T} : ¬x ∈ l → find x l = length l :=
list.rec_on l
   (assume P₁ : ¬x ∈ [], _)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      assume P₁ : ¬x ∈ y::l,
      have P₂ : ¬(x = y ∨ x ∈ l), from iff.elim_right (not_iff_not_of_iff !mem_cons_iff) P₁,
      have P₃ : ¬x = y ∧ ¬x ∈ l, from (iff.elim_left not_or_iff_not_and_not P₂),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : !find_cons
                  ... = succ (find x l)                      : if_neg (and.elim_left P₃)
                  ... = succ (length l)                      : {iH (and.elim_right P₃)}
                  ... = length (y::l)                        : !length_cons⁻¹)
end

/- nth element -/

definition nth [h : inhabited T] : list T → nat → T
| []       n     := arbitrary T
| (a :: l) 0     := a
| (a :: l) (n+1) := nth l n

theorem nth_zero [h : inhabited T] (a : T) (l : list T) : nth (a :: l) 0 = a

theorem nth_succ [h : inhabited T] (a : T) (l : list T) (n : nat) : nth (a::l) (n+1) = nth l n

open decidable
definition has_decidable_eq {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ = l₂)
| []      []      := inl rfl
| []      (b::l₂) := inr (λ H, list.no_confusion H)
| (a::l₁) []      := inr (λ H, list.no_confusion H)
| (a::l₁) (b::l₂) :=
  match H a b with
  | inl Hab  :=
    match has_decidable_eq l₁ l₂ with
    | inl He := inl (eq.rec_on Hab (eq.rec_on He rfl))
    | inr Hn := inr (λ H, list.no_confusion H (λ Hab Ht, absurd Ht Hn))
    end
  | inr Hnab := inr (λ H, list.no_confusion H (λ Hab Ht, absurd Hab Hnab))
  end

section combinators
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
| []       := rfl
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

end combinators

/- flat -/
section
variable {A : Type}

definition flat (l : list (list A)) : list A :=
foldl append nil l
end

/- quasiequal a l l' means that l' is exactly l, with a added
   once somewhere -/
section qeq
variable {A : Type}
inductive qeq (a : A) : list A → list A → Prop :=
| qhead : ∀ l, qeq a l (a::l)
| qcons : ∀ (b : A) {l l' : list A}, qeq a l l' → qeq a (b::l) (b::l')

open qeq

notation l' `≈`:50 a `|` l:50 := qeq a l l'

lemma qeq_app : ∀ (l₁ : list A) (a : A) (l₂ : list A), l₁++(a::l₂) ≈ a|l₁++l₂
| []      a l₂ := qhead a l₂
| (x::xs) a l₂ := qcons x (qeq_app xs a l₂)

lemma mem_head_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → a ∈ l₁ :=
take q, qeq.induction_on q
  (λ l, !mem_cons)
  (λ b l l' q r, or.inr r)

lemma mem_tail_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₂ → x ∈ l₁ :=
take q, qeq.induction_on q
  (λ l x i, or.inr i)
  (λ b l l' q r x xinbl, or.elim (eq_or_mem_of_mem_cons xinbl)
     (λ xeqb : x = b, xeqb ▸ mem_cons x l')
     (λ xinl : x ∈ l, or.inr (r x xinl)))

lemma mem_cons_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₁ → x ∈ a::l₂ :=
take q, qeq.induction_on q
  (λ l x i, i)
  (λ b l l' q r x xinbl', or.elim (eq_or_mem_of_mem_cons xinbl')
    (λ xeqb  : x = b, xeqb ▸ or.inr (mem_cons x l))
    (λ xinl' : x ∈ l', or.elim (eq_or_mem_of_mem_cons (r x xinl'))
      (λ xeqa : x = a, xeqa ▸ mem_cons x (b::l))
      (λ xinl : x ∈ l, or.inr (or.inr xinl))))

lemma length_eq_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → length l₁ = succ (length l₂) :=
take q, qeq.induction_on q
  (λ l, rfl)
  (λ b l l' q r, by rewrite [*length_cons, r])

lemma qeq_of_mem {a : A} {l : list A} : a ∈ l → (∃l', l≈a|l') :=
list.induction_on l
  (λ h : a ∈ nil, absurd h (not_mem_nil a))
  (λ x xs r ainxxs, or.elim (eq_or_mem_of_mem_cons ainxxs)
    (λ aeqx  : a = x,
       assert aux : ∃ l, x::xs≈x|l, from
         exists.intro xs (qhead x xs),
       by rewrite aeqx; exact aux)
    (λ ainxs : a ∈ xs,
       have ex : ∃l', xs ≈ a|l', from r ainxs,
       obtain (l' : list A) (q : xs ≈ a|l'), from ex,
       have q₂ : x::xs ≈ a | x::l', from qcons x q,
       exists.intro (x::l') q₂))

lemma qeq_split {a : A} {l l' : list A} : l'≈a|l → ∃l₁ l₂, l = l₁++l₂ ∧ l' = l₁++(a::l₂) :=
take q, qeq.induction_on q
  (λ t,
    have aux : t = []++t ∧ a::t = []++(a::t), from and.intro rfl rfl,
    exists.intro [] (exists.intro t aux))
  (λ b t t' q r,
    obtain (l₁ l₂ : list A) (h : t = l₁++l₂ ∧ t' = l₁++(a::l₂)), from r,
    have aux : b::t = (b::l₁)++l₂ ∧ b::t' = (b::l₁)++(a::l₂),
      begin
        rewrite [and.elim_right h, and.elim_left h],
        exact (and.intro rfl rfl)
      end,
    exists.intro (b::l₁) (exists.intro l₂ aux))

lemma sub_of_mem_of_sub_of_qeq {a : A} {l : list A} {u v : list A} : a ∉ l → a::l ⊆ v → v≈a|u → l ⊆ u :=
λ (nainl : a ∉ l) (s : a::l ⊆ v) (q : v≈a|u) (x : A) (xinl : x ∈ l),
  have xinv : x ∈ v, from s (or.inr xinl),
  have xinau : x ∈ a::u, from mem_cons_of_qeq q x xinv,
  or.elim (eq_or_mem_of_mem_cons xinau)
    (λ xeqa : x = a, absurd (xeqa ▸ xinl) nainl)
    (λ xinu : x ∈ u, xinu)
end qeq

section erase
variable {A : Type}
variable [H : decidable_eq A]
include H

definition erase (a : A) : list A → list A
| []     := []
| (b::l) :=
  match H a b with
  | inl e := l
  | inr n := b :: erase l
  end

lemma erase_nil (a : A) : erase a [] = [] :=
rfl

lemma erase_cons_head (a : A) (l : list A) : erase a (a :: l) = l :=
show match H a a with | inl e := l | inr n := a :: erase a l end = l,
by rewrite decidable_eq_inl_refl

lemma erase_cons_tail {a b : A} (l : list A) : a ≠ b → erase a (b::l) = b :: erase a l :=
assume h : a ≠ b,
show match H a b with | inl e := l | inr n₁ := b :: erase a l end = b :: erase a l,
by rewrite (decidable_eq_inr_neg h)

lemma length_erase_of_mem {a : A} : ∀ {l}, a ∈ l → length (erase a l) = pred (length l)
| []         h := rfl
| [x]        h := by rewrite [mem_singleton h, erase_cons_head]
| (x::y::xs) h :=
  by_cases
   (λ aeqx : a = x, by rewrite [aeqx, erase_cons_head])
   (λ anex : a ≠ x,
    assert ainyxs : a ∈ y::xs, from or_resolve_right h anex,
    by rewrite [erase_cons_tail _ anex, *length_cons, length_erase_of_mem ainyxs])

lemma length_erase_of_not_mem {a : A} : ∀ {l}, a ∉ l → length (erase a l) = length l
| []      h   := rfl
| (x::xs) h   :=
  assert anex   : a ≠ x,  from λ aeqx  : a = x,  absurd (or.inl aeqx) h,
  assert aninxs : a ∉ xs, from λ ainxs : a ∈ xs, absurd (or.inr ainxs) h,
  by rewrite [erase_cons_tail _ anex, length_cons, length_erase_of_not_mem aninxs]

lemma erase_append_left {a : A} : ∀ {l₁} (l₂), a ∈ l₁ → erase a (l₁++l₂) = erase a l₁ ++ l₂
| []      l₂  h := absurd h !not_mem_nil
| (x::xs) l₂  h :=
  by_cases
   (λ aeqx : a = x, by rewrite [aeqx, append_cons, *erase_cons_head])
   (λ anex : a ≠ x,
    assert ainxs : a ∈ xs, from mem_of_ne_of_mem anex h,
    by rewrite [append_cons, *erase_cons_tail _ anex, erase_append_left l₂ ainxs])

lemma erase_append_right {a : A} : ∀ {l₁} (l₂), a ∉ l₁ → erase a (l₁++l₂) = l₁ ++ erase a l₂
| []      l₂ h := _
| (x::xs) l₂ h :=
  by_cases
   (λ aeqx : a = x, by rewrite aeqx at h; exact (absurd !mem_cons h))
   (λ anex : a ≠ x,
    assert nainxs : a ∉ xs, from not_mem_of_not_mem h,
    by rewrite [append_cons, *erase_cons_tail _ anex, erase_append_right l₂ nainxs])

lemma erase_sub (a : A) : ∀ l, erase a l ⊆ l
| []      := λ x xine, xine
| (x::xs) := λ y xine,
  by_cases
    (λ aeqx : a = x, by rewrite [aeqx at xine, erase_cons_head at xine]; exact (or.inr xine))
    (λ anex : a ≠ x,
      assert yinxe : y ∈ x :: erase a xs, by rewrite [erase_cons_tail _ anex at xine]; exact xine,
      assert subxs : erase a xs ⊆ xs, from erase_sub xs,
      by_cases
        (λ yeqx : y = x, by rewrite yeqx; apply mem_cons)
        (λ ynex : y ≠ x,
          assert yine  : y ∈ erase a xs, from mem_of_ne_of_mem ynex yinxe,
          assert yinxs : y ∈ xs, from subxs yine,
          or.inr yinxs))

theorem mem_erase_of_ne_of_mem {a b : A} : ∀ {l : list A}, a ≠ b → a ∈ l → a ∈ erase b l
| []     n  i := absurd i !not_mem_nil
| (c::l) n  i := by_cases
  (λ beqc : b = c,
   assert ainl : a ∈ l, from or.elim (eq_or_mem_of_mem_cons i)
     (λ aeqc : a = c, absurd aeqc (beqc ▸ n))
     (λ ainl : a ∈ l, ainl),
   by rewrite [beqc, erase_cons_head]; exact ainl)
  (λ bnec : b ≠ c, by_cases
    (λ aeqc : a = c,
      assert aux : a ∈ c :: erase b l, by rewrite [aeqc]; exact !mem_cons,
      by rewrite [erase_cons_tail _ bnec]; exact aux)
    (λ anec : a ≠ c,
      have ainl  : a ∈ l, from mem_of_ne_of_mem anec i,
      have ainel : a ∈ erase b l, from mem_erase_of_ne_of_mem n ainl,
      assert aux : a ∈ c :: erase b l, from mem_cons_of_mem _ ainel,
      by rewrite [erase_cons_tail _ bnec]; exact aux)) --

theorem mem_of_mem_erase {a b : A} : ∀ {l}, a ∈ erase b l → a ∈ l
| []     i := absurd i !not_mem_nil
| (c::l) i := by_cases
  (λ beqc : b = c, by rewrite [beqc at i, erase_cons_head at i]; exact (mem_cons_of_mem _ i))
  (λ bnec : b ≠ c,
    have i₁ : a ∈ c :: erase b l, by rewrite [erase_cons_tail _ bnec at i]; exact i,
    or.elim (eq_or_mem_of_mem_cons i₁)
      (λ aeqc  : a = c, by rewrite [aeqc]; exact !mem_cons)
      (λ ainel : a ∈ erase b l,
        have ainl : a ∈ l, from mem_of_mem_erase ainel,
        mem_cons_of_mem _ ainl))
end erase

/- disjoint -/
section disjoint
variable {A : Type}

definition disjoint (l₁ l₂ : list A) : Prop := ∀ a, (a ∈ l₁ → a ∉ l₂) ∧ (a ∈ l₂ → a ∉ l₁)

lemma disjoint_left {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₁ → a ∉ l₂ :=
λ d a, and.elim_left (d a)

lemma disjoint_right {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
λ d a, and.elim_right (d a)

lemma disjoint.comm {l₁ l₂ : list A} : disjoint l₁ l₂ → disjoint l₂ l₁ :=
λ d a, and.intro
  (λ ainl₂ : a ∈ l₂, disjoint_right d ainl₂)
  (λ ainl₁ : a ∈ l₁, disjoint_left d ainl₁)

lemma disjoint_of_disjoint_cons_left {a : A} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
λ d x, and.intro
  (λ xinl₁ : x ∈ l₁, disjoint_left d (or.inr xinl₁))
  (λ xinl₂ : x ∈ l₂,
    have nxinal₁ : x ∉ a::l₁, from disjoint_right d xinl₂,
    not_mem_of_not_mem nxinal₁)

lemma disjoint_of_disjoint_cons_right {a : A} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
λ d, disjoint.comm (disjoint_of_disjoint_cons_left (disjoint.comm d))

lemma disjoint_nil_left (l : list A) : disjoint [] l :=
λ a, and.intro
  (λ ab   : a ∈ nil, absurd ab !not_mem_nil)
  (λ ainl : a ∈ l, !not_mem_nil)

lemma disjoint_nil_right (l : list A) : disjoint l [] :=
disjoint.comm (disjoint_nil_left l)

lemma disjoint_cons_of_not_mem_of_disjoint {a : A} {l₁ l₂} : a ∉ l₂ → disjoint l₁ l₂ → disjoint (a::l₁) l₂ :=
λ nainl₂ d x, and.intro
  (λ xinal₁ : x ∈ a::l₁, or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, xeqa⁻¹ ▸ nainl₂)
    (λ xinl₁ : x ∈ l₁, disjoint_left d xinl₁))
  (λ (xinl₂ : x ∈ l₂) (xinal₁ : x ∈ a::l₁), or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, absurd (xeqa ▸ xinl₂) nainl₂)
    (λ xinl₁ : x ∈ l₁, absurd xinl₁ (disjoint_right d xinl₂)))

lemma disjoint_of_disjoint_append_left_left : ∀ {l₁ l₂ l : list A}, disjoint (l₁++l₂) l → disjoint l₁ l
| []      l₂ l d := disjoint_nil_left l
| (x::xs) l₂ l d :=
  have nxinl : x ∉ l, from disjoint_left d !mem_cons,
  have d₁    : disjoint (xs++l₂) l, from disjoint_of_disjoint_cons_left d,
  have d₂    : disjoint xs l, from disjoint_of_disjoint_append_left_left d₁,
  disjoint_cons_of_not_mem_of_disjoint nxinl d₂

lemma disjoint_of_disjoint_append_left_right : ∀ {l₁ l₂ l : list A}, disjoint (l₁++l₂) l → disjoint l₂ l
| []      l₂ l d := d
| (x::xs) l₂ l d :=
  have d₁  : disjoint (xs++l₂) l, from disjoint_of_disjoint_cons_left d,
  disjoint_of_disjoint_append_left_right d₁

lemma disjoint_of_disjoint_append_right_left : ∀ {l₁ l₂ l : list A}, disjoint l (l₁++l₂) → disjoint l l₁ :=
λ l₁ l₂ l d, disjoint.comm (disjoint_of_disjoint_append_left_left (disjoint.comm d))

lemma disjoint_of_disjoint_append_right_right : ∀ {l₁ l₂ l : list A}, disjoint l (l₁++l₂) → disjoint l l₂ :=
λ l₁ l₂ l d, disjoint.comm (disjoint_of_disjoint_append_left_right (disjoint.comm d))

end disjoint

/- no duplicates predicate -/

inductive nodup {A : Type} : list A → Prop :=
| ndnil  : nodup []
| ndcons : ∀ {a l}, a ∉ l → nodup l → nodup (a::l)

section nodup
open nodup
variables {A B : Type}

theorem nodup_nil : @nodup A [] :=
ndnil

theorem nodup_cons {a : A} {l : list A} : a ∉ l → nodup l → nodup (a::l)  :=
λ i n, ndcons i n

theorem nodup_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → nodup l
| a xs (ndcons i n) := n

theorem not_mem_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → a ∉ l
| a xs (ndcons i n) := i

theorem nodup_of_nodup_append_left : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → nodup l₁
| []      l₂ n := nodup_nil
| (x::xs) l₂ n :=
  have ndxs     : nodup xs,   from nodup_of_nodup_append_left (nodup_of_nodup_cons n),
  have nxinxsl₂ : x ∉ xs++l₂, from not_mem_of_nodup_cons n,
  have nxinxs   : x ∉ xs,     from not_mem_of_not_mem_append_left nxinxsl₂,
  nodup_cons nxinxs ndxs

theorem nodup_of_nodup_append_right : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → nodup l₂
| []      l₂ n := n
| (x::xs) l₂ n := nodup_of_nodup_append_right (nodup_of_nodup_cons n)

theorem disjoint_of_nodup_append : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → disjoint l₁ l₂
| []      l₂  d := disjoint_nil_left l₂
| (x::xs) l₂  d :=
  have d₁     : nodup (x::(xs++l₂)), from d,
  have d₂     : nodup (xs++l₂),      from nodup_of_nodup_cons d₁,
  have nxin   : x ∉ xs++l₂,          from not_mem_of_nodup_cons d₁,
  have nxinl₂ : x ∉ l₂,              from not_mem_of_not_mem_append_right nxin,
  have dsj    : disjoint xs l₂,      from disjoint_of_nodup_append d₂,
  (λ a, and.intro
    (λ ainxxs : a ∈ x::xs,
      or.elim (eq_or_mem_of_mem_cons ainxxs)
        (λ aeqx  : a = x, aeqx⁻¹ ▸ nxinl₂)
        (λ ainxs : a ∈ xs, disjoint_left dsj ainxs))
    (λ ainl₂  : a ∈ l₂,
      have nainxs : a ∉ xs, from disjoint_right dsj ainl₂,
      assume ain : a ∈ x::xs, or.elim (eq_or_mem_of_mem_cons ain)
       (λ aeqx  : a = x, absurd (aeqx ▸ ainl₂) nxinl₂)
       (λ ainxs : a ∈ xs, absurd ainxs nainxs)))

theorem nodup_append_of_nodup_of_nodup_of_disjoint : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → disjoint l₁ l₂ → nodup (l₁++l₂)
| []      l₂ d₁ d₂ dsj := by rewrite [append_nil_left]; exact d₂
| (x::xs) l₂ d₁ d₂ dsj :=
  have dsj₁     : disjoint xs l₂,      from disjoint_of_disjoint_cons_left dsj,
  have ndxs     : nodup xs,            from nodup_of_nodup_cons d₁,
  have ndxsl₂   : nodup (xs++l₂),      from nodup_append_of_nodup_of_nodup_of_disjoint ndxs d₂ dsj₁,
  have nxinxs   : x ∉ xs,              from not_mem_of_nodup_cons d₁,
  have nxinl₂   : x ∉ l₂,              from disjoint_left dsj !mem_cons,
  have nxinxsl₂ : x ∉ xs++l₂,          from not_mem_append nxinxs nxinl₂,
  nodup_cons nxinxsl₂ ndxsl₂

theorem nodup_app_comm {l₁ l₂ : list A} (d : nodup (l₁++l₂)) : nodup (l₂++l₁) :=
have d₁  : nodup l₁,       from nodup_of_nodup_append_left d,
have d₂  : nodup l₂,       from nodup_of_nodup_append_right d,
have dsj : disjoint l₁ l₂, from disjoint_of_nodup_append d,
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₁ (disjoint.comm dsj)

theorem nodup_head {a : A} {l₁ l₂ : list A} (d : nodup (l₁++(a::l₂))) : nodup (a::(l₁++l₂)) :=
have d₁    : nodup (a::(l₂++l₁)), from nodup_app_comm d,
have d₂    : nodup (l₂++l₁),      from nodup_of_nodup_cons d₁,
have d₃    : nodup (l₁++l₂),      from nodup_app_comm d₂,
have nain  : a ∉ l₂++l₁,          from not_mem_of_nodup_cons d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_left nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_right nain,
nodup_cons (not_mem_append nain₁ nain₂) d₃

theorem nodup_middle {a : A} {l₁ l₂ : list A} (d : nodup (a::(l₁++l₂))) : nodup (l₁++(a::l₂)) :=
have d₁    : nodup (l₁++l₂),      from nodup_of_nodup_cons d,
have nain  : a ∉ l₁++l₂,          from not_mem_of_nodup_cons d,
have disj  : disjoint l₁ l₂,      from disjoint_of_nodup_append d₁,
have d₂    : nodup l₁,            from nodup_of_nodup_append_left d₁,
have d₃    : nodup l₂,            from nodup_of_nodup_append_right d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_right nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_left nain,
have d₄    : nodup (a::l₂),       from nodup_cons nain₂ d₃,
have disj₂ : disjoint l₁ (a::l₂), from disjoint.comm (disjoint_cons_of_not_mem_of_disjoint nain₁ (disjoint.comm disj)),
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₄ disj₂

theorem nodup_map {f : A → B} (inj : injective f) : ∀ {l : list A}, nodup l → nodup (map f l)
| []      n := begin rewrite [map_nil], apply nodup_nil end
| (x::xs) n :=
  assert nxinxs : x ∉ xs,           from not_mem_of_nodup_cons n,
  assert ndxs   : nodup xs,         from nodup_of_nodup_cons n,
  assert ndmfxs : nodup (map f xs), from nodup_map ndxs,
  assert nfxinm : f x ∉ map f xs,   from
    λ ab : f x ∈ map f xs,
      obtain (finv : B → A) (isinv : finv ∘ f = id), from inj,
      assert finvfxin : finv (f x) ∈ map finv (map f xs), from mem_map finv ab,
      assert xinxs : x ∈ xs,
        begin
          rewrite [map_map at finvfxin, isinv at finvfxin, left_inv_eq isinv at finvfxin],
          rewrite [map_id at finvfxin],
          exact finvfxin
        end,
      absurd xinxs nxinxs,
  nodup_cons nfxinm ndmfxs

theorem nodup_erase_of_nodup [h : decidable_eq A] (a : A) : ∀ {l}, nodup l → nodup (erase a l)
| []     n := nodup_nil
| (b::l) n := by_cases
  (λ aeqb : a = b, by rewrite [aeqb, erase_cons_head]; exact (nodup_of_nodup_cons n))
  (λ aneb : a ≠ b,
    have nbinl   : b ∉ l,                  from not_mem_of_nodup_cons n,
    have ndl     : nodup l,                from nodup_of_nodup_cons n,
    have ndeal   : nodup (erase a l),      from nodup_erase_of_nodup ndl,
    have nbineal : b ∉ erase a l,          from λ i, absurd (erase_sub _ _ i) nbinl,
    assert aux   : nodup (b :: erase a l), from nodup_cons nbineal ndeal,
    by rewrite [erase_cons_tail _ aneb]; exact aux)

theorem mem_erase_of_nodup [h : decidable_eq A] (a : A) : ∀ {l}, nodup l → a ∉ erase a l
| []     n := !not_mem_nil
| (b::l) n :=
  have ndl     : nodup l,       from nodup_of_nodup_cons n,
  have naineal : a ∉ erase a l, from mem_erase_of_nodup ndl,
  assert nbinl : b ∉ l,         from not_mem_of_nodup_cons n,
  by_cases
  (λ aeqb : a = b, by rewrite [aeqb, erase_cons_head]; exact nbinl)
  (λ aneb : a ≠ b,
    assert aux : a ∉ b :: erase a l, from
      assume ainbeal : a ∈ b :: erase a l, or.elim (eq_or_mem_of_mem_cons ainbeal)
        (λ aeqb   : a = b, absurd aeqb aneb)
        (λ aineal : a ∈ erase a l, absurd aineal naineal),
    by rewrite [erase_cons_tail _ aneb]; exact aux)

definition erase_dup [H : decidable_eq A] : list A → list A
| []        :=  []
| (x :: xs) :=  if x ∈ xs then erase_dup xs else x :: erase_dup xs

theorem erase_dup_nil [H : decidable_eq A] : erase_dup [] = []

theorem erase_dup_cons_of_mem [H : decidable_eq A] {a : A} {l : list A} : a ∈ l → erase_dup (a::l) = erase_dup l :=
assume ainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = erase_dup l                                     : if_pos ainl

theorem erase_dup_cons_of_not_mem [H : decidable_eq A] {a : A} {l : list A} : a ∉ l → erase_dup (a::l) = a :: erase_dup l :=
assume nainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = a :: erase_dup l                                : if_neg nainl

theorem mem_erase_dup [H : decidable_eq A] {a : A} : ∀ {l}, a ∈ l → a ∈ erase_dup l
| []     h  := absurd h !not_mem_nil
| (b::l) h  := by_cases
  (λ binl  : b ∈ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b, by rewrite [erase_dup_cons_of_mem binl, -aeqb at binl]; exact (mem_erase_dup binl))
    (λ ainl : a ∈ l, by rewrite [erase_dup_cons_of_mem binl]; exact (mem_erase_dup ainl)))
  (λ nbinl : b ∉ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b, by rewrite [erase_dup_cons_of_not_mem nbinl, aeqb]; exact !mem_cons)
    (λ ainl : a ∈ l, by rewrite [erase_dup_cons_of_not_mem nbinl]; exact (or.inr (mem_erase_dup ainl))))

theorem mem_of_mem_erase_dup [H : decidable_eq A] {a : A} : ∀ {l}, a ∈ erase_dup l → a ∈ l
| []     h := by rewrite [erase_dup_nil at h]; exact h
| (b::l) h := by_cases
  (λ binl  : b ∈ l,
    have h₁ : a ∈ erase_dup l, by rewrite [erase_dup_cons_of_mem binl at h]; exact h,
    or.inr (mem_of_mem_erase_dup h₁))
  (λ nbinl : b ∉ l,
    have h₁ : a ∈ b :: erase_dup l, by rewrite [erase_dup_cons_of_not_mem nbinl at h]; exact h,
    or.elim (eq_or_mem_of_mem_cons h₁)
      (λ aeqb  : a = b, by rewrite aeqb; exact !mem_cons)
      (λ ainel : a ∈ erase_dup l, or.inr (mem_of_mem_erase_dup ainel)))

theorem nodup_erase_dup [H : decidable_eq A] : ∀ l : list A, nodup (erase_dup l)
| []        := by rewrite erase_dup_nil; exact nodup_nil
| (a::l)    := by_cases
  (λ ainl  : a ∈ l, by rewrite [erase_dup_cons_of_mem ainl]; exact (nodup_erase_dup l))
  (λ nainl : a ∉ l,
    assert r   : nodup (erase_dup l), from nodup_erase_dup l,
    assert nin : a ∉ erase_dup l, from
      assume ab : a ∈ erase_dup l, absurd (mem_of_mem_erase_dup ab) nainl,
    by rewrite [erase_dup_cons_of_not_mem nainl]; exact (nodup_cons nin r))

theorem erase_dup_eq_of_nodup [H : decidable_eq A] : ∀ {l : list A}, nodup l → erase_dup l = l
| []     d := rfl
| (a::l) d :=
  assert nainl : a ∉ l, from not_mem_of_nodup_cons d,
  assert dl : nodup l,  from nodup_of_nodup_cons d,
  by rewrite [erase_dup_cons_of_not_mem nainl, erase_dup_eq_of_nodup dl]
end nodup

/- union -/
section union
variable {A : Type}
variable [H : decidable_eq A]
include H

definition union : list A → list A → list A
| []      l₂ := l₂
| (a::l₁) l₂ := if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂

theorem union_nil (l : list A) : union [] l = l

theorem union_cons_of_mem {a : A} {l₂} : ∀ (l₁), a ∈ l₂ → union (a::l₁) l₂ = union l₁ l₂ :=
take l₁, assume ainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = union l₁ l₂                                           : if_pos ainl₂

theorem union_cons_of_not_mem {a : A} {l₂} : ∀ (l₁), a ∉ l₂ → union (a::l₁) l₂ = a :: union l₁ l₂ :=
take l₁, assume nainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = a :: union l₁ l₂                                      : if_neg nainl₂

theorem mem_or_mem_of_mem_union : ∀ {l₁ l₂} {a : A}, a ∈ union l₁ l₂ → a ∈ l₁ ∨ a ∈ l₂
| []      l₂ a ainl₂ := by rewrite union_nil at ainl₂; exact (or.inr (ainl₂))
| (b::l₁) l₂ a ainbl₁l₂ := by_cases
  (λ binl₂  : b ∈ l₂,
    have ainl₁l₂ : a ∈ union l₁ l₂, by rewrite [union_cons_of_mem l₁ binl₂ at ainbl₁l₂]; exact ainbl₁l₂,
    or.elim (mem_or_mem_of_mem_union ainl₁l₂)
      (λ ainl₁, or.inl (mem_cons_of_mem _ ainl₁))
      (λ ainl₂, or.inr ainl₂))
  (λ nbinl₂ : b ∉ l₂,
    have ainb_l₁l₂ : a ∈ b :: union l₁ l₂, by rewrite [union_cons_of_not_mem l₁ nbinl₂ at ainbl₁l₂]; exact ainbl₁l₂,
    or.elim (eq_or_mem_of_mem_cons ainb_l₁l₂)
      (λ aeqb, by rewrite aeqb; exact (or.inl !mem_cons))
      (λ ainl₁l₂,
        or.elim (mem_or_mem_of_mem_union ainl₁l₂)
          (λ ainl₁, or.inl (mem_cons_of_mem _ ainl₁))
          (λ ainl₂, or.inr ainl₂)))

theorem mem_union_right {a : A} : ∀ (l₁) {l₂}, a ∈ l₂ → a ∈ union l₁ l₂
| []      l₂  h := by rewrite union_nil; exact h
| (b::l₁) l₂  h := by_cases
  (λ binl₂ : b ∈ l₂, by rewrite [union_cons_of_mem _ binl₂]; exact (mem_union_right _ h))
  (λ nbinl₂ : b ∉ l₂, by rewrite [union_cons_of_not_mem _ nbinl₂]; exact (mem_cons_of_mem _ (mem_union_right _ h)))

theorem mem_union_left {a : A} : ∀ {l₁} (l₂), a ∈ l₁ → a ∈ union l₁ l₂
| []      l₂  h := absurd h !not_mem_nil
| (b::l₁) l₂  h := by_cases
  (λ binl₂  : b ∈ l₂, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb  : a = b,
      by rewrite [union_cons_of_mem l₁ binl₂, -aeqb at binl₂]; exact (mem_union_right _ binl₂))
    (λ ainl₁ : a ∈ l₁,
      by rewrite [union_cons_of_mem l₁ binl₂]; exact (mem_union_left _ ainl₁)))
  (λ nbinl₂ : b ∉ l₂, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb  : a = b,
      by rewrite [union_cons_of_not_mem l₁ nbinl₂, aeqb]; exact !mem_cons)
    (λ ainl₁ : a ∈ l₁,
      by rewrite [union_cons_of_not_mem l₁ nbinl₂]; exact (mem_cons_of_mem _ (mem_union_left _ ainl₁))))

theorem nodup_union_of_nodup_of_nodup : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → nodup (union l₁ l₂)
| []      l₂ n₁   nl₂ := by rewrite union_nil; exact nl₂
| (a::l₁) l₂ nal₁ nl₂ :=
  assert nl₁   : nodup l₁, from nodup_of_nodup_cons nal₁,
  assert nl₁l₂ : nodup (union l₁ l₂), from nodup_union_of_nodup_of_nodup nl₁ nl₂,
  by_cases
    (λ ainl₂  : a ∈ l₂,
       by rewrite [union_cons_of_mem l₁ ainl₂]; exact nl₁l₂)
    (λ nainl₂ : a ∉ l₂,
       have nainl₁ : a ∉ l₁, from not_mem_of_nodup_cons nal₁,
       assert nainl₁l₂ : a ∉ union l₁ l₂, from
         assume ainl₁l₂ : a ∈ union l₁ l₂, or.elim (mem_or_mem_of_mem_union ainl₁l₂)
           (λ ainl₁, absurd ainl₁ nainl₁)
           (λ ainl₂, absurd ainl₂ nainl₂),
       by rewrite [union_cons_of_not_mem l₁ nainl₂]; exact (nodup_cons nainl₁l₂ nl₁l₂))
end union

/- insert -/
section insert
variable {A : Type}
variable [H : decidable_eq A]
include H

definition insert (a : A) (l : list A) : list A :=
if a ∈ l then l else a::l

theorem insert_eq_of_mem {a : A} {l : list A} : a ∈ l → insert a l = l :=
assume ainl, if_pos ainl

theorem insert_eq_of_not_mem {a : A} {l : list A} : a ∉ l → insert a l = a::l :=
assume nainl, if_neg nainl

theorem mem_insert (a : A) (l : list A) : a ∈ insert a l :=
by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact ainl)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact !mem_cons)

theorem mem_insert_of_mem {a : A} (b : A) {l : list A} : a ∈ l → a ∈ insert b l :=
assume ainl, by_cases
  (λ binl  : b ∈ l, by rewrite [insert_eq_of_mem binl]; exact ainl)
  (λ nbinl : b ∉ l, by rewrite [insert_eq_of_not_mem nbinl]; exact (mem_cons_of_mem _ ainl))

theorem nodup_insert (a : A) {l : list A} : nodup l → nodup (insert a l) :=
assume n, by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact n)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact (nodup_cons nainl n))

theorem length_insert_of_mem {a : A} {l : list A} : a ∈ l → length (insert a l) = length l :=
assume ainl, by rewrite [insert_eq_of_mem ainl]

theorem length_insert_of_not_mem {a : A} {l : list A} : a ∉ l → length (insert a l) = length l + 1 :=
assume nainl, by rewrite [insert_eq_of_not_mem nainl]
end insert
end list

attribute list.has_decidable_eq  [instance]
attribute list.decidable_mem [instance]
attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
