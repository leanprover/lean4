/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.basic
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura

Basic properties of lists.
-/
import logic tools.helper_tactics data.nat.basic

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

theorem mem_nil (x : T) : x ∈ [] ↔ false :=
iff.rfl

theorem mem_cons (x : T) (l : list T) : x ∈ x :: l :=
or.inl rfl

theorem mem_cons_iff (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

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
          or.elim H1
            (take H2 : x = y, or.inl H2)
            (take H2 : x ∈ s, or.inr (IH (or.inl H2))))
        (assume H1 : x ∈ t, or.inr (IH (or.inr H1))))

theorem mem_append_iff (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
list.induction_on l
  (take H : x ∈ [], false.elim (iff.elim_left !mem_nil H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim H
      (assume H1 : x = y,
        exists.intro [] (!exists.intro (H1 ▸ rfl)))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x::t)), from IH H1,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have H4 : y :: l = (y::s) ++ (x::t),
          from H3 ▸ rfl,
        !exists.intro (!exists.intro H4)))

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
or.elim H₂ (λe, absurd e H₁) (λr, r)

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
λ b Hin, or.elim Hin
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

lemma sub_append_left (l₁ l₂ : list T) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mp' (mem_append_iff b l₁ l₂) (or.inl i)

lemma sub_append_right (l₁ l₂ : list T) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mp' (mem_append_iff b l₁ l₂) (or.inr i)

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
definition decidable_eq {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ = l₂)
| []      []      := inl rfl
| []      (b::l₂) := inr (λ H, list.no_confusion H)
| (a::l₁) []      := inr (λ H, list.no_confusion H)
| (a::l₁) (b::l₂) :=
  match H a b with
  | inl Hab  :=
    match decidable_eq l₁ l₂ with
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

theorem map_map (g : B → C) (f : A → B) : ∀ l : list A, map g (map f l) = map (g ∘ f) l
| []       := rfl
| (a :: l) :=
  show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
  by rewrite (map_map l)

theorem len_map (f : A → B) : ∀ l : list A, length (map f l) = length l
| []       := rfl
| (a :: l) :=
  show length (map f l) + 1 = length l + 1,
  by rewrite (len_map l)

definition map₂ (f : A → B → C) : list A → list B → list C
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

definition foldl (f : A → B → A) : A → list B → A
| a []       := a
| a (b :: l) := foldl (f a b) l

definition foldr (f : A → B → B) : B → list A → B
| b []       := b
| b (a :: l) := f a (foldr b l)

section foldl_eq_foldr
  -- foldl and foldr coincide when f is commutative and associative
  parameters {α : Type} {f : α → α → α}
  hypothesis (Hcomm  : ∀ a b, f a b = f b a)
  hypothesis (Hassoc : ∀ a b c, f a (f b c) = f (f a b) c)
  include Hcomm Hassoc

  theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
  | a b  nil    := Hcomm a b
  | a b  (c::l) :=
    begin
      change (foldl f (f (f a b) c) l = f b (foldl f (f a c) l)),
      rewrite -foldl_eq_of_comm_of_assoc,
      change (foldl f (f (f a b) c) l = foldl f (f (f a c) b) l),
      have H₁ : f (f a b) c = f (f a c) b, by rewrite [-Hassoc, -Hassoc, Hcomm b c],
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
   unzip ((a, b) :: l) = match unzip l with (la, lb) := (a :: la, b :: lb) end

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
variable {A : Type}

definition flat (l : list (list A)) : list A :=
foldl append nil l

end list

attribute list.decidable_eq  [instance]
attribute list.decidable_mem [instance]
attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
