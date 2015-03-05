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
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {T : Type}

/- append -/

definition append : list T → list T → list T
| append nil l      := l
| append (h :: s) t := h :: (append s t)

notation l₁ ++ l₂ := append l₁ l₂

theorem append_nil_left (t : list T) : nil ++ t = t

theorem append_cons (x : T) (s t : list T) : (x::s) ++ t = x::(s ++ t)

theorem append_nil_right : ∀ (t : list T), t ++ nil = t
| append_nil_right nil      := rfl
| append_nil_right (a :: l) := calc
  (a :: l) ++ nil = a :: (l ++ nil) : rfl
              ... = a :: l          : append_nil_right l


theorem append.assoc : ∀ (s t u : list T), s ++ t ++ u = s ++ (t ++ u)
| append.assoc nil t u      := rfl
| append.assoc (a :: l) t u :=
  show a :: (l ++ t ++ u) = (a :: l) ++ (t ++ u),
  by rewrite (append.assoc l t u)

/- length -/

definition length : list T → nat
| length nil      := 0
| length (a :: l) := length l + 1

theorem length_nil : length (@nil T) = 0

theorem length_cons (x : T) (t : list T) : length (x::t) = length t + 1

theorem length_append : ∀ (s t : list T), length (s ++ t) = length s + length t
| length_append nil t      := calc
    length (nil ++ t)  = length t : rfl
                   ... = length nil + length t : zero_add
| length_append (a :: s) t := calc
    length (a :: s ++ t) = length (s ++ t) + 1        : rfl
                    ...  = length s + length t + 1    : length_append
                    ...  = (length s + 1) + length t  : add.succ_left
                    ...  = length (a :: s) + length t : rfl

-- add_rewrite length_nil length_cons

/- concat -/

definition concat : Π (x : T), list T → list T
| concat a nil      := [a]
| concat a (b :: l) := b :: concat a l

theorem concat_nil (x : T) : concat x nil = [x]

theorem concat_cons (x y : T) (l : list T) : concat x (y::l)  = y::(concat x l)

theorem concat_eq_append (a : T) : ∀ (l : list T), concat a l = l ++ [a]
| concat_eq_append nil      := rfl
| concat_eq_append (b :: l) :=
  show b :: (concat a l) = (b :: l) ++ (a :: nil),
  by rewrite concat_eq_append

-- add_rewrite append_nil append_cons

/- reverse -/

definition reverse : list T → list T
| reverse nil      := nil
| reverse (a :: l) := concat a (reverse l)

theorem reverse_nil : reverse (@nil T) = nil

theorem reverse_cons (x : T) (l : list T) : reverse (x::l) = concat x (reverse l)

theorem reverse_singleton (x : T) : reverse [x] = [x]

theorem reverse_append : ∀ (s t : list T), reverse (s ++ t) = (reverse t) ++ (reverse s)
| reverse_append nil t2      := calc
    reverse (nil ++ t2) = reverse t2                    : rfl
                 ...    = (reverse t2) ++ nil           : append_nil_right
                 ...    = (reverse t2) ++ (reverse nil) : {reverse_nil⁻¹}
| reverse_append (a2 :: s2) t2 := calc
    reverse ((a2 :: s2) ++ t2) = concat a2 (reverse (s2 ++ t2))         : rfl
                        ...    = concat a2 (reverse t2 ++ reverse s2)   : reverse_append
                        ...    = (reverse t2 ++ reverse s2) ++ [a2]     : concat_eq_append
                        ...    = reverse t2 ++ (reverse s2 ++ [a2])     : append.assoc
                        ...    = reverse t2 ++ concat a2 (reverse s2)   : concat_eq_append
                        ...    = reverse t2 ++ reverse (a2 :: s2)       : rfl

theorem reverse_reverse : ∀ (l : list T), reverse (reverse l) = l
| reverse_reverse nil      := rfl
| reverse_reverse (a :: l) := calc
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
| head nil      := arbitrary T
| head (a :: l) := a

theorem head_cons [h : inhabited T] (a : T) (l : list T) : head (a::l) = a

theorem head_concat [h : inhabited T] (t : list T) : ∀ {s : list T}, s ≠ nil → head (s ++ t) = head s
| @head_concat nil      H := absurd rfl H
| @head_concat (a :: s) H :=
  show head (a :: (s ++ t)) = head (a :: s),
  by  rewrite head_cons

definition tail : list T → list T
| tail nil      := nil
| tail (a :: l) := l

theorem tail_nil : tail (@nil T) = nil

theorem tail_cons (a : T) (l : list T) : tail (a::l) = l

theorem cons_head_tail [h : inhabited T] {l : list T} : l ≠ nil → (head l)::(tail l) = l :=
list.cases_on l
  (assume H : nil ≠ nil, absurd rfl H)
  (take x l, assume H : x::l ≠ nil, rfl)

/- list membership -/

definition mem : T → list T → Prop
| mem a nil      := false
| mem a (b :: l) := a = b ∨ mem a l

notation e ∈ s := mem e s

theorem mem_nil (x : T) : x ∈ nil ↔ false :=
iff.rfl

theorem mem_cons (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

theorem mem_concat_imp_or {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
list.induction_on s or.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ y::s ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or_of_or_of_imp_right H2 IH,
    iff.elim_right or.assoc H3)

theorem mem_or_imp_concat {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
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

theorem mem_concat (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem_concat_imp_or mem_or_imp_concat

local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
list.induction_on l
  (take H : x ∈ nil, false.elim (iff.elim_left !mem_nil H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim H
      (assume H1 : x = y,
        exists.intro nil (!exists.intro (H1 ▸ rfl)))
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
              iff.elim_right (not_iff_not_of_iff !mem_cons) H1,
            decidable.inr H2)))

/- find -/

section
variable [H : decidable_eq T]
include H

definition find : T → list T → nat
| find a nil      := 0
| find a (b :: l) := if a = b then 0 else succ (find a l)

theorem find_nil (x : T) : find x nil = 0

theorem find_cons (x y : T) (l : list T) : find x (y::l) = if x = y then 0 else succ (find x l)

theorem find.not_mem {l : list T} {x : T} : ¬x ∈ l → find x l = length l :=
list.rec_on l
   (assume P₁ : ¬x ∈ nil, _)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      assume P₁ : ¬x ∈ y::l,
      have P₂ : ¬(x = y ∨ x ∈ l), from iff.elim_right (not_iff_not_of_iff !mem_cons) P₁,
      have P₃ : ¬x = y ∧ ¬x ∈ l, from (iff.elim_left not_or_iff_not_and_not P₂),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : !find_cons
                  ... = succ (find x l)                      : if_neg (and.elim_left P₃)
                  ... = succ (length l)                      : {iH (and.elim_right P₃)}
                  ... = length (y::l)                        : !length_cons⁻¹)
end

/- nth element -/

definition nth [h : inhabited T] : list T → nat → T
| nth nil      n     := arbitrary T
| nth (a :: l) 0     := a
| nth (a :: l) (n+1) := nth l n

theorem nth_zero [h : inhabited T] (a : T) (l : list T) : nth (a :: l) 0 = a

theorem nth_succ [h : inhabited T] (a : T) (l : list T) (n : nat) : nth (a::l) (n+1) = nth l n

open decidable
definition decidable_eq {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ = l₂)
| decidable_eq nil     nil     := inl rfl
| decidable_eq nil     (b::l₂) := inr (λ H, list.no_confusion H)
| decidable_eq (a::l₁) nil     := inr (λ H, list.no_confusion H)
| decidable_eq (a::l₁) (b::l₂) :=
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
| map nil      := nil
| map (a :: l) := f a :: map l

theorem map_nil (f : A → B) : map f nil = nil

theorem map_cons (f : A → B) (a : A) (l : list A) : map f (a :: l) = f a :: map f l

theorem map_map (g : B → C) (f : A → B) : ∀ l : list A, map g (map f l) = map (g ∘ f) l
| map_map nil      := rfl
| map_map (a :: l) :=
  show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
  by rewrite (map_map l)

theorem len_map (f : A → B) : ∀ l : list A, length (map f l) = length l
| len_map nil      := rfl
| len_map (a :: l) :=
  show length (map f l) + 1 = length l + 1,
  by rewrite (len_map l)

definition foldl (f : A → B → A) : A → list B → A
| foldl a nil      := a
| foldl a (b :: l) := foldl (f a b) l

definition foldr (f : A → B → B) : B → list A → B
| foldr b nil      := b
| foldr b (a :: l) := f a (foldr b l)

definition all (p : A → Prop) : list A → Prop
| all nil      := true
| all (a :: l) := p a ∧ all l

definition any (p : A → Prop) : list A → Prop
| any nil      := false
| any (a :: l) := p a ∨ any l

definition decidable_all (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (all p l)
| decidable_all nil      := decidable_true
| decidable_all (a :: l) :=
  match H a with
  | inl Hp₁ :=
    match decidable_all l with
    | inl Hp₂ := inl (and.intro Hp₁ Hp₂)
    | inr Hn₂ := inr (not_and_of_not_right (p a) Hn₂)
    end
  | inr Hn := inr (not_and_of_not_left (all p l) Hn)
  end

definition decidable_any (p : A → Prop) [H : decidable_pred p] : ∀ l, decidable (any p l)
| decidable_any nil      := decidable_false
| decidable_any (a :: l) :=
  match H a with
  | inl Hp := inl (or.inl Hp)
  | inr Hn₁ :=
    match decidable_any l with
    | inl Hp₂ := inl (or.inr Hp₂)
    | inr Hn₂ := inr (not_or Hn₁ Hn₂)
    end
  end

definition zip : list A → list B → list (A × B)
| zip nil       _         := nil
| zip _         nil       := nil
| zip (a :: la) (b :: lb) := (a, b) :: zip la lb

definition unzip : list (A × B) → list A × list B
| unzip nil           := (nil, nil)
| unzip ((a, b) :: l) :=
  match unzip l with
  | (la, lb) := (a :: la, b :: lb)
  end

theorem unzip_nil : unzip (@nil (A × B)) = (nil, nil)

theorem unzip_cons (a : A) (b : B) (l : list (A × B)) :
   unzip ((a, b) :: l) = match unzip l with (la, lb) := (a :: la, b :: lb) end

theorem zip_unzip : ∀ (l : list (A × B)), zip (pr₁ (unzip l)) (pr₂ (unzip l)) = l
| zip_unzip nil           := rfl
| zip_unzip ((a, b) :: l) :=
  begin
    rewrite unzip_cons,
    have r : zip (pr₁ (unzip l)) (pr₂ (unzip l)) = l, from zip_unzip l,
    revert r,
    apply (prod.cases_on (unzip l)),
    intros (la, lb, r),
    rewrite -r
  end

end combinators

end list

attribute list.decidable_eq  [instance]
attribute list.decidable_mem [instance]
attribute list.decidable_any [instance]
attribute list.decidable_all [instance]
