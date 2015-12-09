/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

Basic properties of lists.
Ported from the standard library (list.basic and list.comb)
Some lemmas are commented out, their proofs need to be repaired when needed
-/

import .pointed .nat .pi

open eq lift nat is_trunc pi pointed sum function prod option sigma algebra

inductive list (T : Type) : Type :=
| nil {} : list T
| cons   : T → list T → list T

definition pointed_list [instance] (A : Type) : pointed (list A) :=
pointed.mk list.nil

namespace list
notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

universe variable u
variable {T : Type.{u}}

lemma cons_ne_nil (a : T) (l : list T) : a::l ≠ [] :=
by contradiction

lemma head_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, down (list.no_confusion Peq (assume Pheq Pteq, Pheq))

lemma tail_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, down (list.no_confusion Peq (assume Pheq Pteq, Pteq))

/- append -/

definition append : list T → list T → list T
| []       l := l
| (h :: s) t := h :: (append s t)

notation l₁ ++ l₂ := append l₁ l₂

theorem append_nil_left (t : list T) : [] ++ t = t := idp

theorem append_cons (x : T) (s t : list T) : (x::s) ++ t = x :: (s ++ t) := idp

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

theorem length_nil : length (@nil T) = 0 := idp

theorem length_cons (x : T) (t : list T) : length (x::t) = length t + 1 := idp

theorem length_append : ∀ (s t : list T), length (s ++ t) = length s + length t
| []       t := calc
    length ([] ++ t)  = length t             : rfl
                  ... = length [] + length t : by rewrite [length_nil, zero_add]
| (a :: s) t := calc
    length (a :: s ++ t) = length (s ++ t) + 1        : rfl
                    ...  = length s + length t + 1    : length_append
                    ...  = (length s + 1) + length t  : succ_add
                    ...  = length (a :: s) + length t : rfl

theorem eq_nil_of_length_eq_zero : ∀ {l : list T}, length l = 0 → l = []
| []     H := rfl
| (a::s) H := by contradiction

theorem ne_nil_of_length_eq_succ : ∀ {l : list T} {n : nat}, length l = succ n → l ≠ []
| []     n h := by contradiction
| (a::l) n h := by contradiction

-- add_rewrite length_nil length_cons

/- concat -/

definition concat : Π (x : T), list T → list T
| a []       := [a]
| a (b :: l) := b :: concat a l

theorem concat_nil (x : T) : concat x [] = [x] := idp

theorem concat_cons (x y : T) (l : list T) : concat x (y::l)  = y::(concat x l) := idp

theorem concat_eq_append (a : T) : ∀ (l : list T), concat a l = l ++ [a]
| []       := rfl
| (b :: l) :=
  show b :: (concat a l) = (b :: l) ++ (a :: []),
  by rewrite concat_eq_append

theorem concat_ne_nil (a : T) : ∀ (l : list T), concat a l ≠ [] :=
by intro l; induction l; repeat contradiction

theorem length_concat (a : T) : ∀ (l : list T), length (concat a l) = length l + 1
| []      := rfl
| (x::xs) := by rewrite [concat_cons, *length_cons, length_concat]

theorem concat_append (a : T) : ∀ (l₁ l₂ : list T), concat a l₁ ++ l₂ = l₁ ++ a :: l₂
| []      := λl₂, rfl
| (x::xs) := λl₂, begin rewrite [concat_cons,append_cons, concat_append] end

theorem append_concat (a : T)  : ∀(l₁ l₂ : list T), l₁ ++ concat a l₂ = concat a (l₁ ++ l₂)
| []      := λl₂, rfl
| (x::xs) := λl₂, begin rewrite [+append_cons, concat_cons, append_concat] end

/- last -/

definition last : Π l : list T, l ≠ [] → T
| []          h := absurd rfl h
| [a]         h := a
| (a₁::a₂::l) h := last (a₂::l) !cons_ne_nil

lemma last_singleton (a : T) (h : [a] ≠ []) : last [a] h = a :=
rfl

lemma last_cons_cons (a₁ a₂ : T) (l : list T) (h : a₁::a₂::l ≠ [])
  : last (a₁::a₂::l) h = last (a₂::l) !cons_ne_nil :=
rfl

theorem last_congr {l₁ l₂ : list T} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂)
  : last l₁ h₁ = last l₂ h₂ :=
apd011 last h₃ !is_hprop.elim

theorem last_concat {x : T} : ∀ {l : list T} (h : concat x l ≠ []), last (concat x l) h = x
| []          h := rfl
| [a]         h := rfl
| (a₁::a₂::l) h :=
  begin
    change last (a₁::a₂::concat x l) !cons_ne_nil = x,
    rewrite last_cons_cons,
    change last (concat x (a₂::l)) (cons_ne_nil a₂ (concat x l)) = x,
    apply last_concat
  end

-- add_rewrite append_nil append_cons

/- reverse -/

definition reverse : list T → list T
| []       := []
| (a :: l) := concat a (reverse l)

theorem reverse_nil : reverse (@nil T) = [] := idp

theorem reverse_cons (x : T) (l : list T) : reverse (x::l) = concat x (reverse l) := idp

theorem reverse_singleton (x : T) : reverse [x] = [x] := idp

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

theorem length_reverse : ∀ (l : list T), length (reverse l) = length l
| []      := rfl
| (x::xs) := begin unfold reverse, rewrite [length_concat, length_cons, length_reverse] end

/- head and tail -/

definition head [h : pointed T] : list T → T
| []       := pt
| (a :: l) := a

theorem head_cons [h : pointed T] (a : T) (l : list T) : head (a::l) = a := idp

theorem head_append [h : pointed T] (t : list T) : ∀ {s : list T}, s ≠ [] → head (s ++ t) = head s
| []       H := absurd rfl H
| (a :: s) H :=
  show head (a :: (s ++ t)) = head (a :: s),
  by  rewrite head_cons

definition tail : list T → list T
| []       := []
| (a :: l) := l

theorem tail_nil : tail (@nil T) = [] := idp

theorem tail_cons (a : T) (l : list T) : tail (a::l) = l := idp

theorem cons_head_tail [h : pointed T] {l : list T} : l ≠ [] → (head l)::(tail l) = l :=
list.cases_on l
  (suppose [] ≠ [], absurd rfl this)
  (take x l, suppose x::l ≠ [], rfl)

/- list membership -/

definition mem : T → list T → Type.{u}
| a []       := lift empty
| a (b :: l) := a = b ⊎ mem a l

notation e ∈ s := mem e s
notation e ∉ s := ¬ e ∈ s

theorem mem_nil_iff (x : T) : x ∈ [] ↔ empty :=
iff.intro down up

theorem not_mem_nil (x : T) : x ∉ [] :=
iff.mp !mem_nil_iff

theorem mem_cons (x : T) (l : list T) : x ∈ x :: l :=
sum.inl rfl

theorem mem_cons_of_mem (y : T) {x : T} {l : list T} : x ∈ l → x ∈ y :: l :=
assume H, sum.inr H

theorem mem_cons_iff (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ⊎ x ∈ l) :=
iff.rfl

theorem eq_or_mem_of_mem_cons {x y : T} {l : list T} : x ∈ y::l → x = y ⊎ x ∈ l :=
assume h, h

theorem mem_singleton {x a : T} : x ∈ [a] → x = a :=
suppose x ∈ [a], sum.rec_on (eq_or_mem_of_mem_cons this)
  (suppose x = a, this)
  (suppose x ∈ [], absurd this !not_mem_nil)

theorem mem_of_mem_cons_of_mem {a b : T} {l : list T} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, sum.rec_on (eq_or_mem_of_mem_cons ainbl)
  (suppose a = b, by substvars; exact binl)
  (suppose a ∈ l, this)

theorem mem_or_mem_of_mem_append {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ⊎ x ∈ t :=
list.rec_on s sum.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ⊎ x ∈ t,
    suppose x ∈ y::s ++ t,
    have x = y ⊎ x ∈ s ++ t, from this,
    have x = y ⊎ x ∈ s ⊎ x ∈ t, from sum_of_sum_of_imp_right this IH,
    iff.elim_right sum.assoc this)

theorem mem_append_of_mem_or_mem {x : T} {s t : list T} : (x ∈ s ⊎ x ∈ t) → x ∈ s ++ t :=
list.rec_on s
  (take H, sum.rec_on H (empty.elim ∘ down) (assume H, H))
  (take y s,
    assume IH : (x ∈ s ⊎ x ∈ t) → x ∈ s ++ t,
    suppose x ∈ y::s ⊎ x ∈ t,
      sum.rec_on this
        (suppose x ∈ y::s,
          sum.rec_on (eq_or_mem_of_mem_cons this)
            (suppose x = y, sum.inl this)
            (suppose x ∈ s, sum.inr (IH (sum.inl this))))
        (suppose x ∈ t, sum.inr (IH (sum.inr this))))

theorem mem_append_iff (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ⊎ x ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

theorem not_mem_of_not_mem_append_left {x : T} {s t : list T} : x ∉ s++t → x ∉ s :=
λ nxinst xins, absurd (mem_append_of_mem_or_mem (sum.inl xins)) nxinst

theorem not_mem_of_not_mem_append_right {x : T} {s t : list T} : x ∉ s++t → x ∉ t :=
λ nxinst xint, absurd (mem_append_of_mem_or_mem (sum.inr xint)) nxinst

theorem not_mem_append {x : T} {s t : list T} : x ∉ s → x ∉ t → x ∉ s++t :=
λ nxins nxint xinst, sum.rec_on (mem_or_mem_of_mem_append xinst)
  (λ xins, by contradiction)
  (λ xint, by contradiction)

lemma length_pos_of_mem {a : T} : ∀ {l : list T}, a ∈ l → 0 < length l
| []     := assume Pinnil, by induction Pinnil; contradiction
| (b::l) := assume Pin, !zero_lt_succ

local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → Σs t : list T, l = s ++ (x::t) :=
list.rec_on l
  (suppose x ∈ [], empty.elim (iff.elim_left !mem_nil_iff this))
  (take y l,
    assume IH : x ∈ l → Σs t : list T, l = s ++ (x::t),
    suppose x ∈ y::l,
    sum.rec_on (eq_or_mem_of_mem_cons this)
      (suppose x = y,
        sigma.mk [] (!sigma.mk (this ▸ rfl)))
      (suppose x ∈ l,
        obtain s (H2 : Σt : list T, l = s ++ (x::t)), from IH this,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have y :: l = (y::s) ++ (x::t),
          from H3 ▸ rfl,
        !sigma.mk (!sigma.mk this)))

theorem mem_append_left {a : T} {l₁ : list T} (l₂ : list T) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (sum.inl ainl₁)

theorem mem_append_right {a : T} (l₁ : list T) {l₂ : list T} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (sum.inr ainl₂)

definition decidable_mem [instance] [H : decidable_eq T] (x : T) (l : list T) : decidable (x ∈ l) :=
list.rec_on l
  (decidable.inr begin intro x, induction x, contradiction end)
  (take (h : T) (l : list T) (iH : decidable (x ∈ l)),
    show decidable (x ∈ h::l), from
    decidable.rec_on iH
      (assume Hp : x ∈ l,
        decidable.rec_on (H x h)
          (suppose x = h,
            decidable.inl (sum.inl this))
          (suppose x ≠ h,
            decidable.inl (sum.inr Hp)))
      (suppose ¬x ∈ l,
        decidable.rec_on (H x h)
          (suppose x = h, decidable.inl (sum.inl this))
          (suppose x ≠ h,
            have ¬(x = h ⊎ x ∈ l), from
              suppose x = h ⊎ x ∈ l, sum.rec_on this
                (suppose x = h, by contradiction)
                (suppose x ∈ l,  by contradiction),
            have ¬x ∈ h::l, from
              iff.elim_right (not_iff_not_of_iff !mem_cons_iff) this,
            decidable.inr this)))

theorem mem_of_ne_of_mem {x y : T} {l : list T} (H₁ : x ≠ y) (H₂ : x ∈ y :: l) : x ∈ l :=
sum.rec_on (eq_or_mem_of_mem_cons H₂) (λe, absurd e H₁) (λr, r)

theorem ne_of_not_mem_cons {a b : T} {l : list T} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (sum.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : T} {l : list T} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (sum.inr nainl) nin

lemma not_mem_cons_of_ne_of_not_mem {x y : T} {l : list T} : x ≠ y → x ∉ l → x ∉ y::l :=
assume P1 P2, not.intro (assume Pxin, absurd (eq_or_mem_of_mem_cons Pxin) (not_sum P1 P2))

lemma ne_and_not_mem_of_not_mem_cons {x y : T} {l : list T} : x ∉ y::l → x ≠ y × x ∉ l :=
assume P, prod.mk (ne_of_not_mem_cons P) (not_mem_of_not_mem_cons P)

definition sublist (l₁ l₂ : list T) := ∀ ⦃a : T⦄, a ∈ l₁ → a ∈ l₂

infix ⊆ := sublist

theorem nil_sub (l : list T) : [] ⊆ l :=
λ b i, empty.elim (iff.mp (mem_nil_iff b) i)

theorem sub.refl (l : list T) : l ⊆ l :=
λ b i, i

theorem sub.trans {l₁ l₂ l₃ : list T} (H₁ : l₁ ⊆ l₂) (H₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, H₂ (H₁ i)

theorem sub_cons (a : T) (l : list T) : l ⊆ a::l :=
λ b i, sum.inr i

theorem sub_of_cons_sub {a : T} {l₁ l₂ : list T} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s b (mem_cons_of_mem _ i)

theorem cons_sub_cons  {l₁ l₂ : list T} (a : T) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b Hin, sum.rec_on (eq_or_mem_of_mem_cons Hin)
  (λ e : b = a,  sum.inl e)
  (λ i : b ∈ l₁, sum.inr (s i))

theorem sub_append_left (l₁ l₂ : list T) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (sum.inl i)

theorem sub_append_right (l₁ l₂ : list T) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (sum.inr i)

theorem sub_cons_of_sub (a : T) {l₁ l₂ : list T} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (x : T) (i : x ∈ l₁), sum.inr (s i)

theorem sub_app_of_sub_left (l l₁ l₂ : list T) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (x : T) (xinl : x ∈ l),
  have x ∈ l₁, from s xinl,
  mem_append_of_mem_or_mem (sum.inl this)

theorem sub_app_of_sub_right (l l₁ l₂ : list T) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (x : T) (xinl : x ∈ l),
  have x ∈ l₂, from s xinl,
  mem_append_of_mem_or_mem (sum.inr this)

theorem cons_sub_of_sub_of_mem {a : T} {l m : list T} : a ∈ m → l ⊆ m → a::l ⊆ m :=
λ (ainm : a ∈ m) (lsubm : l ⊆ m) (x : T) (xinal : x ∈ a::l), sum.rec_on (eq_or_mem_of_mem_cons xinal)
  (suppose x = a, by substvars; exact ainm)
  (suppose x ∈ l, lsubm this)

theorem app_sub_of_sub_of_sub {l₁ l₂ l : list T} : l₁ ⊆ l → l₂ ⊆ l → l₁++l₂ ⊆ l :=
λ (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) (x : T) (xinl₁l₂ : x ∈ l₁++l₂),
  sum.rec_on (mem_or_mem_of_mem_append xinl₁l₂)
    (suppose x ∈ l₁, l₁subl this)
    (suppose x ∈ l₂, l₂subl this)

/- find -/
section
variable [H : decidable_eq T]
include H

definition find : T → list T → nat
| a []       := 0
| a (b :: l) := if a = b then 0 else succ (find a l)

theorem find_nil (x : T) : find x [] = 0 := idp

theorem find_cons (x y : T) (l : list T) : find x (y::l) = if x = y then 0 else succ (find x l) :=
idp

theorem find_cons_of_eq {x y : T} (l : list T) : x = y → find x (y::l) = 0 :=
assume e, if_pos e

theorem find_cons_of_ne {x y : T} (l : list T) : x ≠ y → find x (y::l) = succ (find x l) :=
assume n, if_neg n

/-theorem find_of_not_mem {l : list T} {x : T} : ¬x ∈ l → find x l = length l :=
list.rec_on l
   (suppose ¬x ∈ [], _)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      suppose ¬x ∈ y::l,
      have ¬(x = y ⊎ x ∈ l), from iff.elim_right (not_iff_not_of_iff !mem_cons_iff) this,
      have ¬x = y × ¬x ∈ l, from (iff.elim_left not_sum_iff_not_prod_not this),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : !find_cons
                  ... = succ (find x l)                      : if_neg (prod.pr1 this)
                  ... = succ (length l)                      : {iH (prod.pr2 this)}
                  ... = length (y::l)                        : !length_cons⁻¹)-/

lemma find_le_length : ∀ {a} {l : list T}, find a l ≤ length l
| a []        := !le.refl
| a (b::l)    := decidable.rec_on (H a b)
              (assume Peq, by rewrite [find_cons_of_eq l Peq]; exact !zero_le)
              (assume Pne,
                begin
                  rewrite [find_cons_of_ne l Pne, length_cons],
                  apply succ_le_succ, apply find_le_length
                end)

/-lemma not_mem_of_find_eq_length : ∀ {a} {l : list T}, find a l = length l → a ∉ l
| a []        := assume Peq, !not_mem_nil
| a (b::l)    := decidable.rec_on (H a b)
                (assume Peq, by rewrite [find_cons_of_eq l Peq, length_cons]; contradiction)
                (assume Pne,
                  begin
                    rewrite [find_cons_of_ne l Pne, length_cons, mem_cons_iff],
                    intro Plen, apply (not_or Pne),
                    exact not_mem_of_find_eq_length (succ.inj Plen)
                  end)-/

/-lemma find_lt_length {a} {l : list T} (Pin : a ∈ l) : find a l < length l :=
begin
  apply nat.lt_of_le_prod_ne,
  apply find_le_length,
  apply not.intro, intro Peq,
  exact absurd Pin (not_mem_of_find_eq_length Peq)
end-/

end

/- nth element -/
section nth
definition nth : list T → nat → option T
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

theorem nth_zero (a : T) (l : list T) : nth (a :: l) 0 = some a := idp

theorem nth_succ (a : T) (l : list T) (n : nat) : nth (a::l) (succ n) = nth l n := idp

theorem nth_eq_some : ∀ {l : list T} {n : nat}, n < length l → Σ a : T, nth l n = some a
| []     n        h := absurd h !not_lt_zero
| (a::l) 0        h := ⟨a, rfl⟩
| (a::l) (succ n) h :=
  have n < length l,                       from lt_of_succ_lt_succ h,
  obtain (r : T) (req : nth l n = some r), from nth_eq_some this,
  ⟨r, by rewrite [nth_succ, req]⟩

open decidable
theorem find_nth [h : decidable_eq T] {a : T} : ∀ {l}, a ∈ l → nth l (find a l) = some a
| []     ain   := absurd ain !not_mem_nil
| (b::l) ainbl := by_cases
  (λ aeqb : a = b, by rewrite [find_cons_of_eq _ aeqb, nth_zero, aeqb])
  (λ aneb : a ≠ b, sum.rec_on (eq_or_mem_of_mem_cons ainbl)
    (λ aeqb : a = b, absurd aeqb aneb)
    (λ ainl : a ∈ l, by rewrite [find_cons_of_ne _ aneb, nth_succ, find_nth ainl]))

definition inth [h : pointed T] (l : list T) (n : nat) : T :=
match nth l n with
| some a := a
| none   := pt
end

theorem inth_zero [h : pointed T] (a : T) (l : list T) : inth (a :: l) 0 = a := idp

theorem inth_succ [h : pointed T] (a : T) (l : list T) (n : nat) : inth (a::l) (n+1) = inth l n :=
idp
end nth

section ith
definition ith : Π (l : list T) (i : nat), i < length l → T
| nil     i        h := absurd h !not_lt_zero
| (x::xs) 0        h := x
| (x::xs) (succ i) h := ith xs i (lt_of_succ_lt_succ h)

lemma ith_zero (a : T) (l : list T) (h : 0 < length (a::l)) : ith (a::l) 0 h = a :=
rfl

lemma ith_succ (a : T) (l : list T) (i : nat) (h : succ i < length (a::l))
                      : ith (a::l) (succ i) h = ith l i (lt_of_succ_lt_succ h) :=
rfl
end ith

open decidable
definition has_decidable_eq {A : Type} [H : decidable_eq A] : ∀ l₁ l₂ : list A, decidable (l₁ = l₂)
| []      []      := inl rfl
| []      (b::l₂) := inr (by contradiction)
| (a::l₁) []      := inr (by contradiction)
| (a::l₁) (b::l₂) :=
  match H a b with
  | inl Hab  :=
    match has_decidable_eq l₁ l₂ with
    | inl He := inl (by congruence; repeat assumption)
    | inr Hn := inr (by intro H; injection H; contradiction)
    end
  | inr Hnab := inr (by intro H; injection H; contradiction)
  end

/- quasiequal a l l' means that l' is exactly l, with a added
   once somewhere -/
section qeq
variable {A : Type.{u}}
inductive qeq (a : A) : list A → list A → Type.{u} :=
| qhead : ∀ l, qeq a l (a::l)
| qcons : ∀ (b : A) {l l' : list A}, qeq a l l' → qeq a (b::l) (b::l')

open qeq

notation l' `≈`:50 a `|` l:50 := qeq a l l'

theorem qeq_app : ∀ (l₁ : list A) (a : A) (l₂ : list A), l₁++(a::l₂) ≈ a|l₁++l₂
| []      a l₂ := qhead a l₂
| (x::xs) a l₂ := qcons x (qeq_app xs a l₂)

theorem mem_head_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → a ∈ l₁ :=
take q, qeq.rec_on q
  (λ l, !mem_cons)
  (λ b l l' q r, sum.inr r)

theorem mem_tail_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₂ → x ∈ l₁ :=
take q, qeq.rec_on q
  (λ l x i, sum.inr i)
  (λ b l l' q r x xinbl, sum.rec_on (eq_or_mem_of_mem_cons xinbl)
     (λ xeqb : x = b, xeqb ▸ mem_cons x l')
     (λ xinl : x ∈ l, sum.inr (r x xinl)))

/-
theorem mem_cons_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₁ → x ∈ a::l₂ :=
take q, qeq.rec_on q
  (λ l x i, i)
  (λ b l l' q r x xinbl', sum.elim_on (eq_or_mem_of_mem_cons xinbl')
    (λ xeqb  : x = b, xeqb ▸ sum.inr (mem_cons x l))
    (λ xinl' : x ∈ l', sum.rec_on (eq_or_mem_of_mem_cons (r x xinl'))
      (λ xeqa : x = a, xeqa ▸ mem_cons x (b::l))
      (λ xinl : x ∈ l, sum.inr (sum.inr xinl))))-/

theorem length_eq_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → length l₁ = succ (length l₂) :=
take q, qeq.rec_on q
  (λ l, rfl)
  (λ b l l' q r, by rewrite [*length_cons, r])

theorem qeq_of_mem {a : A} {l : list A} : a ∈ l → (Σl', l≈a|l') :=
list.rec_on l
  (λ h : a ∈ nil, absurd h (not_mem_nil a))
  (λ x xs r ainxxs, sum.rec_on (eq_or_mem_of_mem_cons ainxxs)
    (λ aeqx  : a = x,
       assert aux : Σ l, x::xs≈x|l, from
         sigma.mk xs (qhead x xs),
       by rewrite aeqx; exact aux)
    (λ ainxs : a ∈ xs,
       have Σl', xs ≈ a|l', from r ainxs,
       obtain (l' : list A) (q : xs ≈ a|l'), from this,
       have x::xs ≈ a | x::l', from qcons x q,
       sigma.mk (x::l') this))

theorem qeq_split {a : A} {l l' : list A} : l'≈a|l → Σl₁ l₂, l = l₁++l₂ × l' = l₁++(a::l₂) :=
take q, qeq.rec_on q
  (λ t,
    have t = []++t × a::t = []++(a::t), from prod.mk rfl rfl,
    sigma.mk [] (sigma.mk t this))
  (λ b t t' q r,
    obtain (l₁ l₂ : list A) (h : t = l₁++l₂ × t' = l₁++(a::l₂)), from r,
    have b::t = (b::l₁)++l₂ × b::t' = (b::l₁)++(a::l₂),
      begin
        rewrite [prod.pr2 h, prod.pr1 h],
        constructor, repeat reflexivity
      end,
    sigma.mk (b::l₁) (sigma.mk l₂ this))

/-theorem sub_of_mem_of_sub_of_qeq {a : A} {l : list A} {u v : list A} : a ∉ l → a::l ⊆ v → v≈a|u → l ⊆ u :=
λ (nainl : a ∉ l) (s : a::l ⊆ v) (q : v≈a|u) (x : A) (xinl : x ∈ l),
  have x ∈ v,    from s (sum.inr xinl),
  have x ∈ a::u, from mem_cons_of_qeq q x this,
  sum.rec_on (eq_or_mem_of_mem_cons this)
    (suppose x = a, by substvars; contradiction)
    (suppose x ∈ u, this)-/
end qeq

section firstn
variable {A : Type}

definition firstn : nat → list A → list A
| 0     l      := []
| (n+1) []     := []
| (n+1) (a::l) := a :: firstn n l

lemma firstn_zero : ∀ (l : list A), firstn 0 l = [] :=
by intros; reflexivity

lemma firstn_nil : ∀ n, firstn n [] = ([] : list A)
| 0     := rfl
| (n+1) := rfl

lemma firstn_cons : ∀ n (a : A) (l : list A), firstn (succ n) (a::l) = a :: firstn n l :=
by intros; reflexivity

lemma firstn_all : ∀ (l : list A), firstn (length l) l = l
| []     := rfl
| (a::l) := begin unfold [length, firstn], rewrite firstn_all end

/-lemma firstn_all_of_ge : ∀ {n} {l : list A}, n ≥ length l → firstn n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt !succ_pos)
| (n+1) []     h := rfl
| (n+1) (a::l) h := begin unfold firstn, rewrite [firstn_all_of_ge (le_of_succ_le_succ h)] end-/

/-lemma firstn_firstn : ∀ (n m) (l : list A), firstn n (firstn m l) = firstn (min n m) l
| n         0        l      := by rewrite [min_zero, firstn_zero, firstn_nil]
| 0         m        l      := by rewrite [zero_min]
| (succ n)  (succ m) nil    := by rewrite [*firstn_nil]
| (succ n)  (succ m) (a::l) := by rewrite [*firstn_cons, firstn_firstn, min_succ_succ]-/

lemma length_firstn_le : ∀ (n) (l : list A), length (firstn n l) ≤ n
| 0        l      := by rewrite [firstn_zero]
| (succ n) (a::l) := by rewrite [firstn_cons, length_cons, add_one]; apply succ_le_succ; apply length_firstn_le
| (succ n) []     := by rewrite [firstn_nil, length_nil]; apply zero_le

/-lemma length_firstn_eq : ∀ (n) (l : list A), length (firstn n l) = min n (length l)
| 0        l      := by rewrite [firstn_zero, zero_min]
| (succ n) (a::l) := by rewrite [firstn_cons, *length_cons, *add_one, min_succ_succ, length_firstn_eq]
| (succ n) []     := by rewrite [firstn_nil]-/
end firstn

section count
variable {A : Type}
variable [decA : decidable_eq A]
include decA

definition count (a : A) : list A → nat
| []      := 0
| (x::xs) := if a = x then succ (count xs) else count xs

lemma count_nil (a : A) : count a [] = 0 :=
rfl

lemma count_cons (a b : A) (l : list A) : count a (b::l) = if a = b then succ (count a l) else count a l :=
rfl

lemma count_cons_eq (a : A) (l : list A) : count a (a::l) = succ (count a l) :=
if_pos rfl

lemma count_cons_of_ne {a b : A} (h : a ≠ b) (l : list A) : count a (b::l) = count a l :=
if_neg h

lemma count_cons_ge_count (a b : A) (l : list A) : count a (b::l) ≥ count a l :=
by_cases
  (suppose a = b, begin subst b, rewrite count_cons_eq, apply le_succ end)
  (suppose a ≠ b, begin rewrite (count_cons_of_ne this), apply le.refl end)

lemma count_singleton (a : A) : count a [a] = 1 :=
by rewrite count_cons_eq

lemma count_append (a : A) : ∀ l₁ l₂, count a (l₁++l₂) = count a l₁ + count a l₂
| []      l₂ := by rewrite [append_nil_left, count_nil, zero_add]
| (b::l₁) l₂ := by_cases
  (suppose a = b, by rewrite [-this, append_cons, *count_cons_eq, succ_add, count_append])
  (suppose a ≠ b, by rewrite [append_cons, *count_cons_of_ne this, count_append])

lemma count_concat (a : A) (l : list A) : count a (concat a l) = succ (count a l) :=
by rewrite [concat_eq_append, count_append, count_singleton]

lemma mem_of_count_gt_zero : ∀ {a : A} {l : list A}, count a l > 0 → a ∈ l
| a []     h := absurd h !lt.irrefl
| a (b::l) h := by_cases
  (suppose a = b, begin subst b, apply mem_cons end)
  (suppose a ≠ b,
   have count a l > 0, by rewrite [count_cons_of_ne this at h]; exact h,
   have a ∈ l,    from mem_of_count_gt_zero this,
   show a ∈ b::l, from mem_cons_of_mem _ this)

/-lemma count_gt_zero_of_mem : ∀ {a : A} {l : list A}, a ∈ l → count a l > 0
| a []     h := absurd h !not_mem_nil
| a (b::l) h := sum.rec_on h
  (suppose a = b, begin subst b, rewrite count_cons_eq, apply zero_lt_succ end)
  (suppose a ∈ l, calc
   count a (b::l) ≥ count a l : count_cons_ge_count
           ...    > 0         : count_gt_zero_of_mem this)-/

/-lemma count_eq_zero_of_not_mem {a : A} {l : list A} (h : a ∉ l) : count a l = 0 :=
match count a l with
| zero     := suppose count a l = zero, this
| (succ n) := suppose count a l = succ n, absurd (mem_of_count_gt_zero (begin rewrite this, exact dec_trivial end)) h
end rfl-/

end count
end list

attribute list.has_decidable_eq [instance]
--attribute list.decidable_mem    [instance]

namespace list

variables {A B C : Type}
/- map -/
definition map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

theorem map_nil (f : A → B) : map f [] = [] := idp

theorem map_cons (f : A → B) (a : A) (l : list A) : map f (a :: l) = f a :: map f l := idp

lemma map_concat (f : A → B) (a : A) : Πl, map f (concat a l) = concat (f a) (map f l)
| nil    := rfl
| (b::l) := begin rewrite [concat_cons, +map_cons, concat_cons, map_concat] end

lemma map_append (f : A → B) : Π l₁ l₂, map f (l₁++l₂) = (map f l₁)++(map f l₂)
| nil    := take l, rfl
| (a::l) := take l', begin rewrite [append_cons, *map_cons, append_cons, map_append] end

lemma map_reverse (f : A → B) : Πl, map f (reverse l) = reverse (map f l)
| nil    := rfl
| (b::l) := begin rewrite [reverse_cons, +map_cons, reverse_cons, map_concat, map_reverse] end

lemma map_singleton (f : A → B) (a : A) : map f [a] = [f a] := rfl

theorem map_id : Π l : list A, map id l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, map_id] end

theorem map_id' {f : A → A} (H : Πx, f x = x) : Π l : list A, map f l = l
| []      := rfl
| (x::xs) := begin rewrite [map_cons, H, map_id'] end

theorem map_map (g : B → C) (f : A → B) : Π l, map g (map f l) = map (g ∘ f) l
| []       := rfl
| (a :: l) :=
  show (g ∘ f) a :: map g (map f l) = map (g ∘ f) (a :: l),
  by rewrite (map_map l)

theorem length_map (f : A → B) : Π l : list A, length (map f l) = length l
| []       := by esimp
| (a :: l) :=
  show length (map f l) + 1 = length l + 1,
  by rewrite (length_map l)

theorem mem_map {A B : Type} (f : A → B) : Π {a l}, a ∈ l → f a ∈ map f l
| a []      i := absurd i !not_mem_nil
| a (x::xs) i := sum.rec_on (eq_or_mem_of_mem_cons i)
   (suppose a = x, by rewrite [this, map_cons]; apply mem_cons)
   (suppose a ∈ xs, sum.inr (mem_map this))

theorem exists_of_mem_map {A B : Type} {f : A → B} {b : B} :
    Π{l}, b ∈ map f l → Σa, a ∈ l × f a = b
| []     H := empty.elim (down H)
| (c::l) H := sum.rec_on (iff.mp !mem_cons_iff H)
                (suppose b = f c,
                  sigma.mk c (pair !mem_cons (inverse this)))
                (suppose b ∈ map f l,
                  obtain a (Hl : a ∈ l) (Hr : f a = b), from exists_of_mem_map this,
                  sigma.mk a (pair (mem_cons_of_mem _ Hl) Hr))

theorem eq_of_map_const {A B : Type} {b₁ b₂ : B} : Π {l : list A}, b₁ ∈ map (const A b₂) l → b₁ = b₂
| []     h := absurd h !not_mem_nil
| (a::l) h :=
  sum.rec_on (eq_or_mem_of_mem_cons h)
    (suppose b₁ = b₂, this)
    (suppose b₁ ∈ map (const A b₂) l, eq_of_map_const this)

definition map₂ (f : A → B → C) : list A → list B → list C
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

/- filter -/
definition filter (p : A → Type) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

theorem filter_nil (p : A → Type) [h : decidable_pred p] : filter p [] = [] := idp

theorem filter_cons_of_pos {p : A → Type} [h : decidable_pred p] {a : A} : Π l, p a → filter p (a::l) = a :: filter p l :=
λ l pa, if_pos pa

theorem filter_cons_of_neg {p : A → Type} [h : decidable_pred p] {a : A} : Π l, ¬ p a → filter p (a::l) = filter p l :=
λ l pa, if_neg pa

/-
theorem of_mem_filter {p : A → Type} [h : decidable_pred p] {a : A} : Π {l}, a ∈ filter p l → p a
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (assume pb  : p b,
    have a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    sum.rec_on (eq_or_mem_of_mem_cons this)
      (suppose a = b, by rewrite [-this at pb]; exact pb)
      (suppose a ∈ filter p l, of_mem_filter this))
  (suppose ¬ p b, by rewrite [filter_cons_of_neg _ this at ain]; exact (of_mem_filter ain))

theorem mem_of_mem_filter {p : A → Type} [h : decidable_pred p] {a : A} : Π {l}, a ∈ filter p l → a ∈ l
| []     ain := absurd ain !not_mem_nil
| (b::l) ain := by_cases
  (λ pb  : p b,
    have a ∈ b :: filter p l, by rewrite [filter_cons_of_pos _ pb at ain]; exact ain,
    sum.rec_on (eq_or_mem_of_mem_cons this)
      (suppose a = b, by rewrite this; exact !mem_cons)
      (suppose a ∈ filter p l, mem_cons_of_mem _ (mem_of_mem_filter this)))
  (suppose ¬ p b, by rewrite [filter_cons_of_neg _ this at ain]; exact (mem_cons_of_mem _ (mem_of_mem_filter ain)))

theorem mem_filter_of_mem {p : A → Type} [h : decidable_pred p] {a : A} : Π {l}, a ∈ l → p a → a ∈ filter p l
| []     ain pa := absurd ain !not_mem_nil
| (b::l) ain pa := by_cases
  (λ pb  : p b, sum.rec_on (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, by rewrite [filter_cons_of_pos _ pb, aeqb]; exact !mem_cons)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_pos _ pb]; exact (mem_cons_of_mem _ (mem_filter_of_mem ainl pa))))
  (λ npb : ¬ p b, sum.rec_on (eq_or_mem_of_mem_cons ain)
    (λ aeqb : a = b, absurd (eq.rec_on aeqb pa) npb)
    (λ ainl : a ∈ l, by rewrite [filter_cons_of_neg _ npb]; exact (mem_filter_of_mem ainl pa)))

theorem filter_sub {p : A → Type} [h : decidable_pred p] (l : list A) : filter p l ⊆ l :=
λ a ain, mem_of_mem_filter ain

theorem filter_append {p : A → Type} [h : decidable_pred p] : Π (l₁ l₂ : list A), filter p (l₁++l₂) = filter p l₁ ++ filter p l₂
| []      l₂ := rfl
| (a::l₁) l₂ := by_cases
  (suppose p a, by rewrite [append_cons, *filter_cons_of_pos _ this, filter_append])
  (suppose ¬ p a, by rewrite [append_cons, *filter_cons_of_neg _ this, filter_append])
-/

/- foldl & foldr -/
definition foldl (f : A → B → A) : A → list B → A
| a []       := a
| a (b :: l) := foldl (f a b) l

theorem foldl_nil (f : A → B → A) (a : A) : foldl f a [] = a := idp

theorem foldl_cons (f : A → B → A) (a : A) (b : B) (l : list B) : foldl f a (b::l) = foldl f (f a b) l := idp

definition foldr (f : A → B → B) : B → list A → B
| b []       := b
| b (a :: l) := f a (foldr b l)

theorem foldr_nil (f : A → B → B) (b : B) : foldr f b [] = b := idp

theorem foldr_cons (f : A → B → B) (b : B) (a : A) (l : list A) : foldr f b (a::l) = f a (foldr f b l) := idp

section foldl_eq_foldr
  -- foldl and foldr coincide when f is commutative and associative
  parameters {α : Type} {f : α → α → α}
  hypothesis (Hcomm  : Π a b, f a b = f b a)
  hypothesis (Hassoc : Π a b c, f (f a b) c = f a (f b c))
  include Hcomm Hassoc

  theorem foldl_eq_of_comm_of_assoc : Π a b l, foldl f a (b::l) = f b (foldl f a l)
  | a b  nil    := Hcomm a b
  | a b  (c::l) :=
    begin
      change foldl f (f (f a b) c) l = f b (foldl f (f a c) l),
      rewrite -foldl_eq_of_comm_of_assoc,
      change foldl f (f (f a b) c) l = foldl f (f (f a c) b) l,
      have H₁ : f (f a b) c = f (f a c) b, by rewrite [Hassoc, Hassoc, Hcomm b c],
      rewrite H₁
    end

  theorem foldl_eq_foldr : Π a l, foldl f a l = foldr f a l
  | a nil      := rfl
  | a (b :: l) :=
    begin
      rewrite foldl_eq_of_comm_of_assoc,
      esimp,
      change f b (foldl f a l) = f b (foldr f a l),
      rewrite foldl_eq_foldr
    end
end foldl_eq_foldr

theorem foldl_append (f : B → A → B) : Π (b : B) (l₁ l₂ : list A), foldl f b (l₁++l₂) = foldl f (foldl f b l₁) l₂
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldl_cons, foldl_append]

theorem foldr_append (f : A → B → B) : Π (b : B) (l₁ l₂ : list A), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by rewrite [append_cons, *foldr_cons, foldr_append]

end list
