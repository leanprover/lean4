/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura

Basic properties of lists.
-/
import logic tools.helper_tactics data.nat.order
open eq.ops helper_tactics nat prod function option

inductive list (T : Type) : Type :=
| nil {} : list T
| cons   : T → list T → list T

protected definition list.is_inhabited [instance] (A : Type) : inhabited (list A) :=
inhabited.mk list.nil

namespace list
notation h :: t  := cons h t
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l

variable {T : Type}

lemma cons_ne_nil [simp] (a : T) (l : list T) : a::l ≠ [] :=
by contradiction

lemma head_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

lemma tail_eq_of_cons_eq {A : Type} {h₁ h₂ : A} {t₁ t₂ : list A} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

lemma cons_inj {A : Type} {a : A} : injective (cons a) :=
take l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

/- append -/

definition append : list T → list T → list T
| []       l := l
| (h :: s) t := h :: (append s t)

notation l₁ ++ l₂ := append l₁ l₂

theorem append_nil_left [simp] (t : list T) : [] ++ t = t

theorem append_cons [simp] (x : T) (s t : list T) : (x::s) ++ t = x::(s ++ t)

theorem append_nil_right [simp] : ∀ (t : list T), t ++ [] = t
| []       := rfl
| (a :: l) := calc
  (a :: l) ++ [] = a :: (l ++ []) : rfl
             ... = a :: l         : append_nil_right l

theorem append.assoc [simp] : ∀ (s t u : list T), s ++ t ++ u = s ++ (t ++ u)
| []       t u := rfl
| (a :: l) t u :=
  show a :: (l ++ t ++ u) = (a :: l) ++ (t ++ u),
  by rewrite (append.assoc l t u)

/- length -/
definition length : list T → nat
| []       := 0
| (a :: l) := length l + 1

theorem length_nil [simp] : length (@nil T) = 0

theorem length_cons [simp] (x : T) (t : list T) : length (x::t) = length t + 1

theorem length_append [simp] : ∀ (s t : list T), length (s ++ t) = length s + length t
| []       t := calc
    length ([] ++ t)  = length t : rfl
                   ... = length [] + length t : zero_add
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

theorem concat_nil [simp] (x : T) : concat x [] = [x]

theorem concat_cons [simp] (x y : T) (l : list T) : concat x (y::l)  = y::(concat x l)

theorem concat_eq_append (a : T) : ∀ (l : list T), concat a l = l ++ [a]
| []       := rfl
| (b :: l) :=
  show b :: (concat a l) = (b :: l) ++ (a :: []),
  by rewrite concat_eq_append

theorem concat_ne_nil [simp] (a : T) : ∀ (l : list T), concat a l ≠ [] :=
by intro l; induction l; repeat contradiction

/- last -/

definition last : Π l : list T, l ≠ [] → T
| []          h := absurd rfl h
| [a]         h := a
| (a₁::a₂::l) h := last (a₂::l) !cons_ne_nil

lemma last_singleton [simp] (a : T) (h : [a] ≠ []) : last [a] h = a :=
rfl

lemma last_cons_cons [simp] (a₁ a₂ : T) (l : list T) (h : a₁::a₂::l ≠ []) : last (a₁::a₂::l) h = last (a₂::l) !cons_ne_nil :=
rfl

theorem last_congr {l₁ l₂ : list T} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) : last l₁ h₁ = last l₂ h₂ :=
by subst l₁

theorem last_concat [simp] {x : T} : ∀ {l : list T} (h : concat x l ≠ []), last (concat x l) h = x
| []          h := rfl
| [a]         h := rfl
| (a₁::a₂::l) h :=
  begin
    change last (a₁::a₂::concat x l) !cons_ne_nil = x,
    rewrite last_cons_cons,
    change last (concat x (a₂::l)) !concat_ne_nil = x,
    apply last_concat
  end

-- add_rewrite append_nil append_cons

/- reverse -/

definition reverse : list T → list T
| []       := []
| (a :: l) := concat a (reverse l)

theorem reverse_nil [simp] : reverse (@nil T) = []

theorem reverse_cons [simp] (x : T) (l : list T) : reverse (x::l) = concat x (reverse l)

theorem reverse_singleton [simp] (x : T) : reverse [x] = [x]

theorem reverse_append [simp] : ∀ (s t : list T), reverse (s ++ t) = (reverse t) ++ (reverse s)
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

theorem reverse_reverse [simp] : ∀ (l : list T), reverse (reverse l) = l
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

theorem head_cons [simp] [h : inhabited T] (a : T) (l : list T) : head (a::l) = a

theorem head_append [simp] [h : inhabited T] (t : list T) : ∀ {s : list T}, s ≠ [] → head (s ++ t) = head s
| []       H := absurd rfl H
| (a :: s) H :=
  show head (a :: (s ++ t)) = head (a :: s),
  by  rewrite head_cons

definition tail : list T → list T
| []       := []
| (a :: l) := l

theorem tail_nil [simp] : tail (@nil T) = []

theorem tail_cons [simp] (a : T) (l : list T) : tail (a::l) = l

theorem cons_head_tail [h : inhabited T] {l : list T} : l ≠ [] → (head l)::(tail l) = l :=
list.cases_on l
  (suppose [] ≠ [], absurd rfl this)
  (take x l, suppose x::l ≠ [], rfl)

/- list membership -/

definition mem : T → list T → Prop
| a []       := false
| a (b :: l) := a = b ∨ mem a l

notation e ∈ s := mem e s
notation e ∉ s := ¬ e ∈ s

theorem mem_nil_iff [simp] (x : T) : x ∈ [] ↔ false :=
iff.rfl

theorem not_mem_nil (x : T) : x ∉ [] :=
iff.mp !mem_nil_iff

theorem mem_cons [simp] (x : T) (l : list T) : x ∈ x :: l :=
or.inl rfl

theorem mem_cons_of_mem (y : T) {x : T} {l : list T} : x ∈ l → x ∈ y :: l :=
assume H, or.inr H

theorem mem_cons_iff (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

theorem eq_or_mem_of_mem_cons {x y : T} {l : list T} : x ∈ y::l → x = y ∨ x ∈ l :=
assume h, h

theorem mem_singleton {x a : T} : x ∈ [a] → x = a :=
suppose x ∈ [a], or.elim (eq_or_mem_of_mem_cons this)
  (suppose x = a, this)
  (suppose x ∈ [], absurd this !not_mem_nil)

theorem mem_of_mem_cons_of_mem {a b : T} {l : list T} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (suppose a = b, by substvars; exact binl)
  (suppose a ∈ l, this)

theorem mem_or_mem_of_mem_append {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
list.induction_on s or.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    suppose x ∈ y::s ++ t,
    have x = y ∨ x ∈ s ++ t, from this,
    have x = y ∨ x ∈ s ∨ x ∈ t, from or_of_or_of_imp_right this IH,
    iff.elim_right or.assoc this)

theorem mem_append_of_mem_or_mem {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
list.induction_on s
  (take H, or.elim H false.elim (assume H, H))
  (take y s,
    assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
    suppose x ∈ y::s ∨ x ∈ t,
      or.elim this
        (suppose x ∈ y::s,
          or.elim (eq_or_mem_of_mem_cons this)
            (suppose x = y, or.inl this)
            (suppose x ∈ s, or.inr (IH (or.inl this))))
        (suppose x ∈ t, or.inr (IH (or.inr this))))

theorem mem_append_iff (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

theorem not_mem_of_not_mem_append_left {x : T} {s t : list T} : x ∉ s++t → x ∉ s :=
λ nxinst xins, absurd (mem_append_of_mem_or_mem (or.inl xins)) nxinst

theorem not_mem_of_not_mem_append_right {x : T} {s t : list T} : x ∉ s++t → x ∉ t :=
λ nxinst xint, absurd (mem_append_of_mem_or_mem (or.inr xint)) nxinst

theorem not_mem_append {x : T} {s t : list T} : x ∉ s → x ∉ t → x ∉ s++t :=
λ nxins nxint xinst, or.elim (mem_or_mem_of_mem_append xinst)
  (λ xins, by contradiction)
  (λ xint, by contradiction)

lemma length_pos_of_mem {a : T} : ∀ {l : list T}, a ∈ l → 0 < length l
| []     := assume Pinnil, by contradiction
| (b::l) := assume Pin, !zero_lt_succ

local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
list.induction_on l
  (suppose x ∈ [], false.elim (iff.elim_left !mem_nil_iff this))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    suppose x ∈ y::l,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose x = y,
        exists.intro [] (!exists.intro (this ▸ rfl)))
      (suppose x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x::t)), from IH this,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have y :: l = (y::s) ++ (x::t),
          from H3 ▸ rfl,
        !exists.intro (!exists.intro this)))

theorem mem_append_left {a : T} {l₁ : list T} (l₂ : list T) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (or.inl ainl₁)

theorem mem_append_right {a : T} (l₁ : list T) {l₂ : list T} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (or.inr ainl₂)

definition decidable_mem [instance] [H : decidable_eq T] (x : T) (l : list T) : decidable (x ∈ l) :=
list.rec_on l
  (decidable.inr (not_of_iff_false !mem_nil_iff))
  (take (h : T) (l : list T) (iH : decidable (x ∈ l)),
    show decidable (x ∈ h::l), from
    decidable.rec_on iH
      (assume Hp : x ∈ l,
        decidable.rec_on (H x h)
          (suppose x = h,
            decidable.inl (or.inl this))
          (suppose x ≠ h,
            decidable.inl (or.inr Hp)))
      (suppose ¬x ∈ l,
        decidable.rec_on (H x h)
          (suppose x = h, decidable.inl (or.inl this))
          (suppose x ≠ h,
            have ¬(x = h ∨ x ∈ l), from
              suppose x = h ∨ x ∈ l, or.elim this
                (suppose x = h, by contradiction)
                (suppose x ∈ l,  by contradiction),
            have ¬x ∈ h::l, from
              iff.elim_right (not_iff_not_of_iff !mem_cons_iff) this,
            decidable.inr this)))

theorem mem_of_ne_of_mem {x y : T} {l : list T} (H₁ : x ≠ y) (H₂ : x ∈ y :: l) : x ∈ l :=
or.elim (eq_or_mem_of_mem_cons H₂) (λe, absurd e H₁) (λr, r)

theorem ne_of_not_mem_cons {a b : T} {l : list T} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : T} {l : list T} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

lemma not_mem_cons_of_ne_of_not_mem {x y : T} {l : list T} : x ≠ y → x ∉ l → x ∉ y::l :=
assume P1 P2, not.intro (assume Pxin, absurd (eq_or_mem_of_mem_cons Pxin) (not_or P1 P2))

lemma ne_and_not_mem_of_not_mem_cons {x y : T} {l : list T} : x ∉ y::l → x ≠ y ∧ x ∉ l :=
assume P, and.intro (ne_of_not_mem_cons P) (not_mem_of_not_mem_cons P)

definition sublist (l₁ l₂ : list T) := ∀ ⦃a : T⦄, a ∈ l₁ → a ∈ l₂

infix `⊆` := sublist

theorem nil_sub [simp] (l : list T) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil_iff b) i)

theorem sub.refl [simp] (l : list T) : l ⊆ l :=
λ b i, i

theorem sub.trans {l₁ l₂ l₃ : list T} (H₁ : l₁ ⊆ l₂) (H₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, H₂ (H₁ i)

theorem sub_cons [simp] (a : T) (l : list T) : l ⊆ a::l :=
λ b i, or.inr i

theorem sub_of_cons_sub {a : T} {l₁ l₂ : list T} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s b (mem_cons_of_mem _ i)

theorem cons_sub_cons  {l₁ l₂ : list T} (a : T) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b Hin, or.elim (eq_or_mem_of_mem_cons Hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

theorem sub_append_left [simp] (l₁ l₂ : list T) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inl i)

theorem sub_append_right [simp] (l₁ l₂ : list T) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inr i)

theorem sub_cons_of_sub (a : T) {l₁ l₂ : list T} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (x : T) (i : x ∈ l₁), or.inr (s i)

theorem sub_app_of_sub_left (l l₁ l₂ : list T) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (x : T) (xinl : x ∈ l),
  have x ∈ l₁, from s xinl,
  mem_append_of_mem_or_mem (or.inl this)

theorem sub_app_of_sub_right (l l₁ l₂ : list T) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (x : T) (xinl : x ∈ l),
  have x ∈ l₂, from s xinl,
  mem_append_of_mem_or_mem (or.inr this)

theorem cons_sub_of_sub_of_mem {a : T} {l m : list T} : a ∈ m → l ⊆ m → a::l ⊆ m :=
λ (ainm : a ∈ m) (lsubm : l ⊆ m) (x : T) (xinal : x ∈ a::l), or.elim (eq_or_mem_of_mem_cons xinal)
  (suppose x = a, by substvars; exact ainm)
  (suppose x ∈ l, lsubm this)

theorem app_sub_of_sub_of_sub {l₁ l₂ l : list T} : l₁ ⊆ l → l₂ ⊆ l → l₁++l₂ ⊆ l :=
λ (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) (x : T) (xinl₁l₂ : x ∈ l₁++l₂),
  or.elim (mem_or_mem_of_mem_append xinl₁l₂)
    (suppose x ∈ l₁, l₁subl this)
    (suppose x ∈ l₂, l₂subl this)

/- find -/
section
variable [H : decidable_eq T]
include H

definition find : T → list T → nat
| a []       := 0
| a (b :: l) := if a = b then 0 else succ (find a l)

theorem find_nil [simp] (x : T) : find x [] = 0

theorem find_cons (x y : T) (l : list T) : find x (y::l) = if x = y then 0 else succ (find x l)

theorem find_cons_of_eq {x y : T} (l : list T) : x = y → find x (y::l) = 0 :=
assume e, if_pos e

theorem find_cons_of_ne {x y : T} (l : list T) : x ≠ y → find x (y::l) = succ (find x l) :=
assume n, if_neg n

theorem find_of_not_mem {l : list T} {x : T} : ¬x ∈ l → find x l = length l :=
list.rec_on l
   (suppose ¬x ∈ [], _)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      suppose ¬x ∈ y::l,
      have ¬(x = y ∨ x ∈ l), from iff.elim_right (not_iff_not_of_iff !mem_cons_iff) this,
      have ¬x = y ∧ ¬x ∈ l, from (iff.elim_left not_or_iff_not_and_not this),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : !find_cons
                  ... = succ (find x l)                      : if_neg (and.elim_left this)
                  ... = succ (length l)                      : {iH (and.elim_right this)}
                  ... = length (y::l)                        : !length_cons⁻¹)

lemma find_le_length : ∀ {a} {l : list T}, find a l ≤ length l
| a []        := !le.refl
| a (b::l)    := decidable.rec_on (H a b)
              (assume Peq, by rewrite [find_cons_of_eq l Peq]; exact !zero_le)
              (assume Pne,
                begin
                  rewrite [find_cons_of_ne l Pne, length_cons],
                  apply succ_le_succ, apply find_le_length
                end)

lemma not_mem_of_find_eq_length : ∀ {a} {l : list T}, find a l = length l → a ∉ l
| a []        := assume Peq, !not_mem_nil
| a (b::l)    := decidable.rec_on (H a b)
                (assume Peq, by rewrite [find_cons_of_eq l Peq, length_cons]; contradiction)
                (assume Pne,
                  begin
                    rewrite [find_cons_of_ne l Pne, length_cons, mem_cons_iff],
                    intro Plen, apply (not_or Pne),
                    exact not_mem_of_find_eq_length (succ.inj Plen)
                  end)

lemma find_lt_length {a} {l : list T} (Pin : a ∈ l) : find a l < length l :=
begin
  apply nat.lt_of_le_and_ne,
  apply find_le_length,
  apply not.intro, intro Peq,
  exact absurd Pin (not_mem_of_find_eq_length Peq)
end

end

/- nth element -/
section nth
definition nth : list T → nat → option T
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

theorem nth_zero [simp] (a : T) (l : list T) : nth (a :: l) 0 = some a

theorem nth_succ [simp] (a : T) (l : list T) (n : nat) : nth (a::l) (succ n) = nth l n

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
  (λ aneb : a ≠ b, or.elim (eq_or_mem_of_mem_cons ainbl)
    (λ aeqb : a = b, absurd aeqb aneb)
    (λ ainl : a ∈ l, by rewrite [find_cons_of_ne _ aneb, nth_succ, find_nth ainl]))

definition inth [h : inhabited T] (l : list T) (n : nat) : T :=
match nth l n with
| some a := a
| none   := arbitrary T
end

theorem inth_zero [h : inhabited T] (a : T) (l : list T) : inth (a :: l) 0 = a

theorem inth_succ [h : inhabited T] (a : T) (l : list T) (n : nat) : inth (a::l) (n+1) = inth l n
end nth

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
variable {A : Type}
inductive qeq (a : A) : list A → list A → Prop :=
| qhead : ∀ l, qeq a l (a::l)
| qcons : ∀ (b : A) {l l' : list A}, qeq a l l' → qeq a (b::l) (b::l')

open qeq

notation l' `≈`:50 a `|` l:50 := qeq a l l'

theorem qeq_app : ∀ (l₁ : list A) (a : A) (l₂ : list A), l₁++(a::l₂) ≈ a|l₁++l₂
| []      a l₂ := qhead a l₂
| (x::xs) a l₂ := qcons x (qeq_app xs a l₂)

theorem mem_head_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → a ∈ l₁ :=
take q, qeq.induction_on q
  (λ l, !mem_cons)
  (λ b l l' q r, or.inr r)

theorem mem_tail_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₂ → x ∈ l₁ :=
take q, qeq.induction_on q
  (λ l x i, or.inr i)
  (λ b l l' q r x xinbl, or.elim (eq_or_mem_of_mem_cons xinbl)
     (λ xeqb : x = b, xeqb ▸ mem_cons x l')
     (λ xinl : x ∈ l, or.inr (r x xinl)))

theorem mem_cons_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → ∀ x, x ∈ l₁ → x ∈ a::l₂ :=
take q, qeq.induction_on q
  (λ l x i, i)
  (λ b l l' q r x xinbl', or.elim (eq_or_mem_of_mem_cons xinbl')
    (λ xeqb  : x = b, xeqb ▸ or.inr (mem_cons x l))
    (λ xinl' : x ∈ l', or.elim (eq_or_mem_of_mem_cons (r x xinl'))
      (λ xeqa : x = a, xeqa ▸ mem_cons x (b::l))
      (λ xinl : x ∈ l, or.inr (or.inr xinl))))

theorem length_eq_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → length l₁ = succ (length l₂) :=
take q, qeq.induction_on q
  (λ l, rfl)
  (λ b l l' q r, by rewrite [*length_cons, r])

theorem qeq_of_mem {a : A} {l : list A} : a ∈ l → (∃l', l≈a|l') :=
list.induction_on l
  (λ h : a ∈ nil, absurd h (not_mem_nil a))
  (λ x xs r ainxxs, or.elim (eq_or_mem_of_mem_cons ainxxs)
    (λ aeqx  : a = x,
       assert aux : ∃ l, x::xs≈x|l, from
         exists.intro xs (qhead x xs),
       by rewrite aeqx; exact aux)
    (λ ainxs : a ∈ xs,
       have ∃l', xs ≈ a|l', from r ainxs,
       obtain (l' : list A) (q : xs ≈ a|l'), from this,
       have x::xs ≈ a | x::l', from qcons x q,
       exists.intro (x::l') this))

theorem qeq_split {a : A} {l l' : list A} : l'≈a|l → ∃l₁ l₂, l = l₁++l₂ ∧ l' = l₁++(a::l₂) :=
take q, qeq.induction_on q
  (λ t,
    have t = []++t ∧ a::t = []++(a::t), from and.intro rfl rfl,
    exists.intro [] (exists.intro t this))
  (λ b t t' q r,
    obtain (l₁ l₂ : list A) (h : t = l₁++l₂ ∧ t' = l₁++(a::l₂)), from r,
    have b::t = (b::l₁)++l₂ ∧ b::t' = (b::l₁)++(a::l₂),
      begin
        rewrite [and.elim_right h, and.elim_left h],
        constructor, repeat reflexivity
      end,
    exists.intro (b::l₁) (exists.intro l₂ this))

theorem sub_of_mem_of_sub_of_qeq {a : A} {l : list A} {u v : list A} : a ∉ l → a::l ⊆ v → v≈a|u → l ⊆ u :=
λ (nainl : a ∉ l) (s : a::l ⊆ v) (q : v≈a|u) (x : A) (xinl : x ∈ l),
  have x ∈ v,    from s (or.inr xinl),
  have x ∈ a::u, from mem_cons_of_qeq q x this,
  or.elim (eq_or_mem_of_mem_cons this)
    (suppose x = a, by substvars; contradiction)
    (suppose x ∈ u, this)
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

lemma firstn_all_of_ge : ∀ {n} {l : list A}, n ≥ length l → firstn n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt !succ_pos)
| (n+1) []     h := rfl
| (n+1) (a::l) h := begin unfold firstn, rewrite [firstn_all_of_ge (le_of_succ_le_succ h)] end

lemma firstn_firstn : ∀ (n m) (l : list A), firstn n (firstn m l) = firstn (min n m) l
| n         0        l      := by rewrite [min_zero, firstn_zero, firstn_nil]
| 0         m        l      := by rewrite [zero_min]
| (succ n)  (succ m) nil    := by rewrite [*firstn_nil]
| (succ n)  (succ m) (a::l) := by rewrite [*firstn_cons, firstn_firstn, min_succ_succ]

lemma length_firstn_le : ∀ (n) (l : list A), length (firstn n l) ≤ n
| 0        l      := by rewrite [firstn_zero]
| (succ n) (a::l) := by rewrite [firstn_cons, length_cons, add_one]; apply succ_le_succ; apply length_firstn_le
| (succ n) []     := by rewrite [firstn_nil, length_nil]; apply zero_le

lemma length_firstn_eq : ∀ (n) (l : list A), length (firstn n l) = min n (length l)
| 0        l      := by rewrite [firstn_zero, zero_min]
| (succ n) (a::l) := by rewrite [firstn_cons, *length_cons, *add_one, min_succ_succ, length_firstn_eq]
| (succ n) []     := by rewrite [firstn_nil]
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

lemma count_gt_zero_of_mem : ∀ {a : A} {l : list A}, a ∈ l → count a l > 0
| a []     h := absurd h !not_mem_nil
| a (b::l) h := or.elim h
  (suppose a = b, begin subst b, rewrite count_cons_eq, apply zero_lt_succ end)
  (suppose a ∈ l, calc
   count a (b::l) ≥ count a l : count_cons_ge_count
           ...    > 0         : count_gt_zero_of_mem this)

lemma count_eq_zero_of_not_mem {a : A} {l : list A} (h : a ∉ l) : count a l = 0 :=
match count a l with
| 0        := suppose count a l = 0, this
| (succ n) := suppose count a l = succ n, absurd (mem_of_count_gt_zero (begin rewrite this, exact dec_trivial end)) h
end rfl

end count
end list

attribute list.has_decidable_eq [instance]
attribute list.decidable_mem    [instance]
