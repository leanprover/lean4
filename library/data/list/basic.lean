----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import tools.tactic
import data.nat
import logic tools.helper_tactics
import logic.core.identities

open nat
open eq_ops
open helper_tactics

inductive list (T : Type) : Type :=
nil {} : list T,
cons   : T → list T → list T

namespace list
infix `::` := cons

section

variable {T : Type}

protected theorem induction_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hind : ∀ (x : T) (l : list T),  P l → P (x::l)) : P l :=
rec Hnil Hind l

protected theorem cases_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hcons : ∀ (x : T) (l : list T), P (x::l)) : P l :=
induction_on l Hnil (take x l IH, Hcons x l)

protected definition rec_on {A : Type} {C : list A → Type} (l : list A)
    (H1 : C nil) (H2 : Π (h : A) (t : list A), C t → C (h::t)) : C l :=
  rec H1 H2 l

notation `[` l:(foldr `,` (h t, h::t) nil) `]` := l


-- Concat
-- ------

definition append (s t : list T) : list T :=
rec t (λx l u, x::u) s

infixl `++` : 65 := append

theorem nil_append {t : list T} : nil ++ t = t

theorem cons_append {x : T} {s t : list T} : x::s ++ t = x::(s ++ t)

theorem append_nil {t : list T} : t ++ nil = t :=
induction_on t rfl (λx l H, H ▸ rfl)

theorem append_assoc {s t u : list T} : s ++ t ++ u = s ++ (t ++ u) :=
induction_on s rfl (λx l H, H ▸ rfl)

-- Length
-- ------

definition length : list T → nat :=
rec 0 (λx l m, succ m)

theorem length_nil : length (@nil T) = 0

theorem length_cons {x : T} {t : list T} : length (x::t) = succ (length t)

theorem length_append {s t : list T} : length (s ++ t) = length s + length t :=
induction_on s (add_zero_left⁻¹) (λx s H, add_succ_left⁻¹ ▸ H ▸ rfl)

-- add_rewrite length_nil length_cons

-- Append
-- ------

definition concat (x : T) : list T → list T :=
rec [x] (λy l l', y::l')

theorem concat_nil {x : T} : concat x nil = [x]

theorem concat_cons {x y : T} {l : list T} : concat x (y::l)  = y::(concat x l)

theorem concat_eq_append  {x : T} {l : list T} : concat x l = l ++ [x]

-- add_rewrite append_nil append_cons

-- Reverse
-- -------

definition reverse : list T → list T :=
rec nil (λx l r, r ++ [x])

theorem reverse_nil : reverse (@nil T) = nil

theorem reverse_cons {x : T} {l : list T} : reverse (x::l) = concat x (reverse l)

theorem reverse_singleton {x : T} : reverse [x] = [x]

theorem reverse_append {s t : list T} : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
induction_on s (append_nil⁻¹)
  (λx s H, calc
    reverse (x::s ++ t) = reverse t ++ reverse s ++ [x]   : {H}
                    ... = reverse t ++ (reverse s ++ [x]) : append_assoc)

theorem reverse_reverse {l : list T} : reverse (reverse l) = l :=
induction_on l rfl (λx l' H, H ▸ reverse_append)

theorem concat_eq_reverse_cons  {x : T} {l : list T} : concat x l = reverse (x :: reverse l) :=
induction_on l rfl
  (λy l' H, calc
    concat x (y::l') = (y::l') ++ [x]                   : concat_eq_append
                 ... = reverse (reverse (y::l')) ++ [x] : {reverse_reverse⁻¹})

-- Head and tail
-- -------------

definition head (x : T) : list T → T :=
rec x (λx l h, x)

theorem head_nil {x : T} : head x nil = x

theorem head_cons {x x' : T} {t : list T} : head x' (x::t) = x

theorem head_concat {s t : list T} {x : T} : s ≠ nil → (head x (s ++ t) = head x s) :=
cases_on s
  (take H : nil ≠ nil, absurd rfl H)
  (take x s, take H : x::s ≠ nil,
    calc
      head x (x::s ++ t) = head x (x::(s ++ t)) : {cons_append}
        ... = x                                 : {head_cons}
        ... = head x (x::s)                     : {head_cons⁻¹})

definition tail : list T → list T :=
rec nil (λx l b, l)

theorem tail_nil : tail (@nil T) = nil

theorem tail_cons {x : T} {l : list T} : tail (x::l) = l

theorem cons_head_tail {x : T} {l : list T} : l ≠ nil → (head x l)::(tail l) = l :=
cases_on l
  (assume H : nil ≠ nil, absurd rfl H)
  (take x l, assume H : x::l ≠ nil, rfl)

-- List membership
-- ---------------

definition mem (x : T) : list T → Prop :=
rec false (λy l H, x = y ∨ H)

infix `∈` := mem

theorem mem_nil {x : T} : x ∈ nil ↔ false :=
iff.rfl

theorem mem_cons {x y : T} {l : list T} : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

theorem mem_concat_imp_or {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
induction_on s or.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ y::s ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or.imp_or_right H2 IH,
    iff.elim_right or.assoc H3)

theorem mem_or_imp_concat {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
induction_on s
  (take H, or.elim H false_elim (assume H, H))
  (take y s,
    assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
    assume H : x ∈ y::s ∨ x ∈ t,
      or.elim H
        (assume H1,
          or.elim H1
            (take H2 : x = y, or.inl H2)
            (take H2 : x ∈ s, or.inr (IH (or.inl H2))))
        (assume H1 : x ∈ t, or.inr (IH (or.inr H1))))

theorem mem_concat {x : T} {s t : list T} : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem_concat_imp_or mem_or_imp_concat

theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
induction_on l
  (take H : x ∈ nil, false_elim (iff.elim_left mem_nil H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim H
      (assume H1 : x = y,
        exists_intro nil (exists_intro l (H1 ▸ rfl)))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x::t)), from IH H1,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have H4 : y :: l = (y::s) ++ (x::t),
          from H3 ▸ rfl,
        exists_intro _ (exists_intro _ H4)))

definition mem_is_decidable [instance] {H : decidable_eq T} {x : T} {l : list T} : decidable (x ∈ l) :=
rec_on l
  (decidable.inr (iff.false_elim mem_nil))
  (λ (h : T) (l : list T) (iH : decidable (x ∈ l)),
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
              iff.elim_right (iff.flip_sign mem_cons) H1,
            decidable.inr H2)))

-- Find
-- ----

definition find {H : decidable_eq T} (x : T) : list T → nat :=
rec 0 (λy l b, if x = y then 0 else succ b)

theorem find_nil {H : decidable_eq T} {f : T} : find f nil = 0

theorem find_cons {H : decidable_eq T} {x y : T} {l : list T} :
    find x (y::l) = if x = y then 0 else succ (find x l)

theorem not_mem_find {H : decidable_eq T} {l : list T} {x : T} :
     ¬x ∈ l → find x l = length l :=
rec_on l
   (assume P₁ : ¬x ∈ nil, rfl)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      assume P₁ : ¬x ∈ y::l,
      have P₂ : ¬(x = y ∨ x ∈ l), from iff.elim_right (iff.flip_sign mem_cons) P₁,
      have P₃ : ¬x = y ∧ ¬x ∈ l, from (iff.elim_left not_or P₂),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : find_cons
                  ... = succ (find x l)                      : if_neg (and.elim_left P₃)
                  ... = succ (length l)                      : {iH (and.elim_right P₃)}
                  ... = length (y::l)                        : length_cons⁻¹)

-- nth element
-- -----------

definition nth (x : T) (l : list T) (n : nat) : T :=
nat.rec (λl, head x l) (λm f l, f (tail l)) n l

theorem nth_zero {x : T} {l : list T} : nth x l 0 = head x l

theorem nth_succ {x : T} {l : list T} {n : nat} : nth x l (succ n) = nth x (tail l) n
end
end list
