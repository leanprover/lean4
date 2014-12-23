/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.basic
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura

Basic properties of lists.
-/

import logic tools.helper_tactics data.nat.basic

open eq.ops helper_tactics nat

inductive list (T : Type) : Type :=
nil {} : list T,
cons   : T → list T → list T

namespace list
notation h :: t  := cons h t
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {T : Type}

/- append -/

definition append (s t : list T) : list T :=
rec t (λx l u, x::u) s

notation l₁ ++ l₂ := append l₁ l₂

theorem append.nil_left (t : list T) : nil ++ t = t

theorem append.cons (x : T) (s t : list T) : x::s ++ t = x::(s ++ t)

theorem append.nil_right (t : list T) : t ++ nil = t :=
induction_on t rfl (λx l H, H ▸ rfl)

theorem append.assoc (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
induction_on s rfl (λx l H, H ▸ rfl)

/- length -/

definition length : list T → nat :=
rec 0 (λx l m, succ m)

theorem length.nil : length (@nil T) = 0

theorem length.cons (x : T) (t : list T) : length (x::t) = succ (length t)

theorem length.append (s t : list T) : length (s ++ t) = length s + length t :=
induction_on s (!add.left_id⁻¹) (λx s H, !add.succ_left⁻¹ ▸ H ▸ rfl)

-- add_rewrite length_nil length_cons

/- concat -/

definition concat (x : T) : list T → list T :=
rec [x] (λy l l', y::l')

theorem concat.nil (x : T) : concat x nil = [x]

theorem concat.cons (x y : T) (l : list T) : concat x (y::l)  = y::(concat x l)

theorem concat.eq_append (x : T) (l : list T) : concat x l = l ++ [x]

-- add_rewrite append_nil append_cons

/- reverse -/

definition reverse : list T → list T :=
rec nil (λx l r, r ++ [x])

theorem reverse.nil : reverse (@nil T) = nil

theorem reverse.cons (x : T) (l : list T) : reverse (x::l) = concat x (reverse l)

theorem reverse.singleton (x : T) : reverse [x] = [x]

theorem reverse.append (s t : list T) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
induction_on s (!append.nil_right⁻¹)
  (λx s H, calc
    reverse (x::s ++ t) = reverse t ++ reverse s ++ [x]   : {H}
                    ... = reverse t ++ (reverse s ++ [x]) : !append.assoc)

theorem reverse.reverse (l : list T) : reverse (reverse l) = l :=
induction_on l rfl (λx l' H, H ▸ !reverse.append)

theorem concat.eq_reverse_cons  (x : T) (l : list T) : concat x l = reverse (x :: reverse l) :=
induction_on l rfl
  (λy l' H, calc
    concat x (y::l') = (y::l') ++ [x]                   : !concat.eq_append
                 ... = reverse (reverse (y::l')) ++ [x] : {!reverse.reverse⁻¹})

/- head and tail -/

definition head (x : T) : list T → T :=
rec x (λx l h, x)

theorem head.nil (x : T) : head x nil = x

theorem head.cons (x x' : T) (t : list T) : head x' (x::t) = x

theorem head.concat {s : list T} (t : list T) (x : T) : s ≠ nil → (head x (s ++ t) = head x s) :=
cases_on s
  (take H : nil ≠ nil, absurd rfl H)
  (take x s, take H : x::s ≠ nil,
    calc
      head x (x::s ++ t) = head x (x::(s ++ t)) : {!append.cons}
                     ... = x                    : !head.cons
                     ... = head x (x::s)        : !head.cons⁻¹)

definition tail : list T → list T :=
rec nil (λx l b, l)

theorem tail.nil : tail (@nil T) = nil

theorem tail.cons (x : T) (l : list T) : tail (x::l) = l

theorem cons_head_tail {l : list T} (x : T) : l ≠ nil → (head x l)::(tail l) = l :=
cases_on l
  (assume H : nil ≠ nil, absurd rfl H)
  (take x l, assume H : x::l ≠ nil, rfl)

/- list membership -/

definition mem (x : T) : list T → Prop :=
rec false (λy l H, x = y ∨ H)

notation e ∈ s := mem e s

theorem mem.nil (x : T) : x ∈ nil ↔ false :=
iff.rfl

theorem mem.cons (x y : T) (l : list T) : x ∈ y::l ↔ (x = y ∨ x ∈ l) :=
iff.rfl

theorem mem.concat_imp_or {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
induction_on s or.inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ y::s ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or_of_or_of_imp_right H2 IH,
    iff.elim_right or.assoc H3)

theorem mem.or_imp_concat {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
induction_on s
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

theorem mem.concat (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t :=
iff.intro mem.concat_imp_or mem.or_imp_concat

theorem mem.split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x::t) :=
induction_on l
  (take H : x ∈ nil, false.elim (iff.elim_left !mem.nil H))
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

definition mem.is_decidable [instance] (H : decidable_eq T) (x : T) (l : list T) : decidable (x ∈ l) :=
rec_on l
  (decidable.inr (not_of_iff_false !mem.nil))
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
              iff.elim_right (not_iff_not_of_iff !mem.cons) H1,
            decidable.inr H2)))

/- find -/

section
variable [H : decidable_eq T]
include H

definition find (x : T) : list T → nat :=
rec 0 (λy l b, if x = y then 0 else succ b)

theorem find.nil (x : T) : find x nil = 0

theorem find.cons (x y : T) (l : list T) : find x (y::l) = if x = y then 0 else succ (find x l)

theorem find.not_mem {l : list T} {x : T} : ¬x ∈ l → find x l = length l :=
rec_on l
   (assume P₁ : ¬x ∈ nil, rfl)
   (take y l,
      assume iH : ¬x ∈ l → find x l = length l,
      assume P₁ : ¬x ∈ y::l,
      have P₂ : ¬(x = y ∨ x ∈ l), from iff.elim_right (not_iff_not_of_iff !mem.cons) P₁,
      have P₃ : ¬x = y ∧ ¬x ∈ l, from (iff.elim_left not_or_iff_not_and_not P₂),
      calc
        find x (y::l) = if x = y then 0 else succ (find x l) : !find.cons
                  ... = succ (find x l)                      : if_neg (and.elim_left P₃)
                  ... = succ (length l)                      : {iH (and.elim_right P₃)}
                  ... = length (y::l)                        : !length.cons⁻¹)
end

/- nth element -/

definition nth (x : T) (l : list T) (n : nat) : T :=
nat.rec (λl, head x l) (λm f l, f (tail l)) n l

theorem nth.zero (x : T) (l : list T) : nth x l 0 = head x l

theorem nth.succ (x : T) (l : list T) (n : nat) : nth x l (succ n) = nth x (tail l) n

end list
