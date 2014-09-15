----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------
import logic.classes.inhabited data.bool
open bool

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type :=
one  : pos_num,
bit1 : pos_num → pos_num,
bit0 : pos_num → pos_num

theorem pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

namespace pos_num
  theorem induction_on [protected] {P : pos_num → Prop} (a : pos_num)
      (H₁ : P one) (H₂ : ∀ (n : pos_num), P n → P (bit1 n)) (H₃ : ∀ (n : pos_num), P n → P (bit0 n)) : P a :=
  rec H₁ H₂ H₃ a

  abbreviation rec_on [protected] {P : pos_num → Type} (a : pos_num)
      (H₁ : P one) (H₂ : ∀ (n : pos_num), P n → P (bit1 n)) (H₃ : ∀ (n : pos_num), P n → P (bit0 n)) : P a :=
  rec H₁ H₂ H₃ a

  abbreviation succ (a : pos_num) : pos_num :=
  rec_on a (bit0 one) (λn r, bit0 r) (λn r, bit1 n)

  abbreviation is_one (a : pos_num) : bool :=
  rec_on a tt (λn r, ff) (λn r, ff)

  abbreviation pred (a : pos_num) : pos_num :=
  rec_on a one (λn r, bit0 n) (λn r, cond (is_one n) one (bit1 r))

  abbreviation size (a : pos_num) : pos_num :=
  rec_on a one (λn r, succ r) (λn r, succ r)

  theorem succ_not_is_one {a : pos_num} : is_one (succ a) = ff :=
  induction_on a rfl (take n iH, rfl) (take n iH, rfl)

  theorem pred_succ {a : pos_num} : pred (succ a) = a :=
  rec_on a
    rfl
    (take (n : pos_num) (iH : pred (succ n) = n),
      calc
        pred (succ (bit1 n)) = cond ff one (bit1 (pred (succ n))) : {succ_not_is_one}
                       ...   = bit1 (pred (succ n))               : rfl
                       ...   = bit1 n                             : {iH})
    (take (n : pos_num) (iH : pred (succ n) = n), rfl)
end pos_num

inductive num : Type :=
zero  : num,
pos   : pos_num → num

theorem num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

namespace num
  open pos_num
  theorem induction_on [protected] {P : num → Prop} (a : num)
      (H₁ : P zero) (H₂ : ∀ (p : pos_num), P (pos p)) : P a :=
  rec H₁ H₂ a

  abbreviation rec_on [protected] {P : num → Type} (a : num)
      (H₁ : P zero) (H₂ : ∀ (p : pos_num), P (pos p)) : P a :=
  rec H₁ H₂ a

  abbreviation succ (a : num) : num :=
  rec_on a (pos one) (λp, pos (succ p))

  abbreviation pred (a : num) : num :=
  rec_on a zero (λp, cond (is_one p) zero (pos (pred p)))

  abbreviation size (a : num) : num :=
  rec_on a (pos one) (λp, pos (size p))

  theorem pred_succ (a : num) : pred (succ a) = a :=
  rec_on a
    rfl
    (λp, calc
      pred (succ (pos p)) = pred (pos (pos_num.succ p)) : rfl
                   ...    = cond ff zero (pos (pos_num.pred (pos_num.succ p))) : {succ_not_is_one}
                   ...    = pos (pos_num.pred (pos_num.succ p)) : cond_ff _ _
                   ...    = pos p : {pos_num.pred_succ})
end num
