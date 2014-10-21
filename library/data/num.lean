----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------
import logic.inhabited data.bool general_notation
open bool

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type :=
one  : pos_num,
bit1 : pos_num → pos_num,
bit0 : pos_num → pos_num

definition pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

namespace pos_num
  protected theorem induction_on {P : pos_num → Prop} (a : pos_num)
      (H₁ : P one) (H₂ : ∀ (n : pos_num), P n → P (bit1 n)) (H₃ : ∀ (n : pos_num), P n → P (bit0 n)) : P a :=
  rec H₁ H₂ H₃ a

  protected definition rec_on {P : pos_num → Type} (a : pos_num)
      (H₁ : P one) (H₂ : ∀ (n : pos_num), P n → P (bit1 n)) (H₃ : ∀ (n : pos_num), P n → P (bit0 n)) : P a :=
  rec H₁ H₂ H₃ a

  definition succ (a : pos_num) : pos_num :=
  rec_on a (bit0 one) (λn r, bit0 r) (λn r, bit1 n)

  definition is_one (a : pos_num) : bool :=
  rec_on a tt (λn r, ff) (λn r, ff)

  definition pred (a : pos_num) : pos_num :=
  rec_on a one (λn r, bit0 n) (λn r, cond (is_one n) one (bit1 r))

  definition size (a : pos_num) : pos_num :=
  rec_on a one (λn r, succ r) (λn r, succ r)

  theorem succ_not_is_one (a : pos_num) : is_one (succ a) = ff :=
  induction_on a rfl (take n iH, rfl) (take n iH, rfl)

  theorem pred.succ (a : pos_num) : pred (succ a) = a :=
  rec_on a
    rfl
    (take (n : pos_num) (iH : pred (succ n) = n),
      calc
        pred (succ (bit1 n)) = cond ff one (bit1 (pred (succ n))) : {!succ_not_is_one}
                       ...   = bit1 (pred (succ n))               : rfl
                       ...   = bit1 n                             : {iH})
    (take (n : pos_num) (iH : pred (succ n) = n), rfl)

  definition add (a b : pos_num) : pos_num :=
  rec_on a
    succ
    (λn f b, rec_on b
      (succ (bit1 n))
      (λm r, succ (bit1 (f m)))
      (λm r, bit1 (f m)))
    (λn f b, rec_on b
      (bit1 n)
      (λm r, bit1 (f m))
      (λm r, bit0 (f m)))
    b

  notation a + b := add a b

  section
  variables (a b : pos_num)

  theorem add.one_one : one + one = bit0 one :=
  rfl

  theorem add.one_bit0 : one + (bit0 a) = bit1 a :=
  rfl

  theorem add.one_bit1 : one + (bit1 a) = succ (bit1 a) :=
  rfl

  theorem add.bit0_one : (bit0 a) + one = bit1 a :=
  rfl

  theorem add.bit1_one : (bit1 a) + one = succ (bit1 a) :=
  rfl

  theorem add.bit0_bit0 : (bit0 a) + (bit0 b) = bit0 (a + b) :=
  rfl

  theorem add.bit0_bit1 : (bit0 a) + (bit1 b) = bit1 (a + b) :=
  rfl

  theorem add.bit1_bit0 : (bit1 a) + (bit0 b) = bit1 (a + b) :=
  rfl

  theorem add.bit1_bit1 : (bit1 a) + (bit1 b) = succ (bit1 (a + b)) :=
  rfl
  end

  definition mul (a b : pos_num) : pos_num :=
  rec_on a
    b
    (λn r, bit0 r + b)
    (λn r, bit0 r)

  notation a * b := mul a b

  theorem mul.one_left (a : pos_num) : one * a = a :=
  rfl

  theorem mul.one_right (a : pos_num) : a * one = a :=
  induction_on a
    rfl
    (take (n : pos_num) (iH : n * one = n),
      calc bit1 n * one = bit0 (n * one) + one : rfl
                   ...  = bit0 n + one : {iH}
                   ...  = bit1 n       : !add.bit0_one)
    (take (n : pos_num) (iH : n * one = n),
      calc bit0 n * one = bit0 (n * one) : rfl
                    ... = bit0 n         : {iH})
end pos_num

inductive num : Type :=
zero  : num,
pos   : pos_num → num

definition num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

namespace num
  open pos_num
  protected theorem induction_on {P : num → Prop} (a : num)
      (H₁ : P zero) (H₂ : ∀ (p : pos_num), P (pos p)) : P a :=
  rec H₁ H₂ a

  protected definition rec_on {P : num → Type} (a : num)
      (H₁ : P zero) (H₂ : ∀ (p : pos_num), P (pos p)) : P a :=
  rec H₁ H₂ a

  definition succ (a : num) : num :=
  rec_on a (pos one) (λp, pos (succ p))

  definition pred (a : num) : num :=
  rec_on a zero (λp, cond (is_one p) zero (pos (pred p)))

  definition size (a : num) : num :=
  rec_on a (pos one) (λp, pos (size p))

  theorem pred.succ (a : num) : pred (succ a) = a :=
  rec_on a
    rfl
    (λp, calc
      pred (succ (pos p)) = pred (pos (pos_num.succ p)) : rfl
                   ...    = cond ff zero (pos (pos_num.pred (pos_num.succ p))) : {!succ_not_is_one}
                   ...    = pos (pos_num.pred (pos_num.succ p)) : !cond.ff
                   ...    = pos p : {!pos_num.pred.succ})

  definition add (a b : num) : num :=
  rec_on a b (λp_a, rec_on b (pos p_a) (λp_b, pos (pos_num.add p_a p_b)))

  definition mul (a b : num) : num :=
  rec_on a zero (λp_a, rec_on b zero (λp_b, pos (pos_num.mul p_a p_b)))

  notation a + b := add a b
  notation a * b := mul a b
end num
