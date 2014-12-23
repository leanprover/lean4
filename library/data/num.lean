/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.num
Author: Leonardo de Moura
-/

import logic.eq
open bool

namespace pos_num
  theorem succ_not_is_one (a : pos_num) : is_one (succ a) = ff :=
  induction_on a rfl (take n iH, rfl) (take n iH, rfl)

  theorem pred.succ (a : pos_num) : pred (succ a) = a :=
  rec_on a
    rfl
    (take (n : pos_num) (iH : pred (succ n) = n),
      calc
        pred (succ (bit1 n)) = cond (is_one (succ n)) one (bit1 (pred (succ n))) : rfl
                       ...   = cond ff one (bit1 (pred (succ n)))                : succ_not_is_one
                       ...   = bit1 (pred (succ n))                              : rfl
                       ...   = bit1 n                                            : iH)
    (take (n : pos_num) (iH : pred (succ n) = n), rfl)

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

  theorem mul.one_left (a : pos_num) : one * a = a :=
  rfl

  theorem mul.one_right (a : pos_num) : a * one = a :=
  induction_on a
    rfl
    (take (n : pos_num) (iH : n * one = n),
      calc bit1 n * one = bit0 (n * one) + one : rfl
                   ...  = bit0 n + one         : iH
                   ...  = bit1 n               : add.bit0_one)
    (take (n : pos_num) (iH : n * one = n),
      calc bit0 n * one = bit0 (n * one)       : rfl
                    ... = bit0 n               : iH)

end pos_num
