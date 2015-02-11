/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.logic init.bool
open bool

definition pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

namespace pos_num
  definition succ (a : pos_num) : pos_num :=
  pos_num.rec_on a (bit0 one) (λn r, bit0 r) (λn r, bit1 n)

  definition is_one (a : pos_num) : bool :=
  pos_num.rec_on a tt (λn r, ff) (λn r, ff)

  definition pred (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λn r, bit0 n) (λn r, cond (is_one n) one (bit1 r))

  definition size (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λn r, succ r) (λn r, succ r)

  definition add (a b : pos_num) : pos_num :=
  pos_num.rec_on a
    succ
    (λn f b, pos_num.rec_on b
      (succ (bit1 n))
      (λm r, succ (bit1 (f m)))
      (λm r, bit1 (f m)))
    (λn f b, pos_num.rec_on b
      (bit1 n)
      (λm r, bit1 (f m))
      (λm r, bit0 (f m)))
    b

  notation a + b := add a b

  definition mul (a b : pos_num) : pos_num :=
  pos_num.rec_on a
    b
    (λn r, bit0 r + b)
    (λn r, bit0 r)

  notation a * b := mul a b

end pos_num

definition num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

namespace num
  open pos_num
  definition succ (a : num) : num :=
  num.rec_on a (pos one) (λp, pos (succ p))

  definition pred (a : num) : num :=
  num.rec_on a zero (λp, cond (is_one p) zero (pos (pred p)))

  definition size (a : num) : num :=
  num.rec_on a (pos one) (λp, pos (size p))

  definition add (a b : num) : num :=
  num.rec_on a b (λp_a, num.rec_on b (pos p_a) (λp_b, pos (pos_num.add p_a p_b)))

  definition mul (a b : num) : num :=
  num.rec_on a zero (λp_a, num.rec_on b zero (λp_b, pos (pos_num.mul p_a p_b)))

  notation a + b := add a b
  notation a * b := mul a b
end num
