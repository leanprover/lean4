/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.num
Authors: Leonardo de Moura
-/

prelude
import init.logic init.bool
open bool

definition pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

namespace pos_num
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

  definition lt (a b : pos_num) : bool :=
  pos_num.rec_on a
    (λ b, pos_num.cases_on b
      ff
      (λm, tt)
      (λm, tt))
    (λn f b, pos_num.cases_on b
      ff
      (λm, f m)
      (λm, f m))
    (λn f b, pos_num.cases_on b
      ff
      (λm, f (succ m))
      (λm, f m))
    b

  definition le (a b : pos_num) : bool :=
  lt a (succ b)

  definition equal (a b : pos_num) : bool :=
  le a b && le b a

end pos_num

definition num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

namespace num
  open pos_num

  definition pred (a : num) : num :=
  num.rec_on a zero (λp, cond (is_one p) zero (pos (pred p)))

  definition size (a : num) : num :=
  num.rec_on a (pos one) (λp, pos (size p))

  definition add (a b : num) : num :=
  num.rec_on a b (λpa, num.rec_on b (pos pa) (λpb, pos (pos_num.add pa pb)))

  definition mul (a b : num) : num :=
  num.rec_on a zero (λpa, num.rec_on b zero (λpb, pos (pos_num.mul pa pb)))

  notation a + b := add a b
  notation a * b := mul a b

  definition le (a b : num) : bool :=
  num.rec_on a tt (λpa, num.rec_on b ff (λpb, pos_num.le pa pb))

  private definition psub (a b : pos_num) : num :=
  pos_num.rec_on a
    (λb, zero)
    (λn f b,
      cond (pos_num.le (bit1 n) b)
        zero
        (pos_num.cases_on b
           (pos (bit0 n))
           (λm, 2 * f m)
           (λm, 2 * f m + 1)))
    (λn f b,
      cond (pos_num.le (bit0 n) b)
        zero
        (pos_num.cases_on b
           (pos (pos_num.pred (bit0 n)))
           (λm, pred (2 * f m))
           (λm, 2 * f m)))
    b

  definition sub (a b : num) : num :=
  num.rec_on a zero (λpa, num.rec_on b a (λpb, psub pa pb))

  notation a ≤ b := le a b
  notation a - b := sub a b
end num

-- the coercion from num to nat is defined here,
-- so that it can already be used in init.trunc and init.tactic
namespace nat
  definition add (a b : nat) : nat :=
  nat.rec_on b a (λ b₁ r, succ r)

  notation a + b := add a b

  definition of_num [coercion] (n : num) : nat :=
  num.rec zero
    (λ n, pos_num.rec (succ zero) (λ n r, r + r + (succ zero)) (λ n r, r + r) n) n
end nat
attribute nat.of_num [reducible] [constructor] -- of_num is also reducible if namespace "nat" is not opened
