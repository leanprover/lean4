/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.bool

namespace pos_num
  protected definition mul (a b : pos_num) : pos_num :=
  pos_num.rec_on a
    b
    (λ n r, bit0 r + b)
    (λ n r, bit0 r)

  definition lt (a b : pos_num) : bool :=
  pos_num.rec_on a
    (λ b, pos_num.cases_on b
      ff
      (λ m, tt)
      (λ m, tt))
    (λ n f b, pos_num.cases_on b
      ff
      (λ m, f m)
      (λ m, f m))
    (λ n f b, pos_num.cases_on b
      ff
      (λ m, f (succ m))
      (λ m, f m))
    b

  definition le (a b : pos_num) : bool :=
  pos_num.lt a (succ b)
end pos_num

instance : has_mul pos_num :=
⟨pos_num.mul⟩

namespace num
  open pos_num

  definition pred (a : num) : num :=
  num.rec_on a zero (λ p, bool.cond (is_one p) zero (pos (pred p)))

  definition size (a : num) : num :=
  num.rec_on a (pos pos_num.one) (λ p, pos (size p))

  protected definition mul (a b : num) : num :=
  num.rec_on a zero (λ pa, num.rec_on b zero (λ pb, pos (pos_num.mul pa pb)))
end num

instance : has_mul num :=
⟨num.mul⟩

namespace num
  protected definition le (a b : num) : bool :=
  num.rec_on a tt (λ pa, num.rec_on b ff (λ pb, pos_num.le pa pb))

  private definition psub (a b : pos_num) : num :=
  pos_num.rec_on a
    (λ b, zero)
    (λ n f b,
      bool.cond (pos_num.le (bit1 n) b)
        zero
        (pos_num.cases_on b
           (pos (bit0 n))
           (λ m, 2 * f m)
           (λ m, 2 * f m + 1)))
    (λ n f b,
      bool.cond (pos_num.le (bit0 n) b)
        zero
        (pos_num.cases_on b
           (pos (pos_num.pred (bit0 n)))
           (λ m, pred (2 * f m))
           (λ m, 2 * f m)))
    b

  protected definition sub (a b : num) : num :=
  num.rec_on a zero (λ pa, num.rec_on b a (λ pb, psub pa pb))
end num

instance : has_sub num :=
⟨num.sub⟩
