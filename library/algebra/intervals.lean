/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Notation for intervals and some properties.

The mnemonic: o = open, c = closed, u = unbounded. For example, Iou a b is '(a, ∞).
-/
import .order data.set
open set

namespace intervals

variables {A : Type} [order_pair A]

definition Ioo (a b : A) : set A := {x | a < x ∧ x < b}
definition Ioc (a b : A) : set A := {x | a < x ∧ x ≤ b}
definition Ico (a b : A) : set A := {x | a ≤ x ∧ x < b}
definition Icc (a b : A) : set A := {x | a ≤ x ∧ x ≤ b}
definition Iou (a : A)   : set A := {x | a < x}
definition Icu (a : A)   : set A := {x | a ≤ x}
definition Iuo (b : A)   : set A := {x | x < b}
definition Iuc (b : A)   : set A := {x | x ≤ b}

notation `'` `(` a `, ` b `)`     := Ioo a b
notation `'` `(` a `, ` b `]`     := Ioc a b
notation `'[` a `, ` b `)`        := Ico a b
notation `'[` a `, ` b `]`        := Icc a b
notation `'` `(` a `, ` `∞` `)`   := Iou a
notation `'[` a `, ` `∞` `)`      := Icu a
notation `'` `(` `-∞` `, ` b `)`  := Iuo b
notation `'` `(` `-∞` `, ` b `]`  := Iuc b

variables a b c d e f : A

/- some examples:

  check '(a, b)
  check '(a, b]
  check '[a, b)
  check '[a, b]
  check '(a, ∞)
  check '[a, ∞)
  check '(-∞, b)
  check '(-∞, b]

  check '{a, b, c}

  check '(a, b] ∩ '(c, ∞)
  check '(-∞, b) \ ('(c, d) ∪ '[e, ∞))
-/

proposition Iou_inter_Iuo : '(a, ∞) ∩ '(-∞, b) = '(a, b) := rfl

end intervals
