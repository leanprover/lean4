/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Basic datatypes
-/
prelude
notation `Prop`  := Type.{0}
notation [parsing_only] `Type'` := Type.{_+1}
notation [parsing_only] `Type₊` := Type.{_+1}
notation `Type₁` := Type.{1}
notation `Type₂` := Type.{2}
notation `Type₃` := Type.{3}

inductive poly_unit.{l} : Type.{l}
| star : poly_unit

inductive unit : Type₁
| star : unit

inductive true : Prop
| intro : true

inductive false : Prop

inductive empty : Type₁

inductive eq {A : Type} (a : A) : A → Prop
| refl : eq a

inductive heq {A : Type} (a : A) : Π {B : Type}, B → Prop
| refl : heq a

structure prod (A B : Type) :=
(pr1 : A) (pr2 : B)

inductive and (a b : Prop) : Prop
| intro : a → b → and

definition and.elim_left {a b : Prop} (H : and a b) : a  :=
and.rec (λa b, a) H

definition and.left := @and.elim_left

definition and.elim_right {a b : Prop} (H : and a b) : b :=
and.rec (λa b, b) H

definition and.right := @and.elim_right

inductive sum (A B : Type) : Type
| inl {} : A → sum
| inr {} : B → sum

attribute [reducible]
definition sum.intro_left {A : Type} (B : Type) (a : A) : sum A B :=
sum.inl a

attribute [reducible]
definition sum.intro_right (A : Type) {B : Type} (b : B) : sum A B :=
sum.inr b

inductive or (a b : Prop) : Prop
| inl {} : a → or
| inr {} : b → or

definition or.intro_left {a : Prop} (b : Prop) (Ha : a) : or a b :=
or.inl Ha

definition or.intro_right (a : Prop) {b : Prop} (Hb : b) : or a b :=
or.inr Hb

structure sigma {A : Type} (B : A → Type) :=
mk :: (pr1 : A) (pr2 : B pr1)

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

namespace pos_num
  definition succ (a : pos_num) : pos_num :=
  pos_num.rec_on a (bit0 one) (λn r, bit0 r) (λn r, bit1 n)
end pos_num

inductive num : Type
| zero  : num
| pos   : pos_num → num

namespace num
  open pos_num
  definition succ (a : num) : num :=
  num.rec_on a (pos one) (λp, pos (succ p))
end num

inductive bool : Type
| ff : bool
| tt : bool

inductive option (A : Type) : Type
| none {} : option
| some    : A → option

export option (none some)
export bool (ff tt)

inductive list (T : Type) : Type
| nil {} : list
| cons   : T → list → list

-- Remark: we manually generate the nat.rec_on, nat.induction_on, nat.cases_on and nat.no_confusion.
-- We do that because we want 0 instead of nat.zero in these eliminators.
set_option inductive.rec_on   false
set_option inductive.cases_on false
inductive nat
| zero : nat
| succ : nat → nat
