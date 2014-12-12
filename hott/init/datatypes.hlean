/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Jakob von Raumer

Basic datatypes
-/
prelude
notation [parsing-only] `Type'` := Type.{_+1}
notation [parsing-only] `Type₊` := Type.{_+1}
notation `Type₀` := Type.{0}
notation `Type₁` := Type.{1}
notation `Type₂` := Type.{2}
notation `Type₃` := Type.{3}

inductive unit.{l} : Type.{l} :=
star : unit

namespace unit

  notation `⋆` := star

end unit

inductive empty.{l} : Type.{l}

inductive eq.{l} {A : Type.{l}} (a : A) : A → Type.{l} :=
refl : eq a a

structure lift.{l₁ l₂} (A : Type.{l₁}) : Type.{max l₁ l₂} :=
up :: (down : A)

structure prod (A B : Type) :=
mk :: (pr1 : A) (pr2 : B)

inductive sum (A B : Type) : Type :=
inl {} : A → sum A B,
inr {} : B → sum A B

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive pos_num : Type :=
one  : pos_num,
bit1 : pos_num → pos_num,
bit0 : pos_num → pos_num

inductive num : Type :=
zero  : num,
pos   : pos_num → num

inductive bool : Type :=
ff : bool,
tt : bool

inductive char : Type :=
mk : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type :=
empty : string,
str   : char → string → string

inductive nat :=
zero : nat,
succ : nat → nat

inductive option (A : Type) : Type :=
none {} : option A,
some    : A → option A
