/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Int.Basic
public import Init.Data.BitVec.Basic
public import Init.Data.Repr
public import Init.Data.Ord.Basic

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Inductive with two constructors `negative` and `positive` for representing sign bits in
floating-point models. This is not a general-purpose sign type like mathlib's `SignType`,
which also includes a `zero` case.
-/
inductive Sign where
  /-- Negative (`-`) sign. -/
  | negative : Sign
  /-- Positive (`+`) sign. -/
  | positive : Sign
deriving Repr, BEq

namespace Sign

instance : Mul Sign where
  mul
    | .negative, .negative => .positive
    | .negative, .positive => .negative
    | .positive, .negative => .negative
    | .positive, .positive => .positive

instance : Div Sign where
  div
    | .negative, .negative => .positive
    | .negative, .positive => .negative
    | .positive, .negative => .negative
    | .positive, .positive => .positive

instance : Neg Sign where
  neg
    | .negative => .positive
    | .positive => .negative

instance : Ord Sign where
  compare
    | .negative, .negative => .eq
    | .negative, .positive => .lt
    | .positive, .negative => .gt
    | .positive, .positive => .eq

/--
Apply the given sign to the given integer.
-/
def apply (s : Sign) (n : Int) : Int :=
  match s with
  | .negative => -n
  | .positive => n

/--
Converts the sign to a bitvector, with positive sign denoted by `0`.
-/
def toBitVec : Sign → BitVec 1
  | .negative => 1#1
  | .positive => 0#1

/--
Constructs a sign from a bitvector, with positive sign denoted by `0`.
-/
def ofBitVec (b  : BitVec 1) : Sign :=
  if b = 0#1 then .positive else .negative

end Sign

end Float.Model.UnpackedFloat
