-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad
-- Ported from Coq HoTT
import .path
open path

-- Truncation levels
-- -----------------

inductive Contr (A : Type) : Type :=
Contr_mk : Π
  (center : A)
  (contr : Πy : A, center ≈ y),
Contr A

definition center {A : Type} (C : Contr A) : A := Contr.rec (λcenter contr, center) C

definition contr {A : Type} (C : Contr A) : Πy : A, center C ≈ y :=
Contr.rec (λcenter contr, contr) C

inductive trunc_index : Type :=
minus_two : trunc_index,
trunc_S : trunc_index → trunc_index

-- TODO: add coercions to / from nat

-- TODO: note in the Coq version, there is an internal version
definition IsTrunc (n : trunc_index) : Type → Type :=
trunc_index.rec (λA, Contr A) (λn trunc_n A, (Π(x y : A), trunc_n (x ≈ y))) n

-- TODO: in the Coq version, this is notation
definition minus_one := trunc_index.trunc_S trunc_index.minus_two
definition IsHProp := IsTrunc minus_one
definition IsHSet := IsTrunc (trunc_index.trunc_S minus_one)

prefix `!`:75 := center
