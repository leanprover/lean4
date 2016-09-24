/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.applicative
universe variables u v

class alternative (F : Type u → Type v) extends applicative F : Type (max u+1 v) :=
(failure : Π {A : Type u}, F A)
(orelse  : Π {A : Type u}, F A → F A → F A)

attribute [inline]
def failure {F : Type u → Type v} [alternative F] {A : Type u} : F A :=
alternative.failure F

attribute [inline]
def orelse {F : Type u → Type v} [alternative F] {A : Type u} : F A → F A → F A :=
alternative.orelse

infixr ` <|> `:2 := orelse

attribute [inline]
def guard {F : Type → Type v} [alternative F] (P : Prop) [decidable P] : F unit :=
if P then pure () else failure
