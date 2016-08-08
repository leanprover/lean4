/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.applicative

structure alternative [class] (f : Type → Type) extends applicative f :=
(failure : Π {A : Type}, f A)
(orelse  : Π {A : Type}, f A → f A → f A)

definition failure [inline] {f : Type → Type} [alternative f] {A : Type} : f A :=
alternative.failure f

definition orelse [inline] {f : Type → Type} [alternative f] {A : Type} : f A → f A → f A :=
alternative.orelse

infixr ` <|> `:2 := orelse

definition guard [inline] {f : Type₁ → Type} [alternative f] (p : Prop) [decidable p] : f unit :=
if p then pure () else failure
