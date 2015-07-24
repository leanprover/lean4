/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Types with a nat-valued complexity measure.
-/
prelude
import init.nat
open nat

inductive measurable [class] (A : Type) :=
mk : (A → nat) → measurable A

definition size_of {A : Type} [s : measurable A] : A → nat :=
measurable.rec_on s (λ f, f)

definition nat.measurable [instance] : measurable nat :=
measurable.mk (λ a, a)

definition option.measurable [instance] (A : Type) [s : measurable A] : measurable (option A) :=
measurable.mk (λ a, option.cases_on a zero size_of)

definition prod.measurable [instance] (A B : Type) [sa : measurable A] [sb : measurable B] : measurable (prod A B) :=
measurable.mk (λ p, prod.cases_on p (λ a b, size_of a + size_of b))

definition sum.measurable [instance] (A B : Type) [sa : measurable A] [sb : measurable B] : measurable (sum A B) :=
measurable.mk (λ s, sum.cases_on s (λ a, size_of a) (λ b, size_of b))

definition bool.measurable [instance] : measurable bool :=
measurable.mk (λb, zero)

definition Prop.measurable [instance] : measurable Prop :=
measurable.mk (λp, zero)

definition unit.measurable [instance] : measurable unit :=
measurable.mk (λu, zero)

definition fn.measurable [instance] (A : Type) (B : A → Type) : measurable (Π x, B x) :=
measurable.mk (λf, zero)
