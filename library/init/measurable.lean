/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Types with a nat-valued complexity measure.
-/
prelude
import init.nat init.meta.mk_measurable_instance
open nat tactic

inductive measurable [class] (A : Type) :=
mk : (A → nat) → measurable A

definition size_of {A : Type} [s : measurable A] : A → nat :=
measurable.rec_on s (λ f, f)

definition prop_measurable [instance] (p : Prop) : measurable p :=
measurable.mk (λ t, zero)

definition nat_measurable [instance] : measurable nat :=
measurable.mk (λ a, a)

definition Type_measurable [instance] : measurable Type :=
measurable.mk (λ t, zero)

definition fn_measurable [instance] (A : Type) (B : A → Type) : measurable (Π x, B x) :=
measurable.mk (λf, zero)

definition option.measurable [instance] (A : Type) [measurable A] : measurable (option A) :=
by mk_measurable_instance

definition prod_measurable [instance] (A B : Type) [measurable A] [measurable B] : measurable (prod A B) :=
by mk_measurable_instance

definition sum_measurable [instance] (A B : Type) [measurable A] [measurable B] : measurable (sum A B) :=
by mk_measurable_instance

definition list_measurable [instance] (A : Type) [measurable A] : measurable (list A) :=
by mk_measurable_instance

definition unit_measurable [instance] : measurable unit :=
by mk_measurable_instance

definition sigma_measurable [instance] (A : Type) (B : A → Type) [measurable A] [∀ x, measurable (B x)] : measurable (Σ x, B x) :=
by mk_measurable_instance

definition subtype_mesurable [instance] (A : Type) (P : A → Prop) [measurable A] : measurable {x \ P x} :=
by mk_measurable_instance

definition pos_num_measurable [instance] : measurable pos_num :=
by mk_measurable_instance

definition num_measurable [instance] : measurable num :=
by mk_measurable_instance
