/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Types with a nat-valued complexity measure.
-/
prelude
import init.nat init.meta.mk_has_sizeof_instance
open nat tactic

structure has_sizeof [class] (A : Type) :=
(sizeof : A → nat)

definition sizeof {A : Type} [s : has_sizeof A] : A → nat :=
has_sizeof.sizeof

definition prop_has_sizeof [instance] (p : Prop) : has_sizeof p :=
has_sizeof.mk (λ t, zero)

definition nat_has_sizeof [instance] : has_sizeof nat :=
has_sizeof.mk (λ a, a)

definition Type_has_sizeof [instance] : has_sizeof Type :=
has_sizeof.mk (λ t, zero)

definition Prop_has_sizeof [instance] : has_sizeof Prop :=
has_sizeof.mk (λ t, zero)

definition fn_has_sizeof [instance] (A : Type) (B : A → Type) : has_sizeof (Π x, B x) :=
has_sizeof.mk (λf, zero)

definition option.has_sizeof [instance] (A : Type) [has_sizeof A] : has_sizeof (option A) :=
by mk_has_sizeof_instance

definition prod_has_sizeof [instance] (A B : Type) [has_sizeof A] [has_sizeof B] : has_sizeof (prod A B) :=
by mk_has_sizeof_instance

definition sum_has_sizeof [instance] (A B : Type) [has_sizeof A] [has_sizeof B] : has_sizeof (sum A B) :=
by mk_has_sizeof_instance

definition list_has_sizeof [instance] (A : Type) [has_sizeof A] : has_sizeof (list A) :=
by mk_has_sizeof_instance

definition unit_has_sizeof [instance] : has_sizeof unit :=
by mk_has_sizeof_instance

definition bool_has_sizeof [instance] : has_sizeof bool :=
by mk_has_sizeof_instance

definition sigma_has_sizeof [instance] (A : Type) (B : A → Type) [has_sizeof A] [∀ x, has_sizeof (B x)] : has_sizeof (Σ x, B x) :=
by mk_has_sizeof_instance

definition subtype_has_sizeof [instance] (A : Type) (P : A → Prop) [has_sizeof A] : has_sizeof {x \ P x} :=
by mk_has_sizeof_instance

definition pos_num_has_sizeof [instance] : has_sizeof pos_num :=
by mk_has_sizeof_instance

definition num_has_sizeof [instance] : has_sizeof num :=
by mk_has_sizeof_instance
