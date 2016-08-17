/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Types with a nat-valued complexity measure.
-/
prelude
import init.nat init.meta.mk_has_sizeof_instance
open nat tactic

structure [class] has_sizeof (A : Type) :=
(sizeof : A → nat)

definition sizeof {A : Type} [s : has_sizeof A] : A → nat :=
has_sizeof.sizeof

attribute [instance]
definition prop_has_sizeof (p : Prop) : has_sizeof p :=
has_sizeof.mk (λ t, zero)

attribute [instance]
definition nat_has_sizeof : has_sizeof nat :=
has_sizeof.mk (λ a, a)

attribute [instance]
definition Type_has_sizeof : has_sizeof Type :=
has_sizeof.mk (λ t, zero)

attribute [instance]
definition Prop_has_sizeof : has_sizeof Prop :=
has_sizeof.mk (λ t, zero)

attribute [instance]
definition fn_has_sizeof (A : Type) (B : A → Type) : has_sizeof (Π x, B x) :=
has_sizeof.mk (λf, zero)

attribute [instance]
definition option.has_sizeof (A : Type) [has_sizeof A] : has_sizeof (option A) :=
by mk_has_sizeof_instance

attribute [instance]
definition prod_has_sizeof (A B : Type) [has_sizeof A] [has_sizeof B] : has_sizeof (A × B) :=
by mk_has_sizeof_instance

attribute [instance]
definition sum_has_sizeof (A B : Type) [has_sizeof A] [has_sizeof B] : has_sizeof (A ⊕ B) :=
by mk_has_sizeof_instance

attribute [instance]
definition list_has_sizeof (A : Type) [has_sizeof A] : has_sizeof (list A) :=
by mk_has_sizeof_instance

attribute [instance]
definition unit_has_sizeof : has_sizeof unit :=
by mk_has_sizeof_instance

attribute [instance]
definition bool_has_sizeof : has_sizeof bool :=
by mk_has_sizeof_instance

attribute [instance]
definition sigma_has_sizeof (A : Type) (B : A → Type) [has_sizeof A] [∀ x, has_sizeof (B x)] : has_sizeof (Σ x, B x) :=
by mk_has_sizeof_instance

attribute [instance]
definition subtype_has_sizeof (A : Type) (P : A → Prop) [has_sizeof A] : has_sizeof {x \ P x} :=
by mk_has_sizeof_instance

attribute [instance]
definition pos_num_has_sizeof : has_sizeof pos_num :=
by mk_has_sizeof_instance

attribute [instance]
definition num_has_sizeof : has_sizeof num :=
by mk_has_sizeof_instance
