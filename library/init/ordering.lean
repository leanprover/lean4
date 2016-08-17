/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.to_string init.prod init.sum

inductive ordering
| lt | eq | gt

open ordering

attribute [instance]
definition ordering.has_to_string : has_to_string ordering :=
has_to_string.mk (λ s, match s with | ordering.lt := "lt" | ordering.eq := "eq" | ordering.gt := "gt" end)

structure [class] has_ordering (A : Type) :=
(cmp : A → A → ordering)

definition nat.cmp (a b : nat) : ordering :=
if a < b      then lt
else if a = b then eq
else               gt

attribute [instance]
definition nat_has_ordering : has_ordering nat :=
has_ordering.mk nat.cmp

section
open prod

variables {A B : Type} [has_ordering A] [has_ordering B]

definition prod.cmp : A × B → A × B → ordering
| (a₁, b₁) (a₂, b₂) :=
   match (has_ordering.cmp a₁ a₂) with
   | ordering.lt := lt
   | ordering.eq := has_ordering.cmp b₁ b₂
   | ordering.gt := gt
   end

attribute [instance]
definition prod_has_ordering {A B : Type} [has_ordering A] [has_ordering B] : has_ordering (A × B) :=
has_ordering.mk prod.cmp
end

section
open sum

variables {A B : Type} [has_ordering A] [has_ordering B]

definition sum.cmp : A ⊕ B → A ⊕ B → ordering
| (inl a₁) (inl a₂) := has_ordering.cmp a₁ a₂
| (inr b₁) (inr b₂) := has_ordering.cmp b₁ b₂
| (inl a₁) (inr b₂) := lt
| (inr b₁) (inl a₂) := gt

attribute [instance]
definition sum_has_ordering {A B : Type} [has_ordering A] [has_ordering B] : has_ordering (A ⊕ B) :=
has_ordering.mk sum.cmp
end

section
open option

variables {A : Type} [has_ordering A]

definition option.cmp : option A → option A → ordering
| (some a₁) (some a₂) := has_ordering.cmp a₁ a₂
| (some a₁) none      := gt
| none      (some a₂) := lt
| none      none      := eq

attribute [instance]
definition option_has_ordering {A : Type} [has_ordering A] : has_ordering (option A) :=
has_ordering.mk option.cmp
end
