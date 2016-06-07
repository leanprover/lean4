/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.to_string init.prod

inductive cmp_result :=
| lt | eq | gt

open cmp_result

definition cmp_result.has_to_string [instance] : has_to_string cmp_result :=
has_to_string.mk (λ s, match s with | lt := "lt" | eq := "eq" | gt := "gt" end)

structure has_cmp [class] (A : Type) :=
(cmp : A → A → cmp_result)

definition nat.cmp (a b : nat) : cmp_result :=
if a < b      then lt
else if a = b then eq
else               gt

definition nat_has_cmp [instance] : has_cmp nat :=
has_cmp.mk nat.cmp

section
open prod

variables {A B : Type} [has_cmp A] [has_cmp B]

definition prod.cmp : A × B → A × B → cmp_result
| (a₁, b₁) (a₂, b₂) :=
   match has_cmp.cmp a₁ a₂ with
   | lt := lt
   | eq := has_cmp.cmp b₁ b₂
   | gt := gt
   end

definition prod_has_cmp [instance] {A B : Type} [has_cmp A] [has_cmp B] : has_cmp (A × B) :=
has_cmp.mk prod.cmp
end

section
open sum

variables {A B : Type} [has_cmp A] [has_cmp B]

definition sum.cmp : sum A B → sum A B → cmp_result
| (inl a₁) (inl a₂) := has_cmp.cmp a₁ a₂
| (inr b₁) (inr b₂) := has_cmp.cmp b₁ b₂
| (inl a₁) (inr b₂) := lt
| (inr b₁) (inl a₂) := gt

definition sum_has_cmp [instance] {A B : Type} [has_cmp A] [has_cmp B] : has_cmp (sum A B) :=
has_cmp.mk sum.cmp
end

section
open option

variables {A : Type} [has_cmp A]

definition option.cmp : option A → option A → cmp_result
| (some a₁) (some a₂) := has_cmp.cmp a₁ a₂
| (some a₁) none      := gt
| none      (some a₂) := lt
| none      none      := eq

definition option_has_cmp [instance] {A : Type} [has_cmp A] : has_cmp (option A) :=
has_cmp.mk option.cmp
end
