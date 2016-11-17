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

instance : has_to_string ordering :=
has_to_string.mk (λ s, match s with | ordering.lt := "lt" | ordering.eq := "eq" | ordering.gt := "gt" end)

class has_ordering (α : Type) :=
(cmp : α → α → ordering)

def nat.cmp (a b : nat) : ordering :=
if a < b      then ordering.lt
else if a = b then ordering.eq
else               ordering.gt

instance : has_ordering nat :=
⟨nat.cmp⟩

section
open prod

variables {α β : Type} [has_ordering α] [has_ordering β]

def prod.cmp : α × β → α × β → ordering
| (a₁, b₁) (a₂, b₂) :=
   match (has_ordering.cmp a₁ a₂) with
   | ordering.lt := lt
   | ordering.eq := has_ordering.cmp b₁ b₂
   | ordering.gt := gt
   end

instance {α β : Type} [has_ordering α] [has_ordering β] : has_ordering (α × β) :=
⟨prod.cmp⟩
end

section
open sum

variables {α β : Type} [has_ordering α] [has_ordering β]

def sum.cmp : α ⊕ β → α ⊕ β → ordering
| (inl a₁) (inl a₂) := has_ordering.cmp a₁ a₂
| (inr b₁) (inr b₂) := has_ordering.cmp b₁ b₂
| (inl a₁) (inr b₂) := lt
| (inr b₁) (inl a₂) := gt

instance {α β : Type} [has_ordering α] [has_ordering β] : has_ordering (α ⊕ β) :=
⟨sum.cmp⟩
end

section
open option

variables {α : Type} [has_ordering α]

def option.cmp : option α → option α → ordering
| (some a₁) (some a₂) := has_ordering.cmp a₁ a₂
| (some a₁) none      := gt
| none      (some a₂) := lt
| none      none      := eq

instance {α : Type} [has_ordering α] : has_ordering (option α) :=
⟨option.cmp⟩
end
