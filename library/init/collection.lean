/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic
universe variables u v

/- Type class used to implement polymorphic notation for collections.
   Example: {a, b, c}. -/
structure [class] insertable (A : Type u) (C : Type u → Type v) :=
(empty : C A) (insert : A → C A → C A)

section
variables {A : Type u} {C : Type u → Type v}
variable [insertable A C]

def insert : A → C A → C A :=
insertable.insert

/- The empty collection -/
def empty_col : C A :=
insertable.empty A C

notation `∅` := empty_col

def singleton (a : A) : C A :=
insert a ∅
end

/- Type class used to implement the notation [ a ∈ c | p a ] -/
structure [class] decidable_separable (A : Type u) (C : Type u → Type v) :=
(sep : ∀ (p : A → Prop) [decidable_pred p], C A → C A)

section
variables {A : Type u} {C : Type u → Type v}
variable [decidable_separable A C]

def dec_sep (p : A → Prop) [decidable_pred p] : C A → C A :=
decidable_separable.sep p
end

/- Type class used to implement the notation { a ∈ c | p a } -/
structure [class] separable (A : Type u) (C : Type u → Type v) :=
(sep : (A → Prop) → C A → C A)

section
variables {A : Type u} {C : Type u → Type v}
variable [separable A C]

def sep : (A → Prop) → C A → C A :=
separable.sep
end
