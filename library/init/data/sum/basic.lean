/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import init.logic

notation α ⊕ β := sum α β

universes u v

variables {α : Type u} {β : Type v}

instance sum.inhabited_left [h : inhabited α] : inhabited (α ⊕ β) :=
⟨sum.inl (default α)⟩

instance sum.inhabited_right [h : inhabited β] : inhabited (α ⊕ β) :=
⟨sum.inr (default β)⟩
