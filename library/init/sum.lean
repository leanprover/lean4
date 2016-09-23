/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import init.logic

notation A ⊕ B := sum A B

universe variables u v

variables {A : Type u} {B : Type v}

instance sum.inhabited_left [h : inhabited A] : inhabited (A ⊕ B) :=
⟨sum.inl (default A)⟩

instance sum.inhabited_right [h : inhabited B] : inhabited (A ⊕ B) :=
⟨sum.inr (default B)⟩
