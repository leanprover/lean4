/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance

universe variables u v
instance {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β] : decidable_eq (α ⊕ β) :=
by tactic.mk_dec_eq_instance
