/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic
universe variables u

class is_associative (α : Type u) (r : α → α → Prop) (op : α → α → α) :=
(assoc : ∀ a b c, r (op (op a b) c) (op a (op b c)))

class is_commutative (α : Type u) (r : α → α → Prop) (op : α → α → α) :=
(comm : ∀ a b, r (op a b) (op b a))

class is_eq_associative (α : Type u) (op : α → α → α) extends is_associative α eq op

class is_eq_commutative (α : Type u) (op : α → α → α) extends is_commutative α eq op
