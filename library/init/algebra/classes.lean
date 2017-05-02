/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic
universes u

@[algebra] class is_commutative (α : Type u) (op : α → α → α) : Prop :=
(comm : ∀ a b, op a b = op b a)

@[algebra] class is_associative (α : Type u) (op : α → α → α) : Prop :=
(assoc : ∀ a b c, op (op a b) c = op a (op b c))

@[algebra] class is_left_id (α : Type u) (op : α → α → α) (o : inout α) : Prop :=
(left_id : ∀ a, op o a = a)

@[algebra] class is_right_id (α : Type u) (op : α → α → α) (o : inout α) : Prop :=
(right_id : ∀ a, op a o = a)

@[algebra] class is_left_null (α : Type u) (op : α → α → α) (o : inout α) : Prop :=
(left_null : ∀ a, op o a = o)

@[algebra] class is_right_null (α : Type u) (op : α → α → α) (o : inout α) : Prop :=
(right_null : ∀ a, op a o = o)

@[algebra] class is_left_cancel (α : Type u) (op : α → α → α) : Prop :=
(left_cancel : ∀ a b c, op a b = op a c → b = c)

@[algebra] class is_right_cancel (α : Type u) (op : α → α → α) : Prop :=
(right_cancel : ∀ a b c, op a b = op c b → a = c)

@[algebra] class is_idempotent (α : Type u) (op : α → α → α) : Prop :=
(idempotent : ∀ a, op a a = a)

@[algebra] class is_left_distrib (α : Type u) (op₁ : α → α → α) (op₂ : inout α → α → α) : Prop :=
(left_distrib : ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c))

@[algebra] class is_right_distrib (α : Type u) (op₁ : α → α → α) (op₂ : inout α → α → α) : Prop :=
(right_distrib : ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c))

@[algebra] class is_left_inv (α : Type u) (op : α → α → α) (inv : inout α → α) (o : inout α) : Prop :=
(left_inv : ∀ a, op (inv a) a = o)

@[algebra] class is_right_inv (α : Type u) (op : α → α → α) (inv : inout α → α) (o : inout α) : Prop :=
(right_inv : ∀ a, op a (inv a) = o)

@[algebra] class is_cond_left_inv (α : Type u) (op : α → α → α) (inv : inout α → α) (o : inout α) (p : inout α → Prop) : Prop :=
(left_inv : ∀ a, p a → op (inv a) a = o)

@[algebra] class is_cond_right_inv (α : Type u) (op : α → α → α) (inv : inout α → α) (o : inout α) (p : inout α → Prop) : Prop :=
(right_inv : ∀ a, p a → op a (inv a) = o)

@[algebra] class is_distinct (α : Type u) (a : α) (b : α) : Prop :=
(distinct : a ≠ b)

/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Type u) (β : Type v) (f : α → β) (g : inout β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Type u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/
