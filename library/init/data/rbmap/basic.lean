/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbtree.basic

universes u v w w'

@[inline] def rbmap_lt {α : Type u} {β : Type v} (lt : α → α → Prop) (a b : α × β) : Prop :=
lt a.1 b.1

@[inline] def rbmap_lt_dec {α : Type u} {β : Type v} {lt : α → α → Prop} [h : decidable_rel lt] : decidable_rel (@rbmap_lt α β lt) :=
λ a b, h a.1 b.1

def rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : Type (max u v) :=
rbtree (α × β) (rbmap_lt lt)

@[inline] def mk_rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : rbmap α β lt :=
mk_rbtree (α × β) (rbmap_lt lt)

namespace rbmap
variables {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}

@[inline] def empty (m : rbmap α β lt) : bool :=
m.empty

@[inline] def to_list (m : rbmap α β lt) : list (α × β) :=
m.to_list

@[inline] def min (m : rbmap α β lt) : option (α × β) :=
m.min

@[inline] def max (m : rbmap α β lt) : option (α × β) :=
m.max

@[specialize] def fold (f : α → β → δ → δ) (m : rbmap α β lt) (d : δ) : δ :=
m.fold (λ e, f e.1 e.2) d

@[specialize] def rev_fold (f : α → β → δ → δ) (m : rbmap α β lt) (d : δ) : δ :=
m.rev_fold (λ e, f e.1 e.2) d

@[specialize] def mfold {m : Type w → Type w'} [monad m] (f : α → β → δ → m δ) (mp : rbmap α β lt) (d : δ) : m δ :=
mp.mfold (λ e, f e.1 e.2) d

@[specialize] def mfor {m : Type w → Type w'} [monad m] (f : α → β → m δ) (mp : rbmap α β lt) : m punit :=
mp.mfold (λ a b _, f a b *> pure ⟨⟩) ⟨⟩

/-
We don't assume β is inhabited when in membership predicate `mem` and
function find_entry to make this module more convenient to use.
If we had assumed β to be inhabited we could use the following simpler
definition: (k, default β) ∈ m
-/

protected def mem (k : α) (m : rbmap α β lt) : Prop :=
match m.val with
| rbnode.leaf             := false
| rbnode.red_node _ e _   := rbtree.mem (k, e.2) m
| rbnode.black_node _ e _ := rbtree.mem (k, e.2) m

instance : has_mem α (rbmap α β lt) :=
⟨rbmap.mem⟩

instance [has_repr α] [has_repr β] : has_repr (rbmap α β lt) :=
⟨λ t, "rbmap_of " ++ repr t.to_list⟩

variable [decidable_rel lt]

@[inline] def insert (m : rbmap α β lt) (k : α) (v : β) : rbmap α β lt :=
@rbtree.insert _ _ rbmap_lt_dec m (k, v)

@[inline] def find_entry (m : rbmap α β lt) (k : α) : option (α × β) :=
match m.val with
| rbnode.leaf             := none
| rbnode.red_node _ e _   := @rbtree.find _ _ rbmap_lt_dec m (k, e.2)
| rbnode.black_node _ e _ := @rbtree.find _ _ rbmap_lt_dec m (k, e.2)

@[inline] def to_value : option (α × β) → option β
| none     := none
| (some e) := some e.2

@[inline] def find (m : rbmap α β lt) (k : α) : option β :=
to_value (m.find_entry k)

@[inline] def contains (m : rbmap α β lt) (k : α) : bool :=
(find_entry m k).is_some

def from_list (l : list (α × β)) (lt : α → α → Prop) [decidable_rel lt] : rbmap α β lt :=
l.foldl (λ m p, insert m p.1 p.2)  (mk_rbmap α β lt)

-- TODO: replace with more efficient, structure-preserving implementation (needs wf proof)
@[specialize] def map (f : α → β → δ) (m : rbmap α β lt) : rbmap α δ lt :=
m.fold (λ a b m, rbmap.insert m a (f a b)) (mk_rbmap α δ lt)

end rbmap

def rbmap_of {α : Type u} {β : Type v} (l : list (α × β)) (lt : α → α → Prop) [decidable_rel lt] : rbmap α β lt :=
rbmap.from_list l lt

/- Low level functions that process `rbnode`'s directly.
   It is useful when we need a mapping in a nested inductive datatypes. -/
namespace rbmap_core
variables {α : Type u} {β : Type v}

@[inline] def empty (m : rbnode (α × β)) : bool :=
match m with
| rbnode.leaf := tt
| _           := ff

variables (lt : α → α → Prop) [decidable_rel lt]

@[inline] def insert (m : rbnode (α × β)) (k : α) (v : β) : rbnode (α × β) :=
@rbnode.insert (α × β) (rbmap_lt lt) rbmap_lt_dec m (k, v)

@[inline] def find_entry (m : rbnode (α × β)) (k : α) : option (α × β) :=
match m with
| rbnode.leaf             := none
| rbnode.red_node _ e _   := @rbnode.find (α × β) (rbmap_lt lt) rbmap_lt_dec m (k, e.2)
| rbnode.black_node _ e _ := @rbnode.find (α × β) (rbmap_lt lt) rbmap_lt_dec m (k, e.2)

@[inline] def find (m : rbnode (α × β)) (k : α) : option β :=
rbmap.to_value (rbmap_core.find_entry lt m k)

@[inline] def contains (m : rbnode (α × β)) (k : α) : bool :=
(find_entry lt m k).is_some

def from_list (l : list (α × β)) (lt : α → α → Prop) [decidable_rel lt] : rbnode (α × β) :=
l.foldl (λ m p, insert lt m p.1 p.2) rbnode.leaf

end rbmap_core
