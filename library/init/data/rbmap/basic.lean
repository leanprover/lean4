/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbtree.basic

universes u v w

def rbmap_lt {α : Type u} {β : Type v} (lt : α → α → Prop) (a b : α × β) : Prop :=
lt a.1 b.1

set_option auto_param.check_exists false

def rbmap (α : Type u) (β : Type v) (lt : α → α → Prop . rbtree.default_lt) : Type (max u v) :=
rbtree (α × β) (rbmap_lt lt)

def mk_rbmap (α : Type u) (β : Type v) (lt : α → α → Prop . rbtree.default_lt) : rbmap α β lt :=
mk_rbtree (α × β) (rbmap_lt lt)

namespace rbmap
variables {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}

def empty (m : rbmap α β lt) : bool :=
m.empty

def to_list (m : rbmap α β lt) : list (α × β) :=
m.to_list

def min (m : rbmap α β lt) : option (α × β) :=
m.min

def max (m : rbmap α β lt) : option (α × β) :=
m.max

def fold (f : α → β → δ → δ) (m : rbmap α β lt) (d : δ) : δ :=
m.fold (λ e, f e.1 e.2) d

def rev_fold (f : α → β → δ → δ) (m : rbmap α β lt) (d : δ) : δ :=
m.rev_fold (λ e, f e.1 e.2) d

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
end

instance : has_mem α (rbmap α β lt) :=
⟨rbmap.mem⟩

instance [has_repr α] [has_repr β] : has_repr (rbmap α β lt) :=
⟨λ t, "rbmap_of " ++ repr t.to_list⟩

def rbmap_lt_dec [h : decidable_rel lt] : decidable_rel (@rbmap_lt α β lt) :=
λ a b, h a.1 b.1

variable [decidable_rel lt]

def insert (m : rbmap α β lt) (k : α) (v : β) : rbmap α β lt :=
@rbtree.insert _ _ rbmap_lt_dec m (k, v)

def find_entry (m : rbmap α β lt) (k : α) : option (α × β) :=
match m.val with
| rbnode.leaf             := none
| rbnode.red_node _ e _   := @rbtree.find _ _ rbmap_lt_dec m (k, e.2)
| rbnode.black_node _ e _ := @rbtree.find _ _ rbmap_lt_dec m (k, e.2)
end

def to_value : option (α × β) → option β
| none     := none
| (some e) := some e.2

def find (m : rbmap α β lt) (k : α) : option β :=
to_value (m.find_entry k)

def contains (m : rbmap α β lt) (k : α) : bool :=
(find_entry m k).is_some

def from_list (l : list (α × β)) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbmap α β lt :=
l.foldl (λ m p, insert m p.1 p.2)  (mk_rbmap α β lt)

end rbmap

def rbmap_of {α : Type u} {β : Type v} (l : list (α × β)) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbmap α β lt :=
rbmap.from_list l lt
