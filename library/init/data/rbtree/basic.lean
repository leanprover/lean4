/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering

universes u v

inductive rbnode (α : Type u)
| leaf  {}                                                 : rbnode
| red_node   (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode
| black_node (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode

namespace rbnode
variables {α : Type u} {β : Type v}

inductive color
| red | black

open color nat

instance color.decidable_eq : decidable_eq color :=
λ a b, color.cases_on a
  (color.cases_on b (is_true rfl) (is_false (λ h, color.no_confusion h)))
  (color.cases_on b (is_false (λ h, color.no_confusion h)) (is_true rfl))

def depth (f : nat → nat → nat) : rbnode α → nat
| leaf               := 0
| (red_node l _ r)   := succ (f (depth l) (depth r))
| (black_node l _ r) := succ (f (depth l) (depth r))

protected def min : rbnode α → option α
| leaf                  := none
| (red_node leaf v _)   := some v
| (black_node leaf v _) := some v
| (red_node l v _)      := min l
| (black_node l v _)    := min l

protected def max : rbnode α → option α
| leaf                  := none
| (red_node _ v leaf)   := some v
| (black_node _ v leaf) := some v
| (red_node _ v r)      := max r
| (black_node _ v r)    := max r

def fold (f : α → β → β) : rbnode α → β → β
| leaf b               := b
| (red_node l v r)   b := fold r (f v (fold l b))
| (black_node l v r) b := fold r (f v (fold l b))

def rev_fold (f : α → β → β) : rbnode α → β → β
| leaf b               := b
| (red_node l v r)   b := rev_fold l (f v (rev_fold r b))
| (black_node l v r) b := rev_fold l (f v (rev_fold r b))

def balance1 : rbnode α → α → rbnode α → α → rbnode α → rbnode α
| (red_node l x r₁) y r₂  v t := red_node (black_node l x r₁) y (black_node r₂ v t)
| l₁ y (red_node l₂ x r)  v t := red_node (black_node l₁ y l₂) x (black_node r v t)
| l  y r                  v t := black_node (red_node l y r) v t

def balance1_node : rbnode α → α → rbnode α → rbnode α
| (red_node l x r)   v t := balance1 l x r v t
| (black_node l x r) v t := balance1 l x r v t
| leaf               v t := t  /- dummy value -/

def balance2 : rbnode α → α → rbnode α → α → rbnode α → rbnode α
| (red_node l x₁ r₁) y r₂  v t := red_node (black_node t v l) x₁ (black_node r₁ y r₂)
| l₁ y (red_node l₂ x₂ r₂) v t := red_node (black_node t v l₁) y (black_node l₂ x₂ r₂)
| l  y r                   v t := black_node t v (red_node l y r)

def balance2_node : rbnode α → α → rbnode α → rbnode α
| (red_node l x r)   v t := balance2 l x r v t
| (black_node l x r) v t := balance2 l x r v t
| leaf               v t := t /- dummy -/

def get_color : rbnode α → color
| (red_node _ _ _) := red
| _                := black

section insert

variables (lt : α → α → Prop) [decidable_rel lt]

def ins : rbnode α → α → rbnode α
| leaf             x  := red_node leaf x leaf
| (red_node a y b) x  :=
   match cmp_using lt x y with
   | ordering.lt := red_node (ins a x) y b
   | ordering.eq := red_node a x b
   | ordering.gt := red_node a y (ins b x)
   end
| (black_node a y b) x :=
    match cmp_using lt x y with
    | ordering.lt :=
      if a.get_color = red then balance1_node (ins a x) y b
      else black_node (ins a x) y b
    | ordering.eq := black_node a x b
    | ordering.gt :=
      if b.get_color = red then balance2_node (ins b x) y a
      else black_node a y (ins b x)
    end

def mk_insert_result : color → rbnode α → rbnode α
| red (red_node l v r)   := black_node l v r
| _   t                  := t

def insert (t : rbnode α) (x : α) : rbnode α :=
mk_insert_result (get_color t) (ins lt t x)

end insert

section membership

variable (lt : α → α → Prop)

def mem : α → rbnode α → Prop
| a leaf               := false
| a (red_node l v r)   := mem a l ∨ (¬ lt a v ∧ ¬ lt v a) ∨ mem a r
| a (black_node l v r) := mem a l ∨ (¬ lt a v ∧ ¬ lt v a) ∨ mem a r

def mem_exact : α → rbnode α → Prop
| a leaf               := false
| a (red_node l v r)   := mem_exact a l ∨ a = v ∨ mem_exact a r
| a (black_node l v r) := mem_exact a l ∨ a = v ∨ mem_exact a r

variable [decidable_rel lt]

def find : rbnode α → α → option α
| leaf             x := none
| (red_node a y b) x :=
  match cmp_using lt x y with
  | ordering.lt := find a x
  | ordering.eq := some y
  | ordering.gt := find b x
  end
| (black_node a y b) x :=
  match cmp_using lt x y with
  | ordering.lt := find a x
  | ordering.eq := some y
  | ordering.gt := find b x
  end

end membership

inductive well_formed (lt : α → α → Prop) : rbnode α → Prop
| leaf_wff : well_formed leaf
| insert_wff {n n' : rbnode α} {x : α} [decidable_rel lt] : well_formed n → n' = insert lt n x → well_formed n'

end rbnode

open rbnode

set_option auto_param.check_exists false

def rbtree (α : Type u) (lt : α → α → Prop . rbtree.default_lt) : Type u :=
{t : rbnode α // t.well_formed lt }

def mk_rbtree (α : Type u) (lt : α → α → Prop . rbtree.default_lt) : rbtree α lt :=
⟨leaf, well_formed.leaf_wff lt⟩

namespace rbtree
variables {α : Type u} {β : Type v} {lt : α → α → Prop}

protected def mem (a : α) (t : rbtree α lt) : Prop :=
rbnode.mem lt a t.val

instance : has_mem α (rbtree α lt) :=
⟨rbtree.mem⟩

def mem_exact (a : α) (t : rbtree α lt) : Prop :=
rbnode.mem_exact a t.val

def depth (f : nat → nat → nat) (t : rbtree α lt) : nat :=
t.val.depth f

def fold (f : α → β → β) : rbtree α lt → β →  β
| ⟨t, _⟩ b := t.fold f b

def rev_fold (f : α → β → β) : rbtree α lt → β →  β
| ⟨t, _⟩ b := t.rev_fold f b

def empty : rbtree α lt → bool
| ⟨leaf, _⟩ := tt
| _         := ff

def to_list : rbtree α lt → list α
| ⟨t, _⟩ := t.rev_fold (::) []

protected def min : rbtree α lt → option α
| ⟨t, _⟩ := t.min

protected def max : rbtree α lt → option α
| ⟨t, _⟩ := t.max

instance [has_repr α] : has_repr (rbtree α lt) :=
⟨λ t, "rbtree_of " ++ repr t.to_list⟩

variables [decidable_rel lt]

def insert : rbtree α lt → α → rbtree α lt
| ⟨t, w⟩   x := ⟨t.insert lt x, well_formed.insert_wff w rfl⟩

def find : rbtree α lt → α → option α
| ⟨t, _⟩ x := t.find lt x

def contains (t : rbtree α lt) (a : α) : bool :=
(t.find a).is_some

def from_list (l : list α) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbtree α lt :=
l.foldl insert (mk_rbtree α lt)

end rbtree

def rbtree_of {α : Type u} (l : list α) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbtree α lt :=
rbtree.from_list l lt
