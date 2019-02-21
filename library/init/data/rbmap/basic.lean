/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.coe init.data.option.basic

universes u v w w'

inductive rbcolor
| red | black

inductive rbnode (α : Type u) (β : α → Type v)
| leaf  {}                                                                            : rbnode
| node  (color : rbcolor) (lchild : rbnode) (key : α) (val : β key) (rchild : rbnode) : rbnode

namespace rbnode
variables {α : Type u} {β : α → Type v} {σ : Type w}

open rbcolor nat

def depth (f : nat → nat → nat) : rbnode α β → nat
| leaf               := 0
| (node _ l _ _ r)   := succ (f (depth l) (depth r))

protected def min : rbnode α β → option (Σ k : α, β k)
| leaf                  := none
| (node _ leaf k v _)   := some ⟨k, v⟩
| (node _ l k v _)      := min l

protected def max : rbnode α β → option (Σ k : α, β k)
| leaf                  := none
| (node _ _ k v leaf)   := some ⟨k, v⟩
| (node _ _ k v r)      := max r

@[specialize] def fold (f : Π (k : α), β k → σ → σ) : rbnode α β → σ → σ
| leaf b               := b
| (node _ l k v r)   b := fold r (f k v (fold l b))

@[specialize] def mfold {m : Type w → Type w'} [monad m] (f : Π (k : α), β k → σ → m σ) : rbnode α β → σ → m σ
| leaf b               := pure b
| (node _ l k v r) b   := do b₁ ← mfold l b, b₂ ← f k v b₁, mfold r b₂

@[specialize] def rev_fold (f : Π (k : α), β k → σ → σ) : rbnode α β → σ → σ
| leaf b               := b
| (node _ l k v r)   b := rev_fold l (f k v (rev_fold r b))

@[specialize] def all (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf                 := tt
| (node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf                 := ff
| (node _ l k v r)   := p k v || any l || any r

def balance1 : rbnode α β → Π (k : α), β k → rbnode α β → rbnode α β
| (node _ (node red l kx vx r₁) ky vy r₂) kv vv t := node red (node black l kx vx r₁) ky vy (node black r₂ kv vv t)
| (node _ l₁ ky vy (node red l₂ kx vx r)) kv vv t := node red (node black l₁ ky vy l₂) kx vx (node black r kv vv t)
| (node _ l  ky vy r)                     kv vv t := node black (node red l ky vy r) kv vv t
| leaf                                    kv vv t := t  /- dummy value -/

def balance2 : rbnode α β → Π k : α, β k → rbnode α β → rbnode α β
| (node _ (node red l kx₁ vx₁ r₁) ky vy r₂)  kv vv t := node red (node black t kv vv l) kx₁ vx₁ (node black r₁ ky vy r₂)
| (node _ l₁ ky vy (node red l₂ kx₂ vx₂ r₂)) kv vv t := node red (node black t kv vv l₁) ky vy (node black l₂ kx₂ vx₂ r₂)
| (node _ l ky vy r)                         kv vv t := node black t kv vv (node red l ky vy r)
| leaf                                       kv vv t := t /- dummy -/

def is_red : rbnode α β → bool
| (node red _ _ _ _) := tt
| _                  := ff

section insert

variables (lt : α → α → Prop) [decidable_rel lt]

def ins : rbnode α β → Π k : α, β k → rbnode α β
| leaf                 kx vx := node red leaf kx vx leaf
| (node red a ky vy b) kx vx :=
   (match cmp_using lt kx ky with
    | ordering.lt := node red (ins a kx vx) ky vy b
    | ordering.eq := node red a kx vx b
    | ordering.gt := node red a ky vy (ins b kx vx))
| (node black a ky vy b) kx vx :=
    match cmp_using lt kx ky with
    | ordering.lt :=
      if a.is_red then balance1 (ins a kx vx) ky vy b
      else node black (ins a kx vx) ky vy b
    | ordering.eq := node black a kx vx b
    | ordering.gt :=
      if b.is_red then balance2 (ins b kx vx) ky vy a
      else node black a ky vy (ins b kx vx)

def set_black : rbnode α β → rbnode α β
| (node _ l k v r) := node black l k v r
| e                := e

def insert (t : rbnode α β) (k : α) (v : β k) : rbnode α β :=
if is_red t then set_black (ins lt t k v)
else ins lt t k v

end insert

section membership
variable (lt : α → α → Prop)

variable [decidable_rel lt]

def find_core : rbnode α β → Π k : α, option (Σ k : α, β k)
| leaf               x := none
| (node _ a ky vy b) x :=
  (match cmp_using lt x ky with
   | ordering.lt := find_core a x
   | ordering.eq := some ⟨ky, vy⟩
   | ordering.gt := find_core b x)

def find {β : Type v} : rbnode α (λ _, β) → α → option β
| leaf                 x := none
| (node _ a ky vy b) x :=
  (match cmp_using lt x ky with
   | ordering.lt := find a x
   | ordering.eq := some vy
   | ordering.gt := find b x)

def lower_bound : rbnode α β → α → option (sigma β) → option (sigma β)
| leaf               x lb := lb
| (node _ a ky vy b) x lb :=
  (match cmp_using lt x ky with
   | ordering.lt := lower_bound a x lb
   | ordering.eq := some ⟨ky, vy⟩
   | ordering.gt := lower_bound b x (some ⟨ky, vy⟩))

end membership

inductive well_formed (lt : α → α → Prop) : rbnode α β → Prop
| leaf_wff : well_formed leaf
| insert_wff {n n' : rbnode α β} {k : α} {v : β k} [decidable_rel lt] : well_formed n → n' = insert lt n k v → well_formed n'

end rbnode

open rbnode

/- TODO(Leo): define d_rbmap -/

def rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : Type (max u v) :=
{t : rbnode α (λ _, β) // t.well_formed lt }

@[inline] def mk_rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : rbmap α β lt :=
⟨leaf, well_formed.leaf_wff lt⟩

namespace rbmap
variables {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Prop}

def depth (f : nat → nat → nat) (t : rbmap α β lt) : nat :=
t.val.depth f

@[inline] def fold (f : α → β → σ → σ) : rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.fold f b

@[inline] def rev_fold (f : α → β → σ → σ) : rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.rev_fold f b

@[inline] def mfold {m : Type w → Type w'} [monad m] (f : α → β → σ → m σ) : rbmap α β lt → σ → m σ
| ⟨t, _⟩ b := t.mfold f b

@[inline] def mfor {m : Type w → Type w'} [monad m] (f : α → β → m σ) (t : rbmap α β lt) : m punit :=
t.mfold (λ k v _, f k v *> pure ⟨⟩) ⟨⟩

@[inline] def empty : rbmap α β lt → bool
| ⟨leaf, _⟩ := tt
| _         := ff

@[specialize] def to_list : rbmap α β lt → list (α × β)
| ⟨t, _⟩ := t.rev_fold (λ k v ps, (k, v)::ps) []

@[inline] protected def min : rbmap α β lt → option (α × β)
| ⟨t, _⟩ :=
  match t.min with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

@[inline] protected def max : rbmap α β lt → option (α × β)
| ⟨t, _⟩ :=
  match t.max with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

instance [has_repr α] [has_repr β] : has_repr (rbmap α β lt) :=
⟨λ t, "rbmap_of " ++ repr t.to_list⟩

variables [decidable_rel lt]

def insert : rbmap α β lt → α → β → rbmap α β lt
| ⟨t, w⟩   k v := ⟨t.insert lt k v, well_formed.insert_wff w rfl⟩

@[specialize] def of_list : list (α × β) → rbmap α β lt
| []          := mk_rbmap _ _ _
| (⟨k,v⟩::xs) := (of_list xs).insert k v

def find_core : rbmap α β lt → α → option (Σ k : α, β)
| ⟨t, _⟩ x := t.find_core lt x

def find : rbmap α β lt → α → option β
| ⟨t, _⟩ x := t.find lt x

/-- (lower_bound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lower_bound : rbmap α β lt → α → option (Σ k : α, β)
| ⟨t, _⟩ x := t.lower_bound lt x none

@[inline] def contains (t : rbmap α β lt) (a : α) : bool :=
(t.find a).is_some

def from_list (l : list (α × β)) (lt : α → α → Prop) [decidable_rel lt] : rbmap α β lt :=
l.foldl (λ r p, r.insert p.1 p.2) (mk_rbmap α β lt)

@[inline] def all : rbmap α β lt → (α → β → bool) → bool
| ⟨t, _⟩ p := t.all p

@[inline] def any : rbmap α β lt → (α → β → bool) → bool
| ⟨t, _⟩ p := t.any p

end rbmap

def rbmap_of {α : Type u} {β : Type v} (l : list (α × β)) (lt : α → α → Prop) [decidable_rel lt] : rbmap α β lt :=
rbmap.from_list l lt
