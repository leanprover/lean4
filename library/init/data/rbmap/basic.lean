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

@[specialize] def revFold (f : Π (k : α), β k → σ → σ) : rbnode α β → σ → σ
| leaf b               := b
| (node _ l k v r)   b := revFold l (f k v (revFold r b))

@[specialize] def all (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf                 := tt
| (node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf                 := ff
| (node _ l k v r)   := p k v || any l || any r

def balance1 : rbnode α β → rbnode α β → rbnode α β
| (node _ _ kv vv t) (node _ (node red l kx vx r₁) ky vy r₂) := node red (node black l kx vx r₁) ky vy (node black r₂ kv vv t)
| (node _ _ kv vv t) (node _ l₁ ky vy (node red l₂ kx vx r)) := node red (node black l₁ ky vy l₂) kx vx (node black r kv vv t)
| (node _ _ kv vv t) (node _ l  ky vy r)                     := node black (node red l ky vy r) kv vv t
| _                                                        _ := leaf -- unreachable

def balance2 : rbnode α β → rbnode α β → rbnode α β
| (node _ t kv vv _) (node _ (node red l kx₁ vx₁ r₁) ky vy r₂)  := node red (node black t kv vv l) kx₁ vx₁ (node black r₁ ky vy r₂)
| (node _ t kv vv _) (node _ l₁ ky vy (node red l₂ kx₂ vx₂ r₂)) := node red (node black t kv vv l₁) ky vy (node black l₂ kx₂ vx₂ r₂)
| (node _ t kv vv _) (node _ l ky vy r)                         := node black t kv vv (node red l ky vy r)
| _                                                        _    := leaf -- unreachable

def isRed : rbnode α β → bool
| (node red _ _ _ _) := tt
| _                  := ff

section insert

variables (lt : α → α → Prop) [decidableRel lt]

def ins : rbnode α β → Π k : α, β k → rbnode α β
| leaf                 kx vx := node red leaf kx vx leaf
| (node red a ky vy b) kx vx :=
   (match cmpUsing lt kx ky with
    | ordering.lt := node red (ins a kx vx) ky vy b
    | ordering.eq := node red a kx vx b
    | ordering.gt := node red a ky vy (ins b kx vx))
| (node black a ky vy b) kx vx :=
    match cmpUsing lt kx ky with
    | ordering.lt :=
      if isRed a then balance1 (node black leaf ky vy b) (ins a kx vx)
      else node black (ins a kx vx) ky vy b
    | ordering.eq := node black a kx vx b
    | ordering.gt :=
      if isRed b then balance2 (node black a ky vy leaf) (ins b kx vx)
      else node black a ky vy (ins b kx vx)

def setBlack : rbnode α β → rbnode α β
| (node _ l k v r) := node black l k v r
| e                := e

def insert (t : rbnode α β) (k : α) (v : β k) : rbnode α β :=
if isRed t then setBlack (ins lt t k v)
else ins lt t k v

end insert

section membership
variable (lt : α → α → Prop)

variable [decidableRel lt]

def findCore : rbnode α β → Π k : α, option (Σ k : α, β k)
| leaf               x := none
| (node _ a ky vy b) x :=
  (match cmpUsing lt x ky with
   | ordering.lt := findCore a x
   | ordering.eq := some ⟨ky, vy⟩
   | ordering.gt := findCore b x)

def find {β : Type v} : rbnode α (λ _, β) → α → option β
| leaf                 x := none
| (node _ a ky vy b) x :=
  (match cmpUsing lt x ky with
   | ordering.lt := find a x
   | ordering.eq := some vy
   | ordering.gt := find b x)

def lowerBound : rbnode α β → α → option (sigma β) → option (sigma β)
| leaf               x lb := lb
| (node _ a ky vy b) x lb :=
  (match cmpUsing lt x ky with
   | ordering.lt := lowerBound a x lb
   | ordering.eq := some ⟨ky, vy⟩
   | ordering.gt := lowerBound b x (some ⟨ky, vy⟩))

end membership

inductive wellFormed (lt : α → α → Prop) : rbnode α β → Prop
| leafWff : wellFormed leaf
| insertWff {n n' : rbnode α β} {k : α} {v : β k} [decidableRel lt] : wellFormed n → n' = insert lt n k v → wellFormed n'

end rbnode

open rbnode

/- TODO(Leo): define dRbmap -/

def rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : Type (max u v) :=
{t : rbnode α (λ _, β) // t.wellFormed lt }

@[inline] def mkRbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : rbmap α β lt :=
⟨leaf, wellFormed.leafWff lt⟩

namespace rbmap
variables {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Prop}

def depth (f : nat → nat → nat) (t : rbmap α β lt) : nat :=
t.val.depth f

@[inline] def fold (f : α → β → σ → σ) : rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.fold f b

@[inline] def revFold (f : α → β → σ → σ) : rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.revFold f b

@[inline] def mfold {m : Type w → Type w'} [monad m] (f : α → β → σ → m σ) : rbmap α β lt → σ → m σ
| ⟨t, _⟩ b := t.mfold f b

@[inline] def mfor {m : Type w → Type w'} [monad m] (f : α → β → m σ) (t : rbmap α β lt) : m punit :=
t.mfold (λ k v _, f k v *> pure ⟨⟩) ⟨⟩

@[inline] def empty : rbmap α β lt → bool
| ⟨leaf, _⟩ := tt
| _         := ff

@[specialize] def toList : rbmap α β lt → list (α × β)
| ⟨t, _⟩ := t.revFold (λ k v ps, (k, v)::ps) []

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

instance [hasRepr α] [hasRepr β] : hasRepr (rbmap α β lt) :=
⟨λ t, "rbmapOf " ++ repr t.toList⟩

variables [decidableRel lt]

def insert : rbmap α β lt → α → β → rbmap α β lt
| ⟨t, w⟩   k v := ⟨t.insert lt k v, wellFormed.insertWff w rfl⟩

@[specialize] def ofList : list (α × β) → rbmap α β lt
| []          := mkRbmap _ _ _
| (⟨k,v⟩::xs) := (ofList xs).insert k v

def findCore : rbmap α β lt → α → option (Σ k : α, β)
| ⟨t, _⟩ x := t.findCore lt x

def find : rbmap α β lt → α → option β
| ⟨t, _⟩ x := t.find lt x

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lowerBound : rbmap α β lt → α → option (Σ k : α, β)
| ⟨t, _⟩ x := t.lowerBound lt x none

@[inline] def contains (t : rbmap α β lt) (a : α) : bool :=
(t.find a).isSome

def fromList (l : list (α × β)) (lt : α → α → Prop) [decidableRel lt] : rbmap α β lt :=
l.foldl (λ r p, r.insert p.1 p.2) (mkRbmap α β lt)

@[inline] def all : rbmap α β lt → (α → β → bool) → bool
| ⟨t, _⟩ p := t.all p

@[inline] def any : rbmap α β lt → (α → β → bool) → bool
| ⟨t, _⟩ p := t.any p

end rbmap

def rbmapOf {α : Type u} {β : Type v} (l : list (α × β)) (lt : α → α → Prop) [decidableRel lt] : rbmap α β lt :=
rbmap.fromList l lt
