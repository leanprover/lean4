/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.repr init.data.option.basic

universes u v w w'

inductive Rbcolor
| red | black

inductive RBNode (α : Type u) (β : α → Type v)
| leaf  {}                                                                            : RBNode
| node  (color : Rbcolor) (lchild : RBNode) (key : α) (val : β key) (rchild : RBNode) : RBNode

namespace RBNode
variables {α : Type u} {β : α → Type v} {σ : Type w}

open Rbcolor Nat

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
| leaf               := 0
| (node _ l _ _ r)   := succ (f (depth l) (depth r))

protected def min : RBNode α β → Option (Σ k : α, β k)
| leaf                  := none
| (node _ leaf k v _)   := some ⟨k, v⟩
| (node _ l k v _)      := min l

protected def max : RBNode α β → Option (Σ k : α, β k)
| leaf                  := none
| (node _ _ k v leaf)   := some ⟨k, v⟩
| (node _ _ k v r)      := max r

@[specialize] def fold (f : σ → Π (k : α), β k → σ) : σ → RBNode α β → σ
| b leaf             := b
| b (node _ l k v r) := fold (f (fold b l) k v) r

@[specialize] def mfold {m : Type w → Type w'} [Monad m] (f : σ → Π (k : α), β k → m σ) : σ → RBNode α β → m σ
| b leaf             := pure b
| b (node _ l k v r) := do
  b ← mfold b l,
  b ← f b k v,
  mfold b r

@[specialize] def revFold (f : σ → Π (k : α), β k → σ) : σ → RBNode α β → σ
| b leaf               := b
| b (node _ l k v r)   := revFold (f (revFold b r) k v) l

@[specialize] def all (p : Π k : α, β k → Bool) : RBNode α β → Bool
| leaf                 := true
| (node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → Bool) : RBNode α β → Bool
| leaf                 := false
| (node _ l k v r)   := p k v || any l || any r

def singleton (k : α) (v : β k) : RBNode α β :=
node red leaf k v leaf

def balance1 : RBNode α β → RBNode α β → RBNode α β
| (node _ _ kv vv t) (node _ (node red l kx vx r₁) ky vy r₂) := node red (node black l kx vx r₁) ky vy (node black r₂ kv vv t)
| (node _ _ kv vv t) (node _ l₁ ky vy (node red l₂ kx vx r)) := node red (node black l₁ ky vy l₂) kx vx (node black r kv vv t)
| (node _ _ kv vv t) (node _ l  ky vy r)                     := node black (node red l ky vy r) kv vv t
| _                                                        _ := leaf -- unreachable

def balance2 : RBNode α β → RBNode α β → RBNode α β
| (node _ t kv vv _) (node _ (node red l kx₁ vx₁ r₁) ky vy r₂)  := node red (node black t kv vv l) kx₁ vx₁ (node black r₁ ky vy r₂)
| (node _ t kv vv _) (node _ l₁ ky vy (node red l₂ kx₂ vx₂ r₂)) := node red (node black t kv vv l₁) ky vy (node black l₂ kx₂ vx₂ r₂)
| (node _ t kv vv _) (node _ l ky vy r)                         := node black t kv vv (node red l ky vy r)
| _                                                        _    := leaf -- unreachable

def isRed : RBNode α β → Bool
| (node red _ _ _ _) := true
| _                  := false

section insert

variables (lt : α → α → Bool)

def ins : RBNode α β → Π k : α, β k → RBNode α β
| leaf                 kx vx := node red leaf kx vx leaf
| (node red a ky vy b) kx vx :=
   if lt kx ky then node red (ins a kx vx) ky vy b
   else if lt ky kx then node red a ky vy (ins b kx vx)
   else node red a kx vx b
| (node black a ky vy b) kx vx :=
    if lt kx ky then
      if isRed a then balance1 (node black leaf ky vy b) (ins a kx vx)
      else node black (ins a kx vx) ky vy b
    else if lt ky kx then
      if isRed b then balance2 (node black a ky vy leaf) (ins b kx vx)
      else node black a ky vy (ins b kx vx)
    else
       node black a kx vx b

def setBlack : RBNode α β → RBNode α β
| (node _ l k v r) := node black l k v r
| e                := e

def insert (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
if isRed t then setBlack (ins lt t k v)
else ins lt t k v

end insert

section membership
variable (lt : α → α → Bool)

def findCore : RBNode α β → Π k : α, Option (Σ k : α, β k)
| leaf               x := none
| (node _ a ky vy b) x :=
   if lt x ky then findCore a x
   else if lt ky x then findCore b x
   else some ⟨ky, vy⟩

def find {β : Type v} : RBNode α (λ _, β) → α → Option β
| leaf               x := none
| (node _ a ky vy b) x :=
  if lt x ky then find a x
  else if lt ky x then find b x
  else some vy

def lowerBound : RBNode α β → α → Option (Sigma β) → Option (Sigma β)
| leaf               x lb := lb
| (node _ a ky vy b) x lb :=
  if lt x ky then lowerBound a x lb
  else if lt ky x then lowerBound b x (some ⟨ky, vy⟩)
  else some ⟨ky, vy⟩

end membership

inductive WellFormed (lt : α → α → Bool) : RBNode α β → Prop
| leafWff : WellFormed leaf
| insertWff {n n' : RBNode α β} {k : α} {v : β k} : WellFormed n → n' = insert lt n k v → WellFormed n'

end RBNode

open RBNode

/- TODO(Leo): define dRBMap -/

def RBMap (α : Type u) (β : Type v) (lt : α → α → Bool) : Type (max u v) :=
{t : RBNode α (λ _, β) // t.WellFormed lt }

@[inline] def mkRBMap (α : Type u) (β : Type v) (lt : α → α → Bool) : RBMap α β lt :=
⟨leaf, WellFormed.leafWff lt⟩

instance (α : Type u) (β : Type v) (lt : α → α → Bool) : HasEmptyc (RBMap α β lt) :=
⟨mkRBMap α β lt⟩

namespace RBMap
variables {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Bool}

def depth (f : Nat → Nat → Nat) (t : RBMap α β lt) : Nat :=
t.val.depth f

@[inline] def fold (f : σ → α → β → σ) : σ → RBMap α β lt → σ
| b ⟨t, _⟩ := t.fold f b

@[inline] def revFold (f : σ → α → β → σ) : σ → RBMap α β lt → σ
| b ⟨t, _⟩ := t.revFold f b

@[inline] def mfold {m : Type w → Type w'} [Monad m] (f : σ → α → β → m σ) : σ → RBMap α β lt → m σ
| b ⟨t, _⟩ := t.mfold f b

@[inline] def mfor {m : Type w → Type w'} [Monad m] (f : α → β → m σ) (t : RBMap α β lt) : m PUnit :=
t.mfold (λ _ k v,  f k v *> pure ⟨⟩) ⟨⟩

@[inline] def isEmpty : RBMap α β lt → Bool
| ⟨leaf, _⟩ := true
| _         := false

@[specialize] def toList : RBMap α β lt → List (α × β)
| ⟨t, _⟩ := t.revFold (λ ps k v, (k, v)::ps) []

@[inline] protected def min : RBMap α β lt → Option (α × β)
| ⟨t, _⟩ :=
  match t.min with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

@[inline] protected def max : RBMap α β lt → Option (α × β)
| ⟨t, _⟩ :=
  match t.max with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

instance [HasRepr α] [HasRepr β] : HasRepr (RBMap α β lt) :=
⟨λ t, "rbmapOf " ++ repr t.toList⟩

def insert : RBMap α β lt → α → β → RBMap α β lt
| ⟨t, w⟩   k v := ⟨t.insert lt k v, WellFormed.insertWff w rfl⟩

@[specialize] def ofList : List (α × β) → RBMap α β lt
| []          := mkRBMap _ _ _
| (⟨k,v⟩::xs) := (ofList xs).insert k v

def findCore : RBMap α β lt → α → Option (Σ k : α, β)
| ⟨t, _⟩ x := t.findCore lt x

def find : RBMap α β lt → α → Option β
| ⟨t, _⟩ x := t.find lt x

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lowerBound : RBMap α β lt → α → Option (Σ k : α, β)
| ⟨t, _⟩ x := t.lowerBound lt x none

@[inline] def contains (t : RBMap α β lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List (α × β)) (lt : α → α → Bool) : RBMap α β lt :=
l.foldl (λ r p, r.insert p.1 p.2) (mkRBMap α β lt)

@[inline] def all : RBMap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.all p

@[inline] def any : RBMap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.any p

end RBMap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (lt : α → α → Bool) : RBMap α β lt :=
RBMap.fromList l lt
