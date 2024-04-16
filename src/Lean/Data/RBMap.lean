/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Ord
import Init.Data.Nat.Linear

namespace Lean
universe u v w w'

inductive RBColor where
  | red | black

inductive RBNode (α : Type u) (β : α → Type v) where
  | leaf                                                                                        : RBNode α β
  | node  (color : RBColor) (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}

open RBColor Nat

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
  | leaf           => 0
  | node _ l _ _ r => succ (f (depth f l) (depth f r))

protected def min : RBNode α β → Option (Sigma (fun k => β k))
  | leaf              => none
  | node _ leaf k v _ => some ⟨k, v⟩
  | node _ l _ _ _    => RBNode.min l

protected def max : RBNode α β → Option (Sigma (fun k => β k))
  | leaf              => none
  | node _ _ k v leaf => some ⟨k, v⟩
  | node _ _ _ _ r    => RBNode.max r

@[specialize] def fold (f : σ → (k : α) → β k → σ) : (init : σ) → RBNode α β → σ
  | b, leaf           => b
  | b, node _ l k v r => fold f (f (fold f b l) k v) r

@[specialize] def forM [Monad m] (f : (k : α) → β k → m Unit) : RBNode α β → m Unit
  | leaf           => pure ()
  | node _ l k v r => do forM f l; f k v; forM f r

@[specialize] def foldM [Monad m] (f : σ → (k : α) → β k → m σ) : (init : σ) → RBNode α β → m σ
  | b, leaf           => pure b
  | b, node _ l k v r => do
    let b ← foldM f b l
    let b ← f b k v
    foldM f b r

@[inline] protected def forIn [Monad m] (as : RBNode α β) (init : σ) (f : (k : α) → β k → σ → m (ForInStep σ)) : m σ := do
  let rec @[specialize] visit : RBNode α β → σ → m (ForInStep σ)
    | leaf, b           => return ForInStep.yield b
    | node _ l k v r, b => do
      match (← visit l b) with
      | r@(ForInStep.done _) => return r
      | ForInStep.yield b    =>
        match (← f k v b) with
        | r@(ForInStep.done _) => return r
        | ForInStep.yield b    => visit r b
  match (← visit as init) with
  | ForInStep.done b  => pure b
  | ForInStep.yield b => pure b

@[specialize] def revFold (f : σ → (k : α) → β k → σ) : (init : σ) → RBNode α β → σ
  | b, leaf           => b
  | b, node _ l k v r => revFold f (f (revFold f b r) k v) l

@[specialize] def all (p : (k : α) → β k → Bool) : RBNode α β → Bool
  | leaf           => true
  | node _ l k v r => p k v && all p l && all p r

@[specialize] def any (p : (k : α) → β k → Bool) : RBNode α β → Bool
  | leaf             => false
  | node _ l k v r => p k v || any p l || any p r

def singleton (k : α) (v : β k) : RBNode α β :=
  node red leaf k v leaf

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | node red (node red a kx vx b) ky vy c, kz, vz, d
  | node red a kx vx (node red b ky vy c), kz, vz, d => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a,                                     kx, vx, b => node black a kx vx b

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | a, kx, vx, node red (node red b ky vy c) kz vz d
  | a, kx, vx, node red b ky vy (node red c kz vz d) => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a, kx, vx, b                                     => node black a kx vx b

def isRed : RBNode α β → Bool
  | node red .. => true
  | _           => false

def isBlack : RBNode α β → Bool
  | node black .. => true
  | _             => false

section Insert

variable (cmp : α → α → Ordering)

@[specialize] def ins : RBNode α β → (k : α) → β k → RBNode α β
  | leaf,               kx, vx => node red leaf kx vx leaf
  | node red a ky vy b, kx, vx =>
    match cmp kx ky with
    | Ordering.lt => node red (ins a kx vx) ky vy b
    | Ordering.gt => node red a ky vy (ins b kx vx)
    | Ordering.eq => node red a kx vx b
  | node black a ky vy b, kx, vx =>
    match cmp kx ky with
    | Ordering.lt => balance1 (ins a kx vx) ky vy b
    | Ordering.gt => balance2 a ky vy (ins b kx vx)
    | Ordering.eq => node black a kx vx b

def setBlack : RBNode α β → RBNode α β
  | node _ l k v r => node black l k v r
  | e              => e

@[specialize] def insert (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
  if isRed t then setBlack (ins cmp t k v)
  else ins cmp t k v

end Insert

def setRed : RBNode α β → RBNode α β
  | node _ a k v b => node red a k v b
  | e              => e

def balLeft : RBNode α β → (k : α) → β k → RBNode α β → RBNode α β
  | node red a kx vx b,   k, v, r                    => node red (node black a kx vx b) k v r
  | l, k, v, node black a ky vy b                    => balance2 l k v (node red a ky vy b)
  | l, k, v, node red (node black a ky vy b) kz vz c => node red (node black l k v a) ky vy (balance2 b kz vz (setRed c))
  | l, k, v, r                                       => node red l k v r -- unreachable

def balRight (l : RBNode α β) (k : α) (v : β k) (r : RBNode α β) : RBNode α β :=
  match r with
  | (node red b ky vy c) => node red l k v (node black b ky vy c)
  | _ => match l with
    | node black a kx vx b                    => balance1 (node red a kx vx b) k v r
    | node red a kx vx (node black b ky vy c) => node red (balance1 (setRed a) kx vx b) ky vy (node black c k v r)
    | _                                       => node red l k v r -- unreachable

/-- The number of nodes in the tree. -/
@[local simp] def size : RBNode α β → Nat
  | leaf => 0
  | node _ x _ _ y => x.size + y.size + 1

def appendTrees :  RBNode α β → RBNode α β → RBNode α β
  | leaf, x => x
  | x, leaf => x
  | node red a kx vx b,   node red c ky vy d   =>
    match appendTrees b c with
    | node red b' kz vz c' => node red (node red a kx vx b') kz vz (node red c' ky vy d)
    | bc                   => node red a kx vx (node red bc ky vy d)
  | node black a kx vx b,   node black c ky vy d   =>
     match appendTrees b c with
     | node red b' kz vz c' => node red (node black a kx vx b') kz vz (node black c' ky vy d)
     | bc                   => balLeft a kx vx (node black bc ky vy d)
   | a, node red b kx vx c   => node red (appendTrees a b) kx vx c
   | node red a kx vx b,   c => node red a kx vx (appendTrees b c)
termination_by x y => x.size + y.size

section Erase

variable (cmp : α → α → Ordering)

@[specialize] def del (x : α) : RBNode α β → RBNode α β
  | leaf           => leaf
  | node _ a y v b =>
    match cmp x y with
    | Ordering.lt =>
      if a.isBlack then balLeft (del x a) y v b
      else node red (del x a) y v b
    | Ordering.gt =>
      if b.isBlack then balRight a y v (del x b)
      else node red a y v (del x b)
    | Ordering.eq => appendTrees a b

@[specialize] def erase (x : α) (t : RBNode α β) : RBNode α β :=
  let t := del cmp x t;
  t.setBlack

end Erase

section Membership
variable (cmp : α → α → Ordering)

@[specialize] def findCore : RBNode α β → (k : α) → Option (Sigma (fun k => β k))
  | leaf,             _ => none
  | node _ a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => findCore a x
    | Ordering.gt => findCore b x
    | Ordering.eq => some ⟨ky, vy⟩

@[specialize] def find {β : Type v} : RBNode α (fun _ => β) → α → Option β
  | leaf,             _ => none
  | node _ a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => find a x
    | Ordering.gt => find b x
    | Ordering.eq => some vy

@[specialize] def lowerBound : RBNode α β → α → Option (Sigma β) → Option (Sigma β)
  | leaf,             _, lb => lb
  | node _ a ky vy b, x, lb =>
    match cmp x ky with
    | Ordering.lt => lowerBound a x lb
    | Ordering.gt => lowerBound b x (some ⟨ky, vy⟩)
    | Ordering.eq => some ⟨ky, vy⟩

end Membership

inductive WellFormed (cmp : α → α → Ordering) : RBNode α β → Prop where
  | leafWff : WellFormed cmp leaf
  | insertWff {n n' : RBNode α β} {k : α} {v : β k} : WellFormed cmp n → n' = insert cmp n k v → WellFormed cmp n'
  | eraseWff {n n' : RBNode α β} {k : α} : WellFormed cmp n → n' = erase cmp k n → WellFormed cmp n'

section Map

@[specialize] def mapM {α : Type v} {β γ : α → Type v} {M : Type v → Type v} [Applicative M]
  (f : (a : α) → β a → M (γ a))
  : RBNode α β → M (RBNode α γ)
  | leaf => pure leaf
  | node color lchild key val rchild =>
    pure (node color · key · ·) <*> lchild.mapM f <*> f _ val <*> rchild.mapM f

@[specialize] def map {α : Type u} {β γ : α → Type v}
  (f : (a : α) → β a → γ a)
  : RBNode α β → RBNode α γ
  | leaf => leaf
  | node color lchild key val rchild => node color (lchild.map f) key (f key val) (rchild.map f)

@[specialize] def mapKeys {β : Type v} (f : α → α) : RBNode α (fun _ => β) → RBNode α (fun _ => β)
  | leaf           => leaf
  | node c l k v r => node c (mapKeys f l) (f k) v (mapKeys f r)

end Map

def toArray (n : RBNode α β) : Array (Sigma β) :=
  n.fold (init := ∅) fun acc k v => acc.push ⟨k,v⟩

instance : EmptyCollection (RBNode α β) := ⟨leaf⟩

end RBNode

open Lean.RBNode

/- TODO(Leo): define dRBMap -/

def RBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  {t : RBNode α (fun _ => β) // t.WellFormed cmp }

@[inline] def mkRBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : RBMap α β cmp :=
  ⟨leaf, WellFormed.leafWff⟩

@[inline] def RBMap.empty {α : Type u} {β : Type v} {cmp : α → α → Ordering} : RBMap α β cmp :=
  mkRBMap ..

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : EmptyCollection (RBMap α β cmp) :=
  ⟨RBMap.empty⟩

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Inhabited (RBMap α β cmp) := ⟨∅⟩

namespace RBMap
variable {α : Type u} {β : Type v} {σ : Type w} {cmp : α → α → Ordering}

def depth (f : Nat → Nat → Nat) (t : RBMap α β cmp) : Nat :=
  t.val.depth f

@[inline] def fold (f : σ → α → β → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.fold f b

@[inline] def revFold (f : σ → α → β → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.revFold f b

@[inline] def foldM [Monad m] (f : σ → α → β → m σ) : (init : σ) → RBMap α β cmp → m σ
  | b, ⟨t, _⟩ => t.foldM f b

@[inline] def forM [Monad m] (f : α → β → m PUnit) (t : RBMap α β cmp) : m PUnit :=
  t.foldM (fun _ k v => f k v) ⟨⟩

@[inline] protected def forIn [Monad m] (t : RBMap α β cmp) (init : σ) (f : (α × β) → σ → m (ForInStep σ)) : m σ :=
  t.val.forIn init (fun a b acc => f (a, b) acc)

instance : ForIn m (RBMap α β cmp) (α × β) where
  forIn := RBMap.forIn

@[inline] def isEmpty : RBMap α β cmp → Bool
  | ⟨leaf, _⟩ => true
  | _         => false

@[specialize] def toList : RBMap α β cmp → List (α × β)
  | ⟨t, _⟩ => t.revFold (fun ps k v => (k, v)::ps) []

/-- Returns the kv pair `(a,b)` such that `a ≤ k` for all keys in the RBMap. -/
@[inline] protected def min : RBMap α β cmp → Option (α × β)
  | ⟨t, _⟩ =>
    match t.min with
    | some ⟨k, v⟩ => some (k, v)
    | none        => none

/-- Returns the kv pair `(a,b)` such that `a ≥ k` for all keys in the RBMap. -/
@[inline] protected def max : RBMap α β cmp → Option (α × β)
  | ⟨t, _⟩ =>
    match t.max with
    | some ⟨k, v⟩ => some (k, v)
    | none        => none

instance [Repr α] [Repr β] : Repr (RBMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("Lean.rbmapOf " ++ repr m.toList) prec

@[inline] def insert : RBMap α β cmp → α → β → RBMap α β cmp
  | ⟨t, w⟩, k, v => ⟨t.insert cmp k v, WellFormed.insertWff w rfl⟩

@[inline] def erase : RBMap α β cmp → α → RBMap α β cmp
  | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

@[specialize] def ofList : List (α × β) → RBMap α β cmp
  | []        => mkRBMap ..
  | ⟨k,v⟩::xs => (ofList xs).insert k v

@[inline] def findCore? : RBMap α β cmp → α → Option (Sigma (fun (_ : α) => β))
  | ⟨t, _⟩, x => t.findCore cmp x

@[inline] def find? : RBMap α β cmp → α → Option β
  | ⟨t, _⟩, x => t.find cmp x

@[inline] def findD (t : RBMap α β cmp) (k : α) (v₀ : β) : β :=
  (t.find? k).getD v₀

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
@[inline] def lowerBound : RBMap α β cmp → α → Option (Sigma (fun (_ : α) => β))
  | ⟨t, _⟩, x => t.lowerBound cmp x none

/-- Returns true if the given key `a` is in the RBMap. -/
@[inline] def contains (t : RBMap α β cmp) (a : α) : Bool :=
  (t.find? a).isSome

@[inline] def fromList (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) (mkRBMap α β cmp)

@[inline] def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) (mkRBMap α β cmp)

/-- Returns true if the given predicate is true for all items in the RBMap. -/
@[inline] def all : RBMap α β cmp → (α → β → Bool) → Bool
  | ⟨t, _⟩, p => t.all p

/-- Returns true if the given predicate is true for any item in the RBMap. -/
@[inline] def any : RBMap α β cmp → (α → β → Bool) → Bool
  | ⟨t, _⟩, p => t.any p

/-- The number of items in the RBMap. -/
def size (m : RBMap α β cmp) : Nat :=
  m.fold (fun sz _ _ => sz+1) 0

def maxDepth (t : RBMap α β cmp) : Nat :=
  t.val.depth Nat.max

@[inline] def min! [Inhabited α] [Inhabited β] (t : RBMap α β cmp) : α × β :=
  match t.min with
  | some p => p
  | none   => panic! "map is empty"

@[inline] def max! [Inhabited α] [Inhabited β] (t : RBMap α β cmp) : α × β :=
  match t.max with
  | some p => p
  | none   => panic! "map is empty"

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def find! [Inhabited β] (t : RBMap α β cmp) (k : α) : β :=
  match t.find? k with
  | some b => b
  | none   => panic! "key is not in the map"

/-- Merges the maps `t₁` and `t₂`, if a key `a : α` exists in both,
then use `mergeFn a b₁ b₂` to produce the new merged value. -/
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  t₂.fold (init := t₁) fun t₁ a b₂ =>
    t₁.insert a <|
      match t₁.find? a with
      | some b₁ => mergeFn a b₁ b₂
      | none => b₂

/-- Intersects the maps `t₁` and `t₂` using `mergeFn a b₁ b₂` to produce the new value. -/
def intersectBy {γ : Type v₁} {δ : Type v₂} (mergeFn : α → β → γ → δ) (t₁ : RBMap α β cmp) (t₂ : RBMap α γ cmp) : RBMap α δ cmp :=
  t₁.fold (init := ∅) fun acc a b₁ =>
      match t₂.find? a with
      | some b₂ => acc.insert a <| mergeFn a b₁ b₂
      | none => acc

@[simp] theorem isRed_mapKeys : (n : RBNode α (fun _ => β)) → (n.mapKeys f).isRed = n.isRed
  | node .red ..   => rfl
  | node .black .. => rfl
  | leaf           => rfl

@[simp] theorem isBlack_mapKeys : (n : RBNode α (fun _ => β)) → (n.mapKeys f).isBlack = n.isBlack
  | node .red ..   => rfl
  | node .black .. => rfl
  | leaf           => rfl

@[simp] theorem mapKeys_setBlack :
    (n : RBNode α (fun _ => β)) → n.setBlack.mapKeys f = (n.mapKeys f).setBlack
  | node .red ..   => rfl
  | node .black .. => rfl
  | leaf           => rfl

@[simp] theorem mapKeys_setRed :
    (n : RBNode α (fun _ => β)) → n.setRed.mapKeys f = (n.mapKeys f).setRed
  | node .red ..   => rfl
  | node .black .. => rfl
  | leaf           => rfl

@[simp] theorem mapKeys_balance1 : (a b : RBNode α (fun _ => β)) → (k : α) → (v : β) →
    (a.balance1 k v b).mapKeys f = (a.mapKeys f).balance1 (f k) v (b.mapKeys f)
  | leaf, _, _, _ => by simp [mapKeys, balance1]
  | node .red (node .red a kx vx b) ky vy c, d, kz, vz => by simp [mapKeys,balance1]
  | node .red .leaf kx vx .leaf, d, kz, vz => by simp [mapKeys,balance1]
  | node .red (.leaf) kx vx (node .red b ky vy c), d, kz, vz => by simp [mapKeys,balance1]
  | node .red (node .black ..) kx vx (node .red b ky vy c), d, kz, vz => by simp [mapKeys,balance1]
  | node .red (.leaf) kx vx (node .black b ky vy c), d, kz, vz => by simp [mapKeys,balance1]
  | node .red (node .black ..) kx vx .leaf, d, kz, vz => by simp [mapKeys,balance1]
  | node .red (node .black ..) kx vx (node .black b ky vy c), d, kz, vz => by simp [mapKeys,balance1]
  | node .black _ ky vy c, d, kz, vz => by simp [mapKeys,balance1]

@[simp] theorem mapKeys_balance2 : (a b : RBNode α (fun _ => β)) → (k : α) → (v : β) →
    (a.balance2 k v b).mapKeys f = (a.mapKeys f).balance2 (f k) v (b.mapKeys f)
  | _, leaf, _, _ => by simp [mapKeys, balance2]
  | _, node .red (node .red a kx vx b) ky vy c, kz, vz => by simp [mapKeys,balance2]
  | _, node .red .leaf kx vx .leaf, kz, vz => by simp [mapKeys,balance2]
  | _, node .red (.leaf) kx vx (node .red b ky vy c), kz, vz => by simp [mapKeys,balance2]
  | _, node .red (node .black ..) kx vx (node .red b ky vy c), kz, vz => by simp [mapKeys,balance2]
  | _, node .red (.leaf) kx vx (node .black b ky vy c), kz, vz => by simp [mapKeys,balance2]
  | _, node .red (node .black ..) kx vx .leaf, kz, vz => by simp [mapKeys,balance2]
  | _, node .red (node .black ..) kx vx (node .black b ky vy c), kz, vz => by simp [mapKeys,balance2]
  | _, node .black _ ky vy c, kz, vz => by simp [mapKeys,balance2]

@[simp] theorem mapKeys_balLeft : (a b : RBNode α (fun _ => β)) → (k : α) → (v : β) →
    (a.balLeft k v b).mapKeys f = (a.mapKeys f).balLeft (f k) v (b.mapKeys f)
  | leaf, leaf, _, _ => by simp [mapKeys, balLeft]
  | leaf, node .black .., _, _ => by simp [mapKeys, balLeft]
  | leaf, node .red .leaf .., _, _ => by simp [mapKeys, balLeft]
  | leaf, node .red (node .black ..) .., _, _ => by simp [mapKeys, balLeft]
  | leaf, node .red (node .red ..) .., _, _ => by simp [mapKeys, balLeft]
  | node .red .., d, kz, vz => by simp [mapKeys, balLeft]
  | node .black .., leaf, _, _ => by simp [mapKeys, balLeft]
  | node .black .., node .black .., _, _ => by simp [mapKeys, balLeft]
  | node .black .., node .red .leaf .., _, _ => by simp [mapKeys, balLeft]
  | node .black .., node .red (node .black ..) .., _, _ => by simp [mapKeys, balLeft]
  | node .black .., node .red (node .red ..) .., _, _ => by simp [mapKeys, balLeft]

@[simp] theorem mapKeys_balRight : (a b : RBNode α (fun _ => β)) → (k : α) → (v : β) →
    (a.balRight k v b).mapKeys f = (a.mapKeys f).balRight (f k) v (b.mapKeys f)
  | _, node .red _ .., _, _ => by simp [mapKeys, balRight]
  | leaf, leaf, _, _ => by simp [mapKeys, balRight]
  | node .black .., leaf, _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ leaf, leaf, _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ (node .black .. ), leaf, _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ (node .red .. ), leaf, _, _ => by simp [mapKeys, balRight]
  | leaf, node .black .., _, _ => by simp [mapKeys, balRight]
  | node .black .., node .black .., _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ leaf, node .black .., _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ (node .black .. ), node .black .., _, _ => by simp [mapKeys, balRight]
  | node .red _ _ _ (node .red .. ), node .black .., _, _ => by simp [mapKeys, balRight]

@[simp]
theorem mapKeys_ins (f : α → α) (hf : ∀ x y, cmp (f x) (f y) = cmp x y) :
    (n : RBNode α (fun _ => β)) → (k : α) → (v : β) →
    (n.ins cmp k v).mapKeys f = (n.mapKeys f).ins cmp (f k) v
  | leaf,               kx, vx => by simp [ins, mapKeys]
  | node .red a ky vy b, kx, vx => by
    simp only [ins, mapKeys, hf]
    split <;> simp only [ins, mapKeys, hf, mapKeys_ins f hf]
  | node .black a ky vy b, kx, vx => by
    simp only [ins, mapKeys, hf]
    split <;> simp only [ins, mapKeys, hf, mapKeys_ins f hf, mapKeys_balance1, mapKeys_balance2]

@[simp]
theorem mapKeys_appendTrees (f : α → α) :
    (a b : RBNode α (fun _ => β)) → (a.appendTrees b).mapKeys f = (a.mapKeys f).appendTrees (b.mapKeys f)
  | leaf, leaf => by simp [appendTrees, mapKeys]
  | leaf, node .red b ky vy c => by simp [appendTrees, mapKeys]
  | leaf, node .black b ky vy c => by simp [appendTrees, mapKeys]
  | node .red a kx vx b, leaf => by simp [appendTrees, mapKeys]
  | node .black a kx vx b, leaf => by simp [appendTrees, mapKeys]
  | node .red a kx vx b, node .red c ky vy d => by
    simp [appendTrees, mapKeys]
    rw [← mapKeys_appendTrees]
    match b.appendTrees c  with
    | leaf => simp [*, mapKeys]
    | node .red .. => simp [*, mapKeys]
    | node .black .. => simp [*, mapKeys]
  | node .black a kx vx b, node .black c ky vy d => by
    simp [appendTrees, mapKeys]
    rw [← mapKeys_appendTrees]
    match b.appendTrees c  with
    | leaf => simp [*, mapKeys]
    | node .red .. => simp [*, mapKeys]
    | node .black .. => simp [*, mapKeys]
  | node .red a kx vx b, node .black c ky vy d => by
    -- simp [mapKeys, appendTrees, mapKeys_appendTrees] goes astray
    rw [mapKeys, appendTrees, appendTrees, mapKeys, mapKeys, mapKeys_appendTrees, mapKeys]
    all_goals simp [mapKeys]
  | node .black a kx vx b, node .red c ky vy d => by
    rw [mapKeys, appendTrees, mapKeys, mapKeys, mapKeys_appendTrees, mapKeys, appendTrees]
    all_goals simp [mapKeys]

@[simp]
theorem mapKeys_del (f : α → α) (hf : ∀ x y, cmp (f x) (f y) = cmp x y) :
    (n : RBNode α (fun _ => β)) → (k : α) →
    (n.del cmp k).mapKeys f = (n.mapKeys f).del cmp (f k)
  | leaf, _ => by simp [del, mapKeys]
  | node .red a ky vy b, kx => by
    simp only [del, mapKeys, hf, isBlack_mapKeys]
    split <;> (try split) <;>
      simp only [mapKeys, hf, mapKeys_del f hf, mapKeys_balLeft, mapKeys_balRight, mapKeys_appendTrees]
  | node .black a ky vy b, kx => by
    simp only [del, mapKeys, hf, isBlack_mapKeys]
    split <;> (try split) <;>
      simp only [mapKeys, hf, mapKeys_del f hf, mapKeys_balLeft, mapKeys_balRight, mapKeys_appendTrees]

@[simp]
theorem mapKeys_insert (f : α → α) (hf : ∀ x y, cmp (f x) (f y) = cmp x y) (n : RBNode α (fun _ => β)):
    (n.insert cmp k v).mapKeys f = (n.mapKeys f).insert cmp (f k) v := by
  unfold RBNode.insert
  rw [isRed_mapKeys]
  split <;> simp [hf]

@[simp]
theorem mapKeys_erase (f : α → α) (hf : ∀ x y, cmp (f x) (f y) = cmp x y) (n : RBNode α (fun _ => β)):
    (n.erase cmp k).mapKeys f = (n.mapKeys f).erase cmp (f k) := by
  unfold RBNode.erase
  simp [hf]


theorem mapKeys_WellFormed {f : α → α} (hf : ∀ x y, cmp (f x) (f y) = cmp x y) {t : RBNode α (fun _ => β)} :
    WellFormed cmp t → WellFormed cmp (mapKeys f t) := by
  intro wf
  induction wf with
  | leafWff => exact .leafWff
  | insertWff w h ih => rw [h, mapKeys_insert f hf]; exact WellFormed.insertWff ih (by rfl)
  | eraseWff w h ih => rw [h, mapKeys_erase f hf]; exact WellFormed.eraseWff ih (by rfl)

def mapKeysMono (f : α → α) (hf : ∀ x y, cmp (f x) (f y) = cmp x y) : RBMap α β cmp → RBMap α β cmp
  | ⟨t, w⟩ => ⟨t.mapKeys f, mapKeys_WellFormed hf w⟩

end RBMap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBMap.fromList l cmp
