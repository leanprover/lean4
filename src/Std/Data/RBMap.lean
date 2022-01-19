/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Std
universe u v w w'

inductive Rbcolor where
  | red | black

inductive RBNode (α : Type u) (β : α → Type v) where
  | leaf                                                                                        : RBNode α β
  | node  (color : Rbcolor) (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}

open Std.Rbcolor Nat

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
  | leaf           => 0
  | node _ l _ _ r => succ (f (depth f l) (depth f r))

protected def min : RBNode α β → Option (Sigma (fun k => β k))
  | leaf              => none
  | node _ leaf k v _ => some ⟨k, v⟩
  | node _ l k v _    => RBNode.min l

protected def max : RBNode α β → Option (Sigma (fun k => β k))
  | leaf              => none
  | node _ _ k v leaf => some ⟨k, v⟩
  | node _ _ k v r    => RBNode.max r

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

@[inline] def balance1 : (a : α) → β a → RBNode α β → RBNode α β → RBNode α β
  | kv, vv, t, node _ (node red l kx vx r₁) ky vy r₂   => node red (node black l kx vx r₁) ky vy (node black r₂ kv vv t)
  | kv, vv, t, node _ l₁ ky vy (node red l₂ kx vx r)   => node red (node black l₁ ky vy l₂) kx vx (node black r kv vv t)
  | kv, vv, t, node _ l  ky vy r                       => node black (node red l ky vy r) kv vv t
  | _,  _,  _,                                       _ => leaf -- unreachable

@[inline] def balance2 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | t, kv, vv, node _ (node red l kx₁ vx₁ r₁) ky vy r₂  => node red (node black t kv vv l) kx₁ vx₁ (node black r₁ ky vy r₂)
  | t, kv, vv, node _ l₁ ky vy (node red l₂ kx₂ vx₂ r₂) => node red (node black t kv vv l₁) ky vy (node black l₂ kx₂ vx₂ r₂)
  | t, kv, vv, node _ l ky vy r                         => node black t kv vv (node red l ky vy r)
  | _, _,  _,                                        _  => leaf -- unreachable

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
    | Ordering.lt =>
      if isRed a then balance1 ky vy b (ins a kx vx)
        else node black (ins a kx vx) ky vy b
    | Ordering.gt =>
        if isRed b then balance2 a ky vy (ins b kx vx)
        else node black a ky vy (ins b kx vx)
    | Ordering.eq => node black a kx vx b

def setBlack : RBNode α β → RBNode α β
  | node _ l k v r => node black l k v r
  | e              => e

@[specialize] def insert (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
  if isRed t then setBlack (ins cmp t k v)
  else ins cmp t k v

end Insert

def balance₃ (a : RBNode α β) (k : α) (v : β k) (d : RBNode α β) : RBNode α β :=
  match a with
  | node red (node red a kx vx b) ky vy c => node red (node black a kx vx b) ky vy (node black c k v d)
  | node red a kx vx (node red b ky vy c) => node red (node black a kx vx b) ky vy (node black c k v d)
  | a => match d with
    | node red b ky vy (node red c kz vz d)   => node red (node black a k v b) ky vy (node black c kz vz d)
    | node red (node red b ky vy c) kz vz d   => node red (node black a k v b) ky vy (node black c kz vz d)
    | _                                       => node black a k v d

def setRed : RBNode α β → RBNode α β
  | node _ a k v b => node red a k v b
  | e              => e

def balLeft : RBNode α β → (k : α) → β k → RBNode α β → RBNode α β
  | node red a kx vx b,   k, v, r                    => node red (node black a kx vx b) k v r
  | l, k, v, node black a ky vy b                    => balance₃ l k v (node red a ky vy b)
  | l, k, v, node red (node black a ky vy b) kz vz c => node red (node black l k v a) ky vy (balance₃ b kz vz (setRed c))
  | l, k, v, r                                       => node red l k v r -- unreachable

def balRight (l : RBNode α β) (k : α) (v : β k) (r : RBNode α β) : RBNode α β :=
  match r with
  | (node red b ky vy c) => node red l k v (node black b ky vy c)
  | _ => match l with
    | node black a kx vx b                    => balance₃ (node red a kx vx b) k v r
    | node red a kx vx (node black b ky vy c) => node red (balance₃ (setRed a) kx vx b) ky vy (node black c k v r)
    | _                                       => node red l k v r -- unreachable

-- TODO: use wellfounded recursion
partial def appendTrees :  RBNode α β → RBNode α β → RBNode α β
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
  | leaf,             x => none
  | node _ a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => findCore a x
    | Ordering.gt => findCore b x
    | Ordering.eq => some ⟨ky, vy⟩

@[specialize] def find {β : Type v} : RBNode α (fun _ => β) → α → Option β
  | leaf,             x => none
  | node _ a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => find a x
    | Ordering.gt => find b x
    | Ordering.eq => some vy

@[specialize] def lowerBound : RBNode α β → α → Option (Sigma β) → Option (Sigma β)
  | leaf,             x, lb => lb
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

end RBNode

open Std.RBNode

/- TODO(Leo): define dRBMap -/

def RBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  {t : RBNode α (fun _ => β) // t.WellFormed cmp }

@[inline] def mkRBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : RBMap α β cmp :=
  ⟨leaf, WellFormed.leafWff⟩

@[inline] def RBMap.empty {α : Type u} {β : Type v} {cmp : α → α → Ordering} : RBMap α β cmp :=
  mkRBMap ..

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : EmptyCollection (RBMap α β cmp) :=
  ⟨RBMap.empty⟩

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

@[inline] protected def min : RBMap α β cmp → Option (α × β)
  | ⟨t, _⟩ =>
    match t.min with
    | some ⟨k, v⟩ => some (k, v)
    | none        => none

@[inline] protected def max : RBMap α β cmp → Option (α × β)
  | ⟨t, _⟩ =>
    match t.max with
    | some ⟨k, v⟩ => some (k, v)
    | none        => none

instance [Repr α] [Repr β] : Repr (RBMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.rbmapOf " ++ repr m.toList) prec

@[inline] def insert : RBMap α β cmp → α → β → RBMap α β cmp
  | ⟨t, w⟩, k, v => ⟨t.insert cmp k v, WellFormed.insertWff w rfl⟩

@[inline] def erase : RBMap α β cmp → α → RBMap α β cmp
  | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

@[specialize] def ofList : List (α × β) → RBMap α β cmp
  | []        => mkRBMap ..
  | ⟨k,v⟩::xs => (ofList xs).insert k v

@[inline] def findCore? : RBMap α β cmp → α → Option (Sigma (fun (k : α) => β))
  | ⟨t, _⟩, x => t.findCore cmp x

@[inline] def find? : RBMap α β cmp → α → Option β
  | ⟨t, _⟩, x => t.find cmp x

@[inline] def findD (t : RBMap α β cmp) (k : α) (v₀ : β) : β :=
  (t.find? k).getD v₀

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
@[inline] def lowerBound : RBMap α β cmp → α → Option (Sigma (fun (k : α) => β))
  | ⟨t, _⟩, x => t.lowerBound cmp x none

@[inline] def contains (t : RBMap α β cmp) (a : α) : Bool :=
  (t.find? a).isSome

@[inline] def fromList (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) (mkRBMap α β cmp)

@[inline] def all : RBMap α β cmp → (α → β → Bool) → Bool
  | ⟨t, _⟩, p => t.all p

@[inline] def any : RBMap α β cmp → (α → β → Bool) → Bool
  | ⟨t, _⟩, p => t.any p

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

@[inline] def find! [Inhabited β] (t : RBMap α β cmp) (k : α) : β :=
  match t.find? k with
  | some b => b
  | none   => panic! "key is not in the map"

end RBMap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBMap.fromList l cmp

end Std
