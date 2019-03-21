/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universes u v w w'
namespace tst
inductive Rbcolor
| red | black

inductive Rbnode (α : Type u) (β : α → Type v)
| leaf  {}                                                                        : Rbnode
| Node  (c : Rbcolor) (lchild : Rbnode) (key : α) (val : β key) (rchild : Rbnode) : Rbnode

namespace Rbnode
variables {α : Type u} {β : α → Type v} {σ : Type w}

instance Rbcolor.DecidableEq : DecidableEq Rbcolor :=
{decEq := λ a b, Rbcolor.casesOn a
  (Rbcolor.casesOn b (isTrue rfl) (isFalse (λ h, Rbcolor.noConfusion h)))
  (Rbcolor.casesOn b (isFalse (λ h, Rbcolor.noConfusion h)) (isTrue rfl))}

open tst.Rbcolor

def depth (f : Nat → Nat → Nat) : Rbnode α β → Nat
| leaf               := 0
| (Node _ l _ _ r)   := (f (depth l) (depth r))+1

protected def min : Rbnode α β → Option (Σ k : α, β k)
| leaf                    := none
| (Node _ leaf k v _)     := some ⟨k, v⟩
| (Node _ l _ _ _)        := min l

protected def max : Rbnode α β → Option (Σ k : α, β k)
| leaf                  := none
| (Node _ _ k v leaf)   := some ⟨k, v⟩
| (Node _ _ _ _ r)      := max r

@[specialize] def fold (f : Π (k : α), β k → σ → σ) : Rbnode α β → σ → σ
| leaf b               := b
| (Node _ l k v r)   b := fold r (f k v (fold l b))

@[specialize] def mfold {m : Type w → Type w'} [Monad m] (f : Π (k : α), β k → σ → m σ) : Rbnode α β → σ → m σ
| leaf b               := pure b
| (Node _ l k v r) b   := do b₁ ← mfold l b, b₂ ← f k v b₁, mfold r b₂

@[specialize] def revFold (f : Π (k : α), β k → σ → σ) : Rbnode α β → σ → σ
| leaf b               := b
| (Node _ l k v r)   b := revFold l (f k v (revFold r b))

@[specialize] def all (p : Π k : α, β k → Bool) : Rbnode α β → Bool
| leaf                 := tt
| (Node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → Bool) : Rbnode α β → Bool
| leaf               := ff
| (Node _ l k v r)   := p k v || any l || any r

def balance (rb : Rbcolor) (t1 : Rbnode α β) (k : α) (vk : β k) (t2 : Rbnode α β) :=
match rb with
 | red   := Node red t1 k vk t2
 | black :=
 match t1 with
 | Node red (Node red a x vx b) y vy c :=
    Node red (Node black a x vx b) y vy (Node black c k vk t2)
 | Node red a x vx (Node red b y vy c) :=
    Node red (Node black a x vx b) y vy (Node black c k vk t2)
 | a := match t2 with
            | Node red (Node red b y vy c) z vz d :=
                Node red (Node black t1 k vk b) y vy (Node black c z vz d)
            | Node red b y vy (Node red c z vz d) :=
                Node red (Node black t1 k vk b) y vy (Node black c z vz d)
            | _ := Node black t1 k vk t2

def makeBlack (t : Rbnode α β) :=
match t with
| leaf            := leaf
| Node _ a x vx b := Node black a x vx b

section insert
variables (lt : α → α → Prop) [decidableRel lt]

def ins (x : α) (vx : β x) : Rbnode α β → Rbnode α β
| leaf := Node red leaf x vx leaf
| (Node c a y vy b) :=
  if lt x y then balance c (ins a) y vy b
  else if lt y x then balance c a y vy (ins b)
  else Node c a x vx b

def insert (t : Rbnode α β) (k : α) (v : β k) : Rbnode α β :=
makeBlack (ins lt k v t)

end insert

section membership
variable (lt : α → α → Prop)

variable [decidableRel lt]

def findCore : Rbnode α β → Π k : α, Option (Σ k : α, β k)
| leaf               x := none
| (Node _ a ky vy b) x :=
  (match cmpUsing lt x ky with
   | Ordering.lt := findCore a x
   | Ordering.Eq := some ⟨ky, vy⟩
   | Ordering.gt := findCore b x)

def find {β : Type v} : Rbnode α (λ _, β) → α → Option β
| leaf                 x := none
| (Node _ a ky vy b) x :=
  (match cmpUsing lt x ky with
   | Ordering.lt := find a x
   | Ordering.Eq := some vy
   | Ordering.gt := find b x)

def lowerBound : Rbnode α β → α → Option (Sigma β) → Option (Sigma β)
| leaf                 x lb := lb
| (Node _ a ky vy b) x lb :=
  (match cmpUsing lt x ky with
   | Ordering.lt := lowerBound a x lb
   | Ordering.Eq := some ⟨ky, vy⟩
   | Ordering.gt := lowerBound b x (some ⟨ky, vy⟩))
end membership

inductive WellFormed (lt : α → α → Prop) : Rbnode α β → Prop
| leafWff : WellFormed leaf
| insertWff {n n' : Rbnode α β} {k : α} {v : β k} [decidableRel lt] : WellFormed n → n' = insert lt n k v → WellFormed n'

end Rbnode

open tst.Rbnode

/- TODO(Leo): define dRbmap -/

def Rbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : Type (max u v) :=
{t : Rbnode α (λ _, β) // t.WellFormed lt }

@[inline] def mkRbmap (α : Type u) (β : Type v) (lt : α → α → Prop) : Rbmap α β lt :=
⟨leaf, WellFormed.leafWff lt⟩

namespace Rbmap
variables {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Prop}

def depth (f : Nat → Nat → Nat) (t : Rbmap α β lt) : Nat :=
t.val.depth f

@[inline] def fold (f : α → β → σ → σ) : Rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.fold f b

@[inline] def revFold (f : α → β → σ → σ) : Rbmap α β lt → σ → σ
| ⟨t, _⟩ b := t.revFold f b

@[inline] def mfold {m : Type w → Type w'} [Monad m] (f : α → β → σ → m σ) : Rbmap α β lt → σ → m σ
| ⟨t, _⟩ b := t.mfold f b

@[inline] def mfor {m : Type w → Type w'} [Monad m] (f : α → β → m σ) (t : Rbmap α β lt) : m Punit :=
t.mfold (λ k v _, f k v *> pure ⟨⟩) ⟨⟩

@[inline] def Empty : Rbmap α β lt → Bool
| ⟨leaf, _⟩ := tt
| _         := ff

@[specialize] def toList : Rbmap α β lt → List (α × β)
| ⟨t, _⟩ := t.revFold (λ k v ps, (k, v)::ps) []

@[inline] protected def min : Rbmap α β lt → Option (α × β)
| ⟨t, _⟩ :=
  match t.min with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

@[inline] protected def max : Rbmap α β lt → Option (α × β)
| ⟨t, _⟩ :=
  match t.max with
  | some ⟨k, v⟩ := some (k, v)
  | none        := none

instance [HasRepr α] [HasRepr β] : HasRepr (Rbmap α β lt) :=
⟨λ t, "rbmapOf " ++ repr t.toList⟩

variables [decidableRel lt]

def insert : Rbmap α β lt → α → β → Rbmap α β lt
| ⟨t, w⟩   k v := ⟨t.insert lt k v, WellFormed.insertWff w rfl⟩

@[specialize] def ofList : List (α × β) → Rbmap α β lt
| []          := mkRbmap _ _ _
| (⟨k,v⟩::xs) := (ofList xs).insert k v

def findCore : Rbmap α β lt → α → Option (Σ k : α, β)
| ⟨t, _⟩ x := t.findCore lt x

def find : Rbmap α β lt → α → Option β
| ⟨t, _⟩ x := t.find lt x

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lowerBound : Rbmap α β lt → α → Option (Σ k : α, β)
| ⟨t, _⟩ x := t.lowerBound lt x none

@[inline] def contains (t : Rbmap α β lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List (α × β)) (lt : α → α → Prop) [decidableRel lt] : Rbmap α β lt :=
l.foldl (λ r p, r.insert p.1 p.2) (mkRbmap α β lt)

@[inline] def all : Rbmap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.all p

@[inline] def any : Rbmap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.any p

end Rbmap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (lt : α → α → Prop) [decidableRel lt] : Rbmap α β lt :=
Rbmap.fromList l lt

end tst

@[reducible] def map : Type := tst.Rbmap Nat Bool (<)

def mkMapAux : Nat → Nat → map → map
| 0     i m := m
| (n+1) i m := mkMapAux n (i+1) (tst.Rbmap.insert m i (i % 10 = 0))

def mkMap (n : Nat) :=
mkMapAux n 0 (tst.mkRbmap Nat Bool (<))

def main (xs : List String) : IO UInt32 :=
let m := mkMap xs.head.toNat in
let v := tst.Rbmap.fold (λ (k : Nat) (v : Bool) (r : Nat), if v then r + 1 else r) m 0 in
IO.println (toString v) *>
pure 0
