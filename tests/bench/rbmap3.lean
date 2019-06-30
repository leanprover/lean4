prelude
import init.core init.io init.data.ordering

universes u v w

inductive Rbcolor
| red | black

inductive Rbnode (α : Type u) (β : α → Type v)
| leaf  {}                                                                        : Rbnode
| Node  (c : Rbcolor) (lchild : Rbnode) (key : α) (val : β key) (rchild : Rbnode) : Rbnode

instance Rbcolor.DecidableEq : DecidableEq Rbcolor :=
{decEq := λ a b, Rbcolor.casesOn a
  (Rbcolor.casesOn b (isTrue rfl) (isFalse (λ h, Rbcolor.noConfusion h)))
  (Rbcolor.casesOn b (isFalse (λ h, Rbcolor.noConfusion h)) (isTrue rfl))}

namespace Rbnode
variables {α : Type u} {β : α → Type v} {σ : Type w}

open Rbcolor

def depth (f : Nat → Nat → Nat) : Rbnode α β → Nat
| leaf               := 0
| (Node _ l _ _ r)   := (f (depth l) (depth r)) + 1

protected def min : Rbnode α β → Option (Sigma (λ k : α, β k))
| leaf                  := none
| (Node _ leaf k v _)   := some ⟨k, v⟩
| (Node _ l k v _)      := min l

protected def max : Rbnode α β → Option (Sigma (λ k : α, β k))
| leaf                  := none
| (Node _ _ k v leaf)   := some ⟨k, v⟩
| (Node _ _ k v r)      := max r

@[specialize] def fold (f : Π (k : α), β k → σ → σ) : Rbnode α β → σ → σ
| leaf b               := b
| (Node _ l k v r)   b := fold r (f k v (fold l b))

@[specialize] def revFold (f : Π (k : α), β k → σ → σ) : Rbnode α β → σ → σ
| leaf b               := b
| (Node _ l k v r)   b := revFold l (f k v (revFold r b))

@[specialize] def all (p : Π k : α, β k → Bool) : Rbnode α β → Bool
| leaf                 := true
| (Node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → Bool) : Rbnode α β → Bool
| leaf               := false
| (Node _ l k v r)   := p k v || any l || any r

def isRed : Rbnode α β → Bool
| (Node red _ _ _ _) := true
| _                  := false

def rotateLeft : Π (n : Rbnode α β), n ≠ leaf → Rbnode α β
| n@(Node hc hl hk hv (Node red xl xk xv xr)) _ :=
  if !isRed hl
  then (Node hc (Node red hl hk hv xl) xk xv xr)
  else n
| leaf h := absurd rfl h
| e _    := e

theorem ifNodeNodeNeLeaf {c : Prop} [Decidable c] {l1 l2 : Rbnode α β} {c1 k1 v1 r1 c2 k2 v2 r2} : (if c then Node c1 l1 k1 v1 r1 else Node c2 l2 k2 v2 r2) ≠ leaf :=
λ h, if hc : c
then have h1 : (if c then Node c1 l1 k1 v1 r1 else Node c2 l2 k2 v2 r2) = Node c1 l1 k1 v1 r1, from ifPos hc,
     Rbnode.noConfusion (Eq.trans h1.symm h)
else have h1 : (if c then Node c1 l1 k1 v1 r1 else Node c2 l2 k2 v2 r2) = Node c2 l2 k2 v2 r2, from ifNeg hc,
     Rbnode.noConfusion (Eq.trans h1.symm h)

theorem rotateLeftNeLeaf : ∀ (n : Rbnode α β) (h : n ≠ leaf), rotateLeft n h ≠ leaf
| (Node _ hl _ _ (Node red _ _ _ _)) _ h  := ifNodeNodeNeLeaf h
| leaf h _                                := absurd rfl h
| (Node _ _ _ _ (Node black _ _ _ _)) _ h := Rbnode.noConfusion h

def rotateRight : Π (n : Rbnode α β), n ≠ leaf → Rbnode α β
| n@(Node hc (Node red xl xk xv xr) hk hv hr) _ :=
  if isRed xl
  then (Node hc xl xk xv (Node red xr hk hv hr))
  else n
| leaf h := absurd rfl h
| e _    := e

theorem rotateRightNeLeaf : ∀ (n : Rbnode α β) (h : n ≠ leaf), rotateRight n h ≠ leaf
| (Node _ (Node red _ _ _ _) _ _ _) _ h   := ifNodeNodeNeLeaf h
| leaf h _                                := absurd rfl h
| (Node _ (Node black _ _ _ _) _ _ _) _ h := Rbnode.noConfusion h

def flip : Rbcolor → Rbcolor
| red   := black
| black := red

def flipColor : Rbnode α β → Rbnode α β
| (Node c l k v r) := Node (flip c) l k v r
| leaf             := leaf

def flipColors : Π (n : Rbnode α β), n ≠ leaf → Rbnode α β
| n@(Node c l k v r) _ :=
  if isRed l ∧ isRed r
  then Node (flip c) (flipColor l) k v (flipColor r)
  else n
| leaf h := absurd rfl h

def fixup (n : Rbnode α β) (h : n ≠ leaf) : Rbnode α β :=
let n₁ := rotateLeft n h in
let h₁ := (rotateLeftNeLeaf n h) in
let n₂ := rotateRight n₁ h₁ in
let h₂ := (rotateRightNeLeaf n₁ h₁) in
flipColors n₂ h₂

def setBlack : Rbnode α β → Rbnode α β
| (Node red l k v r) := Node black l k v r
| n                  := n

section insert
variables (lt : α → α → Prop) [DecidableRel lt]

def ins (x : α) (vx : β x) : Rbnode α β → Rbnode α β
| leaf             := Node red leaf x vx leaf
| (Node c l k v r) :=
  if lt x k then fixup (Node c (ins l) k v r) (λ h, Rbnode.noConfusion h)
  else if lt k x then fixup (Node c l k v (ins r)) (λ h, Rbnode.noConfusion h)
  else Node c l x vx r

def insert (t : Rbnode α β) (k : α) (v : β k) : Rbnode α β :=
setBlack (ins lt k v t)

end insert

section membership
variable (lt : α → α → Prop)

variable [DecidableRel lt]

def findCore : Rbnode α β → Π k : α, Option (Sigma (λ k : α, β k))
| leaf                 x := none
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
| insertWff {n n' : Rbnode α β} {k : α} {v : β k} [DecidableRel lt] : WellFormed n → n' = insert lt n k v → WellFormed n'

end Rbnode

open Rbnode

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

@[inline] def empty : Rbmap α β lt → Bool
| ⟨leaf, _⟩ := true
| _         := false

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

variables [DecidableRel lt]

def insert : Rbmap α β lt → α → β → Rbmap α β lt
| ⟨t, w⟩   k v := ⟨t.insert lt k v, WellFormed.insertWff w rfl⟩

@[specialize] def ofList : List (α × β) → Rbmap α β lt
| []          := mkRbmap _ _ _
| (⟨k,v⟩::xs) := (ofList xs).insert k v

def findCore : Rbmap α β lt → α → Option (Sigma (λ k : α, β))
| ⟨t, _⟩ x := t.findCore lt x

def find : Rbmap α β lt → α → Option β
| ⟨t, _⟩ x := t.find lt x

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lowerBound : Rbmap α β lt → α → Option (Sigma (λ k : α, β))
| ⟨t, _⟩ x := t.lowerBound lt x none

@[inline] def contains (t : Rbmap α β lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List (α × β)) (lt : α → α → Prop) [DecidableRel lt] : Rbmap α β lt :=
l.foldl (λ r p, r.insert p.1 p.2) (mkRbmap α β lt)

@[inline] def all : Rbmap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.all p

@[inline] def any : Rbmap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩ p := t.any p

end Rbmap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (lt : α → α → Prop) [DecidableRel lt] : Rbmap α β lt :=
Rbmap.fromList l lt

/- Test -/

@[reducible] def map : Type := Rbmap Nat Bool (<)

def mkMapAux : Nat → map → map
| 0 m := m
| (n+1) m := mkMapAux n (m.insert n (n % 10 = 0))

def mkMap (n : Nat) :=
mkMapAux n (mkRbmap Nat Bool (<))

def main (xs : List String) : IO UInt32 :=
let m := mkMap xs.head.toNat in
let v := Rbmap.fold (λ (k : Nat) (v : Bool) (r : Nat), if v then r + 1 else r) m 0 in
IO.println (toString v) *>
pure 0
