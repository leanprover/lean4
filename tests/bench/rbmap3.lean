prelude
import init.core init.system.io init.data.ordering

universe u v w

inductive RBColor
| red | black

inductive RBNode (α : Type u) (β : α → Type v)
| leaf  {}                                                                        : RBNode
| node  (c : RBColor) (lchild : RBNode) (key : α) (val : β key) (rchild : RBNode) : RBNode

instance RBColor.decidableEq : DecidableEq RBColor :=
{decEq := fun a b => RBColor.casesOn a
  (RBColor.casesOn b (isTrue rfl) (isFalse (fun h => RBColor.noConfusion h)))
  (RBColor.casesOn b (isFalse (fun h => RBColor.noConfusion h)) (isTrue rfl))}

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}

open RBColor

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
| leaf               => 0
| node _ l _ _ r     => (f (depth l) (depth r)) + 1

protected def min : RBNode α β → Option (Sigma (fun k => β k))
| leaf                  => none
| node _ leaf k v _     => some ⟨k, v⟩
| node _ l k v _        => min l

protected def max : RBNode α β → Option (Sigma (fun k => β k))
| leaf                  => none
| node _ _ k v leaf     => some ⟨k, v⟩
| node _ _ k v r        => max r

@[specialize] def fold (f : ∀ (k : α), β k → σ → σ) : RBNode α β → σ → σ
| leaf, b               => b
| node _ l k v r,     b => fold r (f k v (fold l b))

@[specialize] def revFold (f : ∀ (k : α), β k → σ → σ) : RBNode α β → σ → σ
| leaf, b               => b
| node _ l k v r,     b => revFold l (f k v (revFold r b))

@[specialize] def all (p : ∀ (k : α), β k → Bool) : RBNode α β → Bool
| leaf                 => true
| node _ l k v r       => p k v && all l && all r

@[specialize] def any (p : ∀ (k : α), β k → Bool) : RBNode α β → Bool
| leaf               => false
| node _ l k v r     => p k v || any l || any r

def isRed : RBNode α β → Bool
| node red _ _ _ _   => true
| _                  => false

def rotateLeft : ∀ (n : RBNode α β), n ≠ leaf → RBNode α β
| n@(node hc hl hk hv (node red xl xk xv xr)), _ =>
  if !isRed hl
  then (node hc (node red hl hk hv xl) xk xv xr)
  else n
| leaf, h => absurd rfl h
| e, _    => e

theorem if_node_node_ne_leaf {c : Prop} [Decidable c] {l1 l2 : RBNode α β} {c1 k1 v1 r1 c2 k2 v2 r2} : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) ≠ leaf :=
fun h => if hc : c
then have h1 : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) = node c1 l1 k1 v1 r1 from ifPos hc;
     RBNode.noConfusion (Eq.trans h1.symm h)
else have h1 : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) = node c2 l2 k2 v2 r2 from ifNeg hc;
     RBNode.noConfusion (Eq.trans h1.symm h)

theorem rotateLeft_ne_leaf : ∀ (n : RBNode α β) (h : n ≠ leaf), rotateLeft n h ≠ leaf
| node _ hl _ _ (node red _ _ _ _),   _, h  => if_node_node_ne_leaf h
| leaf, h, _                                => absurd rfl h
| node _ _ _ _ (node black _ _ _ _),   _, h => RBNode.noConfusion h

def rotateRight : ∀ (n : RBNode α β), n ≠ leaf → RBNode α β
| n@(node hc (node red xl xk xv xr) hk hv hr), _ =>
  if isRed xl
  then (node hc xl xk xv (node red xr hk hv hr))
  else n
| leaf, h => absurd rfl h
| e, _    => e

theorem rotateRight_ne_leaf : ∀ (n : RBNode α β) (h : n ≠ leaf), rotateRight n h ≠ leaf
| node _ (node red _ _ _ _) _ _ _,   _, h   => if_node_node_ne_leaf h
| leaf, h, _                                => absurd rfl h
| node _ (node black _ _ _ _) _ _ _,   _, h => RBNode.noConfusion h

def flip : RBColor → RBColor
| red   => black
| black => red

def flipColor : RBNode α β → RBNode α β
| node c l k v r   => node (flip c) l k v r
| leaf             => leaf

def flipColors : ∀ (n : RBNode α β), n ≠ leaf → RBNode α β
| n@(node c l k v r), _ =>
  if isRed l ∧ isRed r
  then node (flip c) (flipColor l) k v (flipColor r)
  else n
| leaf, h => absurd rfl h

def fixup (n : RBNode α β) (h : n ≠ leaf) : RBNode α β :=
let n₁ := rotateLeft n h;
let h₁ := (rotateLeft_ne_leaf n h);
let n₂ := rotateRight n₁ h₁;
let h₂ := (rotateRight_ne_leaf n₁ h₁);
flipColors n₂ h₂

def setBlack : RBNode α β → RBNode α β
| node red l k v r   => node black l k v r
| n                  => n

section insert
variable (lt : α → α → Prop) [DecidableRel lt]

def ins (x : α) (vx : β x) : RBNode α β → RBNode α β
| leaf             => node red leaf x vx leaf
| node c l k v r   =>
  if lt x k then fixup (node c (ins l) k v r) (fun h => RBNode.noConfusion h)
  else if lt k x then fixup (node c l k v (ins r)) (fun h => RBNode.noConfusion h)
  else node c l x vx r

def insert (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
setBlack (ins lt k v t)

end insert

section membership
variable (lt : α → α → Prop)

variable [DecidableRel lt]

def findCore : RBNode α β → ∀ (k : α), Option (Sigma (fun k => β k))
| leaf,                 x => none
| node _ a ky vy b,   x =>
  (match cmpUsing lt x ky with
   | Ordering.lt => findCore a x
   | Ordering.Eq => some ⟨ky, vy⟩
   | Ordering.gt => findCore b x)

def find {β : Type v} : RBNode α (fun _ => β) → α → Option β
| leaf,                 x => none
| node _ a ky vy b,   x =>
  (match cmpUsing lt x ky with
   | Ordering.lt => find a x
   | Ordering.Eq => some vy
   | Ordering.gt => find b x)

def lowerBound : RBNode α β → α → Option (Sigma β) → Option (Sigma β)
| leaf,                 x, lb => lb
| node _ a ky vy b,   x, lb =>
  (match cmpUsing lt x ky with
   | Ordering.lt => lowerBound a x lb
   | Ordering.Eq => some ⟨ky, vy⟩
   | Ordering.gt => lowerBound b x (some ⟨ky, vy⟩))

end membership

inductive WellFormed (lt : α → α → Prop) : RBNode α β → Prop
| leaf_wff : WellFormed leaf
| insert_wff {n n' : RBNode α β} {k : α} {v : β k} [DecidableRel lt] : WellFormed n → n' = insert lt n k v → WellFormed n'

end RBNode

open RBNode

/- TODO(Leo): define dRbmap -/

def RBMap (α : Type u) (β : Type v) (lt : α → α → Prop) : Type (max u v) :=
{t : RBNode α (fun _ => β) // t.WellFormed lt }

@[inline] def mkRBMap (α : Type u) (β : Type v) (lt : α → α → Prop) : RBMap α β lt :=
⟨leaf, WellFormed.leaf_wff lt⟩

namespace RBMap
variable {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Prop}

def depth (f : Nat → Nat → Nat) (t : RBMap α β lt) : Nat :=
t.val.depth f

@[inline] def fold (f : α → β → σ → σ) : RBMap α β lt → σ → σ
| ⟨t, _⟩, b => t.fold f b

@[inline] def revFold (f : α → β → σ → σ) : RBMap α β lt → σ → σ
| ⟨t, _⟩, b => t.revFold f b

@[inline] def empty : RBMap α β lt → Bool
| ⟨leaf, _⟩ => true
| _         => false

@[specialize] def toList : RBMap α β lt → List (α × β)
| ⟨t, _⟩ => t.revFold (fun k v ps => (k, v)::ps) []

@[inline] protected def min : RBMap α β lt → Option (α × β)
| ⟨t, _⟩ =>
  match t.min with
  | some ⟨k, v⟩ => some (k, v)
  | none        => none

@[inline] protected def max : RBMap α β lt → Option (α × β)
| ⟨t, _⟩ =>
  match t.max with
  | some ⟨k, v⟩ => some (k, v)
  | none        => none

instance [Repr α] [Repr β] : Repr (RBMap α β lt) :=
⟨fun t => "rbmapOf " ++ repr t.toList⟩

variable [DecidableRel lt]

def insert : RBMap α β lt → α → β → RBMap α β lt
| ⟨t, w⟩,   k, v => ⟨t.insert lt k v, WellFormed.insert_wff w rfl⟩

@[specialize] def ofList : List (α × β) → RBMap α β lt
| []          => mkRBMap _ _ _
| ⟨k,v⟩::xs   => (ofList xs).insert k v

def findCore : RBMap α β lt → α → Option (Sigma (fun (k : α) => β))
| ⟨t, _⟩, x => t.findCore lt x

def find : RBMap α β lt → α → Option β
| ⟨t, _⟩, x => t.find lt x

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
def lowerBound : RBMap α β lt → α → Option (Sigma (fun (k : α) => β))
| ⟨t, _⟩, x => t.lowerBound lt x none

@[inline] def contains (t : RBMap α β lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List (α × β)) (lt : α → α → Prop) [DecidableRel lt] : RBMap α β lt :=
l.foldl (fun r p => r.insert p.1 p.2) (mkRBMap α β lt)

@[inline] def all : RBMap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩, p => t.all p

@[inline] def any : RBMap α β lt → (α → β → Bool) → Bool
| ⟨t, _⟩, p => t.any p

end RBMap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β)) (lt : α → α → Prop) [DecidableRel lt] : RBMap α β lt :=
RBMap.fromList l lt

/- Test -/

@[reducible] def map : Type := RBMap Nat Bool Less.Less

def mkMapAux : Nat → map → map
| 0, m => m
| n+1,   m => mkMapAux n (m.insert n (n % 10 = 0))

def mkMap (n : Nat) :=
mkMapAux n (mkRBMap Nat Bool Less.Less)

def main (xs : List String) : IO UInt32 :=
let m := mkMap xs.head.toNat;
let v := RBMap.fold (fun (k : Nat) (v : Bool) (r : Nat) => if v then r + 1 else r) m 0;
IO.println (toString v) *>
pure 0
