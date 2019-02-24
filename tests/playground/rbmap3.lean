prelude
import init.core init.io init.data.ordering

universes u v w

inductive rbcolor
| red | black

inductive rbnode (α : Type u) (β : α → Type v)
| leaf  {}                                                                        : rbnode
| node  (c : rbcolor) (lchild : rbnode) (key : α) (val : β key) (rchild : rbnode) : rbnode

instance rbcolor.decidable_eq : decidable_eq rbcolor :=
{dec_eq := λ a b, rbcolor.cases_on a
  (rbcolor.cases_on b (is_true rfl) (is_false (λ h, rbcolor.no_confusion h)))
  (rbcolor.cases_on b (is_false (λ h, rbcolor.no_confusion h)) (is_true rfl))}

namespace rbnode
variables {α : Type u} {β : α → Type v} {σ : Type w}

open rbcolor

def depth (f : nat → nat → nat) : rbnode α β → nat
| leaf               := 0
| (node _ l _ _ r)   := (f (depth l) (depth r)) + 1

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

@[specialize] def rev_fold (f : Π (k : α), β k → σ → σ) : rbnode α β → σ → σ
| leaf b               := b
| (node _ l k v r)   b := rev_fold l (f k v (rev_fold r b))

@[specialize] def all (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf                 := tt
| (node _ l k v r)     := p k v && all l && all r

@[specialize] def any (p : Π k : α, β k → bool) : rbnode α β → bool
| leaf               := ff
| (node _ l k v r)   := p k v || any l || any r

def is_red : rbnode α β → bool
| (node red _ _ _ _) := tt
| _                  := ff

def rotate_left : Π (n : rbnode α β), n ≠ leaf → rbnode α β
| n@(node hc hl hk hv (node red xl xk xv xr)) _ :=
  if not (is_red hl)
  then (node hc (node red hl hk hv xl) xk xv xr)
  else n
| leaf h := absurd rfl h
| e _    := e

theorem if_node_node_ne_leaf {c : Prop} [decidable c] {l1 l2 : rbnode α β} {c1 k1 v1 r1 c2 k2 v2 r2} : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) ≠ leaf :=
λ h, if hc : c
then have h1 : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) = node c1 l1 k1 v1 r1, from if_pos hc,
     rbnode.no_confusion (eq.trans h1.symm h)
else have h1 : (if c then node c1 l1 k1 v1 r1 else node c2 l2 k2 v2 r2) = node c2 l2 k2 v2 r2, from if_neg hc,
     rbnode.no_confusion (eq.trans h1.symm h)

theorem rotate_left_ne_leaf : ∀ (n : rbnode α β) (h : n ≠ leaf), rotate_left n h ≠ leaf
| (node _ hl _ _ (node red _ _ _ _)) _ h  := if_node_node_ne_leaf h
| leaf h _                                := absurd rfl h
| (node _ _ _ _ (node black _ _ _ _)) _ h := rbnode.no_confusion h

def rotate_right : Π (n : rbnode α β), n ≠ leaf → rbnode α β
| n@(node hc (node red xl xk xv xr) hk hv hr) _ :=
  if is_red xl
  then (node hc xl xk xv (node red xr hk hv hr))
  else n
| leaf h := absurd rfl h
| e _    := e

theorem rotate_right_ne_leaf : ∀ (n : rbnode α β) (h : n ≠ leaf), rotate_right n h ≠ leaf
| (node _ (node red _ _ _ _) _ _ _) _ h   := if_node_node_ne_leaf h
| leaf h _                                := absurd rfl h
| (node _ (node black _ _ _ _) _ _ _) _ h := rbnode.no_confusion h

def flip : rbcolor → rbcolor
| red   := black
| black := red

def flip_color : rbnode α β → rbnode α β
| (node c l k v r) := node (flip c) l k v r
| leaf             := leaf

def flip_colors : Π (n : rbnode α β), n ≠ leaf → rbnode α β
| n@(node c l k v r) _ :=
  if is_red l ∧ is_red r
  then node (flip c) (flip_color l) k v (flip_color r)
  else n
| leaf h := absurd rfl h

def fixup (n : rbnode α β) (h : n ≠ leaf) : rbnode α β :=
let n₁ := rotate_left n h in
let h₁ := (rotate_left_ne_leaf n h) in
let n₂ := rotate_right n₁ h₁ in
let h₂ := (rotate_right_ne_leaf n₁ h₁) in
flip_colors n₂ h₂

def set_black : rbnode α β → rbnode α β
| (node red l k v r) := node black l k v r
| n                  := n

section insert
variables (lt : α → α → Prop) [decidable_rel lt]

def ins (x : α) (vx : β x) : rbnode α β → rbnode α β
| leaf             := node red leaf x vx leaf
| (node c l k v r) :=
  if lt x k then fixup (node c (ins l) k v r) (λ h, rbnode.no_confusion h)
  else if lt k x then fixup (node c l k v (ins r)) (λ h, rbnode.no_confusion h)
  else node c l x vx r

def insert (t : rbnode α β) (k : α) (v : β k) : rbnode α β :=
set_black (ins lt k v t)

end insert

section membership
variable (lt : α → α → Prop)

variable [decidable_rel lt]

def find_core : rbnode α β → Π k : α, option (Σ k : α, β k)
| leaf                 x := none
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
| leaf                 x lb := lb
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

/- Test -/

@[reducible] def map : Type := rbmap nat bool (<)

def mk_map_aux : nat → map → map
| 0 m := m
| (n+1) m := mk_map_aux n (m.insert n (n % 10 = 0))

def mk_map (n : nat) :=
mk_map_aux n (mk_rbmap nat bool (<))

def main (xs : list string) : io uint32 :=
let m := mk_map xs.head.to_nat in
let v := rbmap.fold (λ (k : nat) (v : bool) (r : nat), if v then r + 1 else r) m 0 in
io.println' (to_string v) *>
pure 0
