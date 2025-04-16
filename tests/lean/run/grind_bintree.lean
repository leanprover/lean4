set_option grind.warning false
reset_grind_attrs%

attribute [grind] List.append_assoc List.cons_append List.nil_append

inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
  deriving Repr

def Tree.contains (t : Tree β) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node left key _ right =>
    if k < key then
      left.contains k
    else if key < k then
      right.contains k
    else
      true

def Tree.find? (t : Tree β) (k : Nat) : Option β :=
  match t with
  | leaf => none
  | node left key value right =>
    if k < key then
      left.find? k
    else if key < k then
      right.find? k
    else
      some value

def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node leaf k v leaf
  | node left key value right =>
    if k < key then
      node (left.insert k v) key value right
    else if key < k then
      node left key value (right.insert k v)
    else
      node left k v right

def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node l k v r => l.toList ++ [(k, v)] ++ r.toList

def Tree.toListTR (t : Tree β) : List (Nat × β) :=
  go t []
where
  go (t : Tree β) (acc : List (Nat × β)) : List (Nat × β) :=
    match t with
    | leaf => acc
    | node l k v r => go l ((k, v) :: go r acc)

theorem Tree.toList_eq_toListTR (t : Tree β)
        : t.toList = t.toListTR := by
  simp [toListTR, go t []]
where
  go (t : Tree β) (acc : List (Nat × β))
     : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc <;> grind [toListTR.go, toList]

@[csimp] theorem Tree.toList_eq_toListTR_csimp
                 : @Tree.toList = @Tree.toListTR := by
  grind [toList_eq_toListTR]

inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
  | leaf : ForallTree p .leaf
  | node :
     ForallTree p left →
     p key value →
     ForallTree p right →
     ForallTree p (.node left key value right)

inductive BST : Tree β → Prop
  | leaf : BST .leaf
  | node :
     ForallTree (fun k _ => k < key) left →
     ForallTree (fun k _ => key < k) right →
     BST left → BST right →
     BST (.node left key value right)

attribute [local simp, grind] Tree.insert

theorem Tree.forall_insert_of_forall
        (h₁ : ForallTree p t) (h₂ : p key value)
        : ForallTree p (t.insert key value) := by
  induction h₁ <;> grind [ForallTree.node, ForallTree.leaf]

theorem Tree.bst_insert_of_bst
        {t : Tree β} (h : BST t) (key : Nat) (value : β)
        : BST (t.insert key value) := by
  induction h <;> grind [BST.node, BST.leaf, ForallTree.leaf, forall_insert_of_forall]

def BinTree (β : Type u) := { t : Tree β // BST t }

def BinTree.mk : BinTree β :=
  ⟨.leaf, .leaf⟩

def BinTree.contains (b : BinTree β) (k : Nat) : Bool :=
  b.val.contains k

def BinTree.find? (b : BinTree β) (k : Nat) : Option β :=
  b.val.find? k

def BinTree.insert (b : BinTree β) (k : Nat) (v : β) : BinTree β :=
  ⟨b.val.insert k v, b.val.bst_insert_of_bst b.property k v⟩

attribute [local simp, local grind]
  BinTree.mk BinTree.contains BinTree.find?
  BinTree.insert Tree.find? Tree.contains Tree.insert

theorem BinTree.find_mk (k : Nat)
        : BinTree.mk.find? k = (none : Option β) := by
  grind [Tree.find?]

theorem BinTree.find_insert (b : BinTree β) (k : Nat) (v : β)
        : (b.insert k v).find? k = some v := by
  let ⟨t, h⟩ := b; simp
  induction t <;> simp <;> grind [BST]

theorem BinTree.find_insert_of_ne (b : BinTree β) (ne : k ≠ k') (v : β)
        : (b.insert k v).find? k' = b.find? k' := by
  let ⟨t, h⟩ := b; simp
  induction t <;> simp <;> grind [BST]
