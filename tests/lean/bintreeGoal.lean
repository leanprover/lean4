inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
  deriving Repr

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
     {value : β} →
     ForallTree (fun k v => k < key) left →
     ForallTree (fun k v => key < k) right →
     BST left → BST right →
     BST (.node left key value right)

def BinTree (β : Type u) := { t : Tree β // BST t }

def BinTree.mk : BinTree β :=
  ⟨.leaf, .leaf⟩

def BinTree.find? (b : BinTree β) (k : Nat) : Option β :=
  b.val.find? k

def BinTree.insert (b : BinTree β) (k : Nat) (v : β) : BinTree β :=
  ⟨b.val.insert k v, sorry⟩

attribute [local simp]
  BinTree.mk BinTree.find?
  BinTree.insert Tree.find? Tree.insert

theorem BinTree.find_insert (b : BinTree β) (k : Nat) (v : β)
        : (b.insert k v).find? k = some v := by
  let ⟨t, h⟩ := b; simp
  induction t with simp
  | node left key value right ihl ihr =>
    by_cases k < key <;> simp [*]
    . cases h; apply ihl; done
    . sorry
