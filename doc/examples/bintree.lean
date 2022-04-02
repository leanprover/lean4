/-|
==========================================
Binary Search Trees
==========================================

If the type of keys can be totally ordered -- that is, it supports a well-behaved `≤` comparison --
then maps can be implemented with binary search trees (BSTs). Insert and lookup operations on BSTs take time
proportional to the height of the tree. If the tree is balanced, the operations therefore take logarithmic time.

This example is based on a similar example found in the ["Sofware Foundations"](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)
book (volume 3).
-/

/-|
We use `Nat` as the key type in our implementation of BSTs,
since it has a convenient total order with lots of theorems and automation available.
We leave as an exercise to the reader the generalization to arbitrary types.
-/

inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
  deriving Repr

/-|
The function `contains` returns `true` iff the given gree contains the key `k`.
-/
def Tree.contains (t : Tree β) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node left key value right =>
    if k < key then
      left.contains k
    else if key < k then
      right.contains k
    else
      true

/-|
`t.find? k` returns `some v` if `v` is the value bound to key `k` in the tree `t`. It returns `none` otherwise.
-/
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

/-|
`t.insert k v` is the map containing all the bindings of `t` along with a binding of `k` to `v`.
-/
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
/-|
Let's add a new operation to our tree: converting it to an association list that contains the key--value bindings from the tree stored as pairs.
If that list is sorted by the keys, then any two trees that represent the same map would be converted to the same list.
Here's a function that does so with an in-order traversal of the tree.
-/
def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node left key value right => left.toList ++ [(key, value)] ++ right.toList

#eval Tree.leaf.insert 2 "two" |>.insert 3 "three" |>.insert 1 "one"
#eval Tree.leaf.insert 2 "two" |>.insert 3 "three" |>.insert 1 "one" |>.toList

/-|
The implemention of `Tree.toList` is inefficient because of how it uses the `++` operator.
On a balanced tree its running time is linearithmic, because it does a linear number of
concatentations at each level of the tree. On an unbalanced tree it's quadratic time.
Here's a tail-recursive implementation than runs in linear time, regardless of whether the tree is balanced:
-/
def Tree.toListTR (t : Tree β) : List (Nat × β) :=
  go t []
where
  go (t : Tree β) (acc : List (Nat × β)) : List (Nat × β) :=
    match t with
    | leaf => acc
    | node left key value right => left.go ((key, value) :: right.go acc)

/-|
We now prove that `t.toList` and `t.toListTR` return the same list.
The proof is on induction, and as we used the auxiliary function `go`
to define `Tree.toListTR`, we use an auxiliary theorem here too.
-/
theorem Tree.toList_eq_toListTR (t : Tree β) : t.toList = t.toListTR := by
  simp [toListTR, go t []]
where
  go (t : Tree β) (acc : List (Nat × β)) : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc <;> simp [toListTR.go, toList, *, List.append_assoc]

/-|
The `[csimp]` annotation instructs the Lean code generator to replace
any `Tree.toList` with `Tree.toListTR` when generating code.
-/
@[csimp] theorem Tree.toList_eq_toListTR_csimp : @Tree.toList = @Tree.toListTR := by
  funext β t
  apply toList_eq_toListTR

/-|
The implementations of `Tree.find?` and `Tree.insert` assume that values of type tree obey the BST invariant:
for any non-empty node with key `k`, all the values of the `left` subtree are less than `k` and all the values
of the right subtree are greater than `k`. But that invariant is not part of the definition of tree.

So, let's formalize the BST invariant. Here's one way to do so. First, we define a helper `ForallTree`
to express that idea that a predicate holds at every node of a tree:
-/
inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
  | leaf : ForallTree p .leaf
  | node : ForallTree p left → p key value → ForallTree p right → ForallTree p (.node left key value right)


/-|
Second, we define the BST invariant:
An empty tree is a BST.
A non-empty tree is a BST if all its left nodes have a lesser key, its right nodes have a greater key, and the left and right subtrees are themselves BSTs.
-/
inductive BST : Tree β → Prop
  | leaf : BST .leaf
  | node :
     {value : β} →
     ForallTree (fun k v => k < key) left →
     ForallTree (fun k v => key < k) right →
     BST left → BST right →
     BST (.node left key value right)

/-|
We now prove that `Tree.insert` preserves the BST invariant using induction and case analysis.
-/

theorem Tree.forall_insert_of_forall (h₁ : ForallTree p t) (h₂ : p key value) : ForallTree p (t.insert key value) := by
  induction h₁ with
  | leaf => exact .node .leaf h₂ .leaf
  | node hl hp hr ihl ihr =>
    rename Nat => k
    simp [insert]
    by_cases key < k <;> simp [*]
    · exact .node ihl hp hr
    · by_cases k < key <;> simp [*]
      · exact .node hl hp ihr
      · have heq : key = k := by simp_arith at *; apply Nat.le_antisymm <;> assumption -- TODO: improve with linarith
        subst key
        exact .node hl h₂ hr

theorem Tree.bst_insert_of_bst {t : Tree β} (h : BST t) (key : Nat) (value : β) : BST (t.insert key value) := by
  induction h with
  | leaf => exact .node .leaf .leaf .leaf .leaf
  | node h₁ h₂ b₁ b₂ ih₁ ih₂ =>
    rename Nat => k
    simp [insert]
    by_cases hlt : key < k <;> simp [*]
    · exact .node (forall_insert_of_forall h₁ hlt) h₂ ih₁ b₂
    · by_cases hgt : k < key <;> simp [*]
      · exact .node h₁ (forall_insert_of_forall h₂ hgt) b₁ ih₂
      · have heq : key = k := by simp_arith at *; apply Nat.le_antisymm <;> assumption -- TODO: improve with linarith
        subst key
        exact .node h₁ h₂ b₁ b₂

/-|
Now, we define the type `BinTree` using a `Subtype` that states that only trees satisfying the BST invariant are `BinTree`s.
-/
def BinTree (β : Type u) := { t : Tree β // BST t }

def BinTree.mk : BinTree β :=
  ⟨.leaf, .leaf⟩

def BinTree.contains (b : BinTree β) (k : Nat) : Bool :=
  b.val.contains k

def BinTree.find? (b : BinTree β) (k : Nat) : Option β :=
  b.val.find? k

def BinTree.insert (b : BinTree β) (k : Nat) (v : β) : BinTree β :=
  ⟨b.val.insert k v, b.val.bst_insert_of_bst b.property k v⟩

attribute [local simp] BinTree.mk BinTree.contains BinTree.find? BinTree.insert Tree.find? Tree.contains Tree.insert

/-|
Finally, we prove that `BinTree.find?` and `BinTree.insert` satisfy the map properties.
-/

theorem BinTree.find_mk {β : Type u} (k : Nat) : (@BinTree.mk β).find? k = none := by
  simp

theorem BinTree.find_insert (b : BinTree β) (k : Nat) (v : β) : (b.insert k v).find? k = some v := by
  let ⟨t, h⟩ := b; simp
  induction t with simp
  | node left key value right ihl ihr =>
    by_cases k < key <;> simp [*]
    · cases h; apply ihl; assumption
    · by_cases key < k <;> simp [*]
      cases h; apply ihr; assumption

theorem BinTree.find_insert_of_ne (b : BinTree β) (h : k ≠ k') (v : β) : (b.insert k v).find? k' = b.find? k' := by
  let ⟨t, h⟩ := b; simp
  induction t with simp
  | leaf =>
    split <;> simp <;> split <;> simp
    have heq : k = k' := by simp_arith at *; apply Nat.le_antisymm <;> assumption -- TODO: improve with linarith
    contradiction
  | node left key value right ihl ihr =>
    let .node hl hr bl br := h
    have ihl := ihl bl
    have ihr := ihr br
    by_cases k < key <;> simp [*]
    by_cases key < k <;> simp [*]
    have heq : key = k := by simp_arith at *; apply Nat.le_antisymm <;> assumption -- TODO: improve with linarith
    subst key
    by_cases k' < k <;> simp [*]
    by_cases k  < k' <;> simp [*]
    have heq : k = k' := by simp_arith at *; apply Nat.le_antisymm <;> assumption -- TODO: improve with linarith
    contradiction
