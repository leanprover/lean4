/-!
A few tests for functional induction theorems generated from mutual recursive inductives.

Some more tests are in `structuralMutual.lean` and `funind_structural`.
-/


inductive Tree (α : Type u) : Type u where
  | node : α → (Bool → List (Tree α)) → Tree α

-- Recursion over nested inductive

mutual
def Tree.size : Tree α → Nat
  | .node _ tsf => 1 + size_aux (tsf true) + size_aux (tsf false)
termination_by structural t => t
def Tree.size_aux : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size t + size_aux ts
end

/--
info: Tree.size.induct.{u_1} {α : Type u_1} (motive_1 : Tree α → Prop) (motive_2 : List (Tree α) → Prop)
  (case1 :
    ∀ (a : α) (tsf : Bool → List (Tree α)), motive_2 (tsf true) → motive_2 (tsf false) → motive_1 (Tree.node a tsf))
  (case2 : motive_2 []) (case3 : ∀ (t : Tree α) (ts : List (Tree α)), motive_1 t → motive_2 ts → motive_2 (t :: ts)) :
  ∀ (a : Tree α), motive_1 a
-/
#guard_msgs in
#check Tree.size.induct


-- Recursion over nested inductive, functions in the “wrong” order (auxillary first)

mutual
def Tree.size_aux' : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size' t + size_aux' ts
def Tree.size' : Tree α → Nat
  | .node _ tsf => 1 + size_aux' (tsf true) + size_aux' (tsf false)
termination_by structural t => t
end

/--
info: Tree.size_aux'.mutual_induct.{u_1} {α : Type u_1} (motive_1 : List (Tree α) → Prop) (motive_2 : Tree α → Prop)
  (case1 :
    ∀ (a : α) (tsf : Bool → List (Tree α)), motive_1 (tsf true) → motive_1 (tsf false) → motive_2 (Tree.node a tsf))
  (case2 : motive_1 []) (case3 : ∀ (t : Tree α) (ts : List (Tree α)), motive_2 t → motive_1 ts → motive_1 (t :: ts)) :
  (∀ (a : List (Tree α)), motive_1 a) ∧ ∀ (a : Tree α), motive_2 a
-/
#guard_msgs in
#check Tree.size_aux'.mutual_induct

-- Similar, but with many packed functions
mutual
def Tree.size_aux1 : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size2 t + size_aux2 ts
def Tree.size1 : Tree α → Nat
  | .node _ tsf => 1 + size_aux2 (tsf true) + size_aux3 (tsf false)
termination_by structural t => t
def Tree.size_aux2 : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size3 t + size_aux3 ts
def Tree.size2 : Tree α → Nat
  | .node _ tsf => 1 + size_aux3 (tsf true) + size_aux1 (tsf false)
def Tree.size_aux3 : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size1 t + size_aux1 ts
def Tree.size3 : Tree α → Nat
  | .node _ tsf => 1 + size_aux1 (tsf true) + size_aux2 (tsf false)
end

#check Tree.size_aux1.mutual_induct
