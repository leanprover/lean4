inductive Tree (α : Type u) : Type u where
  | node : α → (Bool → List (Tree α)) → Tree α

mutual
def Tree.size : Tree α → Nat
  | .node _ tsf => 1 + size_aux (tsf true) + size_aux (tsf false)
termination_by structural t => t
def Tree.size_aux : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size t + size_aux ts
end

/--
info: theorem Tree.size.eq_def.{u_1} : ∀ {α : Type u_1} (x : Tree α),
  x.size =
    match x with
    | Tree.node a tsf => 1 + Tree.size_aux (tsf true) + Tree.size_aux (tsf false)
-/
#guard_msgs in
#print sig Tree.size.eq_def

/--
info: theorem Tree.size_aux.eq_def.{u_1} : ∀ {α : Type u_1} (x : List (Tree α)),
  Tree.size_aux x =
    match x with
    | [] => 0
    | t :: ts => t.size + Tree.size_aux ts
-/
#guard_msgs in
#print sig Tree.size_aux.eq_def

mutual
def Tree.size1 : Tree α → Nat
  | .node _ tsf => 1 + size_aux2 (tsf true) + size_aux2 (tsf false)
termination_by structural t => t
def Tree.size2 : Tree α → Nat
  | .node _ tsf => 1 + size_aux1 (tsf true) + size_aux1 (tsf false)
termination_by structural t => t
def Tree.size_aux1 : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size2 t + size_aux2 ts
def Tree.size_aux2 : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size1 t + size_aux1 ts
end

/--
info: theorem Tree.size1.eq_def.{u_1} : ∀ {α : Type u_1} (x : Tree α),
  x.size1 =
    match x with
    | Tree.node a tsf => 1 + Tree.size_aux2 (tsf true) + Tree.size_aux2 (tsf false)
-/
#guard_msgs in #print sig Tree.size1.eq_def
/--
info: theorem Tree.size2.eq_def.{u_1} : ∀ {α : Type u_1} (x : Tree α),
  x.size2 =
    match x with
    | Tree.node a tsf => 1 + Tree.size_aux1 (tsf true) + Tree.size_aux1 (tsf false)
-/
#guard_msgs in #print sig Tree.size2.eq_def
/--
info: theorem Tree.size_aux1.eq_def.{u_1} : ∀ {α : Type u_1} (x : List (Tree α)),
  Tree.size_aux1 x =
    match x with
    | [] => 0
    | t :: ts => t.size2 + Tree.size_aux2 ts
-/
#guard_msgs in #print sig Tree.size_aux1.eq_def
/--
info: theorem Tree.size_aux2.eq_def.{u_1} : ∀ {α : Type u_1} (x : List (Tree α)),
  Tree.size_aux2 x =
    match x with
    | [] => 0
    | t :: ts => t.size1 + Tree.size_aux1 ts
-/
#guard_msgs in #print sig Tree.size_aux2.eq_def
