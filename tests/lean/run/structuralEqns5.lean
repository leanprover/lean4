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
error: Failed to realize constant Tree.size_aux.eq_def:
  failed to generate equational theorem for `Tree.size_aux`
    goal not headed by `.brecOn`
    α : Type u_1
    x✝ : List (Tree α)
    ⊢ (Tree.brecOn_1 x✝
          (fun x f =>
            (match (motive := (x : Tree α) → x.below → Nat) x with
              | Tree.node a tsf => fun x => 1 + (x true).1 + (x false).1)
              f)
          fun x f =>
          (match (motive := (x : List (Tree α)) → Tree.below_1 x → Nat) x with
            | [] => fun x => 0
            | t :: ts => fun x => x.1.1 + x.2.1)
            f) =
        match x✝ with
        | [] => 0
        | t :: ts => t.size + Tree.size_aux ts
---
error: Unknown constant `Tree.size_aux.eq_def`
-/
#guard_msgs in
#print sig Tree.size_aux.eq_def
