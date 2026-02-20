inductive Tree (α : Type) : Type where
| leaf : Tree α
| node (t : Tree α) (f : Tree α) : Tree α

inductive Subtree : Tree α → Tree α → Prop where
| left_head  (t f : Tree α) : Subtree t (Tree.node t f)
| right_head (t f : Tree α) : Subtree f (Tree.node t f)

def dec_subtree (n m : Tree α) : Decidable (Subtree n m) :=
  match n, m with
  | .leaf, .node t f =>
    let ht := dec_subtree .leaf t
    let hf := dec_subtree .leaf f
    match ht, hf with
    | .isFalse ht, .isFalse hf => .isFalse (fun h =>
      match h with
      | .left_head _ _ => sorry
      | _ => sorry
    )
    | _, _ => sorry
  | _, _ => sorry
