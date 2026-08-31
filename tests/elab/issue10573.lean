
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Array (Tree α) → Tree α

def Tree.map {α β} (f : α → β) : Tree α → Tree β
  | .leaf x => .leaf (f x)
  | .node ts => .node (ts.map (Tree.map f))

def Tree.map' {α β} [SizeOf α]: (t : Tree α) → (f : (x : α) → sizeOf x < sizeOf t → β) → Tree β
  | .leaf x, f => .leaf (f x (by simp))
  | .node ts, f => .node (ts.attach.map (fun ⟨t, ht⟩ =>
    Tree.map' t (fun x hx => f x (by have := Array.sizeOf_lt_of_mem ht; grind [node.sizeOf_spec]))))

/--
error: Tactic `try?` failed: consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`

α β : Type
inst✝ : SizeOf α
f : α → β
t : Tree α
⊢ map f t = t.map' fun x x_1 => f x
-/
#guard_msgs in
theorem Tree.map_eq_map' {α β} [SizeOf α] (f : α → β) (t : Tree α) :
    Tree.map f t = Tree.map' t (fun x _ => f x) := by try?


inductive Tree' where | nil

#guard_msgs in
example : 0 <= (Tree'.nil : Tree')._sizeOf_1 := by simp [Tree'._sizeOf_1]
