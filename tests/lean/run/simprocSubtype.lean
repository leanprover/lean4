inductive Tree where | node : List Tree → Tree

def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.reverse.map (fun ⟨t, _⟩ => t.rev))

@[simp] theorem Tree.rev_def (ts : List Tree) :
    Tree.rev (.node ts) = .node (ts.reverse.map rev) := by
  simp [Tree.rev]
