def small (ps : Array (Nat × Nat)) : Array (Nat × Nat) :=
  (ps.filter fun (p : Prod _ _) =>
    match p with
    | (x, y) => x == 0)
  ++
  ps

#eval small #[(1, 2), (0, 3), (2, 4)]

variable {α β : Type} [Inhabited α] [Inhabited β]

def P (xys : Array (α × β)) (f : α → β) : Prop := True

example (xys : Array (α × β))
        (pred? : α → Bool)
        (H : Subtype $ P (xys.filter fun (x, _) => pred? x))
        : Unit := ()
