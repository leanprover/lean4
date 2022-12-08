inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)

def test [Monad m] (xs : Vector α a) : m Unit :=
  match xs with
  | Vector.nil => return ()
  | Vector.cons x xs => test xs
termination_by test xs => sizeOf xs
