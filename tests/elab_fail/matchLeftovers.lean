def f : Nat × Nat → Nat
  | (a, b) => a + b

def f' : Nat × Nat → Nat
  | (a, b) => by done

example (x : Nat × Nat) (h : x.1 > 0) : f x > 0 := by
  match x with
  | (a, b) => done

def g (x : Nat) : Nat × Nat :=
  (x, x+1)

example (x : Nat) : Nat :=
  match g x with
  | (a, b) => by done

inductive Vector' (α : Type u) : Nat → Type u where
  | nil  : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)

namespace Vector'
  def insert (a: α): Fin (n+1) → Vector' α n → Vector' α (n+1)
    | ⟨0  , _⟩,        xs => cons a xs
    | ⟨i+1, h⟩, cons x xs => by done

end Vector'
