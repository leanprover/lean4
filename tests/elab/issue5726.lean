inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n + 1)

inductive Tree : Type where
  | branch : ∀ {n}, Vec (Option Tree) n → Tree

theorem die : Tree → True
  | .branch v =>
    let rec loop {n} : Vec (Option Tree) n → True
    | .nil => ⟨⟩
    | .cons none _ => ⟨⟩
    | .cons (some t) _ => die t
    loop v
