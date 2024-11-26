inductive Vector' (α : Type u) : Nat → Type u
  | nil : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)
  deriving Repr

infix:67 " :: " => Vector'.cons

def tabulate (f : Fin n → α) : Vector' α n :=
  match n with
  | 0   => Vector'.nil
  | n+1 => f 0 :: tabulate (f ∘ Fin.succ)

#eval tabulate fun i : Fin 5 => i
