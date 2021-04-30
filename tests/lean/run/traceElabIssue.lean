set_option trace.Elab true
inductive Vec (α : Type u) : Nat → Type u
| nil      : Vec α Nat.zero
| cons {n : Nat} : (head : α) → (tail : Vec α n) → Vec α (Nat.succ n)
