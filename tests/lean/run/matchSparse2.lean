set_option linter.unusedVariables false


inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)

def Finn.min (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Unit
  | fzero, _ => ()
  | _, fzero => ()
  | fsucc i, fsucc j => ()

def boo (x : Fin 3) : Nat :=
  match x with
  | 0 => 1
  | 1 => 2
  | 2 => 4
