set_option linter.unusedVariables false

/-! A variety of matches that failed at some point during the development of the sparse match features. -/


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

-- This only works if we do not use the sparse cases on when there are no alternatives left
def List.nth : (as : List α) → (i : Fin as.length) → α
  | a::as, ⟨0, _⟩   => a
  | a::as, ⟨i+1, h⟩ => nth as ⟨i, Nat.lt_of_succ_lt_succ h⟩


-- So does this, taken from the standard library
example : (a b : Int) → (h : a * b = 0) → a = 0 ∨ b = 0
  | .ofNat 0, _, _ => by simp
  | _, .ofNat 0, _ => by simp
  | .ofNat (a+1), .negSucc b, h => by cases h

-- When we use the sparse cases more aggressively, we had to write it like this
example : (a b : Int) → (h : a * b = 0) → a = 0 ∨ b = 0
  | .ofNat 0, _, _ => by simp
  | _, .ofNat 0, _ => by simp
  | .ofNat (a+1), .negSucc b, h => by cases h
  | .negSucc _, .negSucc _, h => by cases h
