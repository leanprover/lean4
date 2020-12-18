inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving DecidableEq

inductive Test (α : Type)
  | mk₀
  | mk₁ : (n : Nat) → (α × α) → List α → Vec α n → Test α
  | mk₂ : Test α → α → Test α
  deriving DecidableEq

def t1 [DecidableEq α] : DecidableEq (Vec α n) :=
  inferInstance

def t2 [DecidableEq α] : DecidableEq (Test α) :=
  inferInstance
