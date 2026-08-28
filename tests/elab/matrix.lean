
/- Simple Matrix -/

def Matrix (m n : Nat) (α : Type u) : Type u :=
  Fin m → Fin n → α

namespace Matrix

/- Scoped notation for accessing values stored in matrices. -/
scoped syntax:max (name := matrixAccess) (priority := high) term noWs "[" term ", " term "]" : term

macro_rules (kind := matrixAccess)
  | `($x[$i, $j]) => `($x $i $j)

def dotProduct [Mul α] [Add α] [Zero α] (u v : Fin m → α) : α :=
  loop m (Nat.le_refl ..) Zero.zero
where
  loop (i : Nat) (h : i ≤ m) (acc : α) : α :=
    match i, h with
    | 0, _   => acc
    | i+1, h =>
      have : i < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      loop i (Nat.le_of_lt this) (acc + u ⟨i, this⟩ * v ⟨i, this⟩)

instance [Zero α] : Zero (Matrix m n α) where
  zero _ _ := 0

instance [Add α] : Add (Matrix m n α) where
  add x y i j := x[i, j] + y[i, j]

instance [Mul α] [Add α] [Zero α] : HMul (Matrix m n α) (Matrix n p α) (Matrix m p α) where
  hMul x y i j := dotProduct (x[i, ·]) (y[·, j])

instance [Mul α] : HMul α (Matrix m n α) (Matrix m n α) where
  hMul c x i j := c * x[i, j]

end Matrix

def m1 : Matrix 2 2 Int :=
  fun i j => #[#[1, 2], #[3, 4]][i]![j]!

def m2 : Matrix 2 2 Int :=
  fun i j => #[#[5, 6], #[7, 8]][i]![j]!

open Matrix -- activate .[.,.] notation

#guard (m1*m2)[0, 0] == 19
#guard (m1*m2)[0, 1] == 22
#guard (m1*m2)[1, 0] == 43
#guard (m1*m2)[1, 1] == 50

def v := -2

#guard (v*m1*m2)[0, 0] == -38

def ex1 (a b : Nat) (x : Matrix 10 20 Nat) (y : Matrix 20 10 Nat) (z : Matrix 10 10 Nat) : Matrix 10 10 Nat :=
  a * x * y + b * z

def ex2 (a b : Nat) (x : Matrix m n Nat) (y : Matrix n m Nat) (z : Matrix m m Nat) : Matrix m m Nat :=
  a * x * y + b * z
