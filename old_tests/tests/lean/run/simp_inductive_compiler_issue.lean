structure box (α : Type) :=
(val : α)

def f1 (g h : ℕ → ℕ) (b : bool) : ℕ → ℕ :=
box.val (bool.cases_on b (box.mk g) (box.mk h))

def f2 (g h : box (ℕ → ℕ)) (b : bool) : ℕ → ℕ :=
box.val (bool.cases_on b g h)
