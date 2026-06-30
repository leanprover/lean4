inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

theorem ex1 {a b c d x : Nat} (h : Vec.cons a (Vec.cons b Vec.nil) = Vec.cons x (Vec.cons 0 Vec.nil)) : a = x + b := by
  simp_all

theorem ex2 {a b c d x : Nat} (h : [a, b] = [x, 0]) : a = x + b := by
  simp_all

theorem ex3 {a b c d x : Nat} (h : Array.mk [a, b] = Array.mk [x, 0]) : a = x + b := by
  simp_all

theorem ex4 {a b c d x : Nat} (h : (Array.mk [a, b], c)  = (Array.mk [x, 0], d)) : a + c = x + b + d := by
  simp_all
