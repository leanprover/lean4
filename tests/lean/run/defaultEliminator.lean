@[eliminator] protected def Nat.recDiag {motive : Nat → Nat → Sort u}
    (zero_zero : motive 0 0)
    (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
    (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
    (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1))
    (x y : Nat) :  motive x y :=
  let rec go : (x y : Nat) → motive x y
    | 0,     0 => zero_zero
    | x+1, 0   => succ_zero x (go x 0)
    | 0,   y+1 => zero_succ y (go 0 y)
    | x+1, y+1 => succ_succ x y (go x y)
  go x y
termination_by go x y => (x, y)

def f (x y : Nat) :=
  match x, y with
  | 0,   0   => 1
  | x+1, 0   => f x 0
  | 0,   y+1 => f 0 y
  | x+1, y+1 => f x y
termination_by f x y => (x, y)

example (x y : Nat) : f x y > 0 := by
  induction x, y with
  | zero_zero => decide
  | succ_zero x ih => simp [f, ih]
  | zero_succ y ih => simp [f, ih]
  | succ_succ x y ih => simp [f, ih]

example (x y : Nat) : f x y > 0 := by
  induction x, y <;> simp (config := { decide := true }) [f, *]
