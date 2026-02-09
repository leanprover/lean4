theorem ex1 (x : Nat) : 0 + x = x := by
  cases x with
  | zero   => skip -- Error: unsolved goals
  | succ y => skip -- Error: unsolved goals

theorem ex2 (x : Nat) : 0 + x = x := by
  induction x with
  | zero      => skip -- Error: unsolved goals
  | succ y ih => skip -- Error: unsolved goals

theorem ex3 (x : Nat) : 0 + x = x := by
  cases x with
  | zero   => rfl
  | succ y => skip -- Error: unsolved goals

theorem ex4 (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih => skip -- Error: unsolved goals
  | base x y h₁   => skip -- Error: unsolved goals

theorem ex5 (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  cases x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih => skip -- Error: unsolved goals
  | base x y h₁   => skip -- Error: unsolved goals
