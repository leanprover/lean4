

def half : Nat → Nat
| 0     => 0
| 1     => 0
| (x+2) => half x + 1

theorem half0 : half 0 = 0 :=
rfl

theorem half1 : half 1 = 0 :=
rfl

theorem half_succ_succ (a : Nat) : half (a + 2) = half a + 1 :=
rfl

example : half 5 = 2 :=
rfl

example : half 8 = 4 :=
rfl
