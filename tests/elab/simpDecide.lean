example : 0 < 4 := by decide

example : 0 < 4 := by
  fail_if_success { simp only }
  simp (config := { decide := true }) only

def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib (n+1) + fib n

theorem fib_two : fib 2 = 1 := rfl

example : 1 = fib (1 + 1) := by
  fail_if_success { simp only [fib_two] }
  simp (config := { decide := true }) only [fib_two]

example : 1 = fib (1 + 1) := by simp only [fib_two, (by decide : 1 + 1 = 2)]
