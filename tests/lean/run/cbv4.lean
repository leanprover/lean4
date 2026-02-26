/- Minimized example extracted from verifying the Collatz conjecture for small numbers.
   Suggested by Bhavik Mehta (@b-mehta). -/
set_option cbv.warning false
def collatzStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def manyStep (n m : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => m < n ∨ manyStep n (collatzStep m) k

def checkAll (gas : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => bif manyStep (n + 2) (n + 2) gas then checkAll gas n else false

set_option maxRecDepth 5000
set_option trace.Meta.Tactic true
example : checkAll 70 100 = true := by cbv
