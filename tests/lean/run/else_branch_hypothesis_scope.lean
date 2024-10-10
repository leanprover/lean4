/-!
# Demonstrates that the hypothesis created in the `else` branch of a `if` statement
will be available after a control flow statement (i.e. return, break and continue)
-/

def safeDiv (a b : Nat) (_ : b ≠ 0): Nat := a / b

/--
Demonstrates that early `return` is recognized
-/
def earlyReturn (a b : Nat) : Option Nat := Id.run do
  if zh : b = 0 then
    return none

  return safeDiv a b zh
  -- return safeDiv a b nz

/-- info: none -/
#guard_msgs in
#eval earlyReturn 10 0

/-- info: some 5 -/
#guard_msgs in
#eval earlyReturn 10 2

/--
Demonstrates that `break` is recognized
-/
def earlyBreak : Nat := Id.run do
  let mut sum := 0
  for val in [2, 0, 1] do
    if zh : val = 0 then
      let _ := 3 -- test we always look at the last expression in the block
      break

    sum := sum + safeDiv 10 val zh

  return sum

/-- info: 5 -/
#guard_msgs in
#eval earlyBreak

/--
Demonstrates that `continue` is recognized
-/
def earlyContinue : Nat := Id.run do
  let mut sum := 0
  for val in [1, 0, 2] do
    if zh : val = 0 then
      continue

    sum := sum + safeDiv 10 val zh

  return sum

/-- info: 15 -/
#guard_msgs in
#eval earlyContinue
