#eval show Option String from do
  s!"{← some 1}"

def f1 : Option Nat := do
  return (← some 1)

def f2 : Option Nat := do
  let x ← some 1
  return none

def f3 : Option String := do
  if let some x ← some 1 then
    none
  else
    none

def f4 : Option String := do
  let mut x := none
  x ← some 1
  return x

def f5 : Option String := do
  let (x, y) ← some (1, 5)
  return x
