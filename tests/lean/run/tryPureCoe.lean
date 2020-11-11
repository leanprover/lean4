def m1 : IO Bool :=
pure true

def p (x : Nat) : Bool :=
x > 0

def tst1 : IO Bool :=
true <&&> m1

def tst2 (x : Nat) : IO Bool :=
x = 0 <&&> m1

def tst3 (x : Nat) : IO Unit := do
if ← (m1 <&&> x > 0) then
  throw $ IO.userError "test"

def tst4 (x : Nat) : IO Unit := do
if x > 0 && (← m1) then
  throw $ IO.userError "test"

def tst5 (x : Nat) : IO Unit := do
if ← (p x <&&> m1) then
  throw $ IO.userError "test"

def tst6 (x : Nat) : IO Unit := do
if ← (p x <&&> id m1) then
  throw $ IO.userError "test"

def tst7 (x : Nat) : IO Unit := do
if (← m1) && x > 0 then
  throw $ IO.userError "test"

def tst8 (x : Nat) : IO Unit := do
if x > 0 && (← m1) then
  throw $ IO.userError "test"

def tst9 (x : Nat) : IO Unit := do
if p x && (← m1) then
  throw $ IO.userError "test"

def tst10 (x : Nat) : IO Unit := do
if p x && (← id m1) then
  throw $ IO.userError "test"

def tst11 (x : Nat) : IO Unit := do
if p x && id (← m1) then
  throw $ IO.userError "test"
