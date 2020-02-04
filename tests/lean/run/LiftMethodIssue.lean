new_frontend

def tst : IO (Option Nat) := do
x? : Option Nat ← pure none;
pure x?
