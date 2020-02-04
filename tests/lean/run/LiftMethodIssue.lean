new_frontend

def tst : IO (Option Nat) := do
x? : Option Nat ← pure none;
pure x?

def tst2 (x : Nat) : IO (Option Nat) := do
x? : Option Nat ← pure x;
if x?.isNone then pure (x+1) else pure x?
