new_frontend
def m1 : IO Bool :=
pure true

def p (x : Nat) : Bool :=
x > 0

def tst1 : IO Bool :=
true <&&> m1

def tst2 (x : Nat) : IO Bool :=
x = 0 <&&> m1

def tst3 (x : Nat) : IO Unit :=
whenM (m1 <&&> x > 0) $
  throw $ IO.userError "test"

def tst4 (x : Nat) : IO Unit :=
whenM (x > 0 <&&> m1) $
  throw $ IO.userError "test"

def tst5 (x : Nat) : IO Unit :=
whenM (p x <&&> m1) $
  throw $ IO.userError "test"

def tst6 (x : Nat) : IO Unit :=
whenM (p x <&&> id m1) $
  throw $ IO.userError "test"
