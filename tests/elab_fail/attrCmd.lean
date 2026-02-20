

def M := StateM Nat

def f1 : M Nat :=
pure 0 -- failed to synthesize `Pure M`

attribute [reducible] M

def f2 : M Nat :=
pure 0
