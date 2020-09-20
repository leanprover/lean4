new_frontend

def M := StateM Nat

def f1 : M Nat :=
pure 0 -- failed to synthesize `HasPure M`

attribute [reducible] M

def f2 : M Nat :=
pure 0
