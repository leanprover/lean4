def f := 42
def f' := Lean.reduceNat f

#print axioms f'

def g := false
def g' := Lean.reduceBool g

#print axioms g'
