axiom F : Type
axiom foo : F
def foo' : F := foo

axiom bla : Nat

noncomputable def bla1 : Nat := id bla

def bla2 := id bla1
