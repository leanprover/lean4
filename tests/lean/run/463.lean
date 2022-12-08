structure A := (a b : Nat)
structure B extends A := (c : Nat)
structure C := (a b c : Nat)
structure D := (toA : A) (c : Nat)

def foo (s : C) : B := {s with} -- works in lean 4, works in lean 3
def bar (s : D) : B := {s with} -- works in lean 4, fails in lean 3
