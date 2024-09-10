/-!
# Testing eta reduction for structure instances

Implemented in PR #2478 for issue #2451.
-/

set_option pp.structureInstances.flatten false

structure A where
  x : Nat

structure B extends A

structure C extends B

structure D extends B

def a : A := ⟨ 0 ⟩

def b : B := { a with }
#print b

def c : C := { a with }
#print c

def d : D := { c with }
#print d
