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
/--
info: def b : B :=
let __src := a;
{ toA := __src }
-/
#guard_msgs in #print b

def c : C := { a with }
/--
info: def c : C :=
let __src := a;
{ toB := { toA := __src } }
-/
#guard_msgs in #print c

def d : D := { c with }
/--
info: def d : D :=
let __src := c;
{ toB := __src.toB }
-/
#guard_msgs in #print d
