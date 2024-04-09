/-!
# Testing left to right semantics for field instantiation

Implemented in PR #2478 for issue #2451.
-/

set_option pp.structureInstances.flatten false

structure A where
  x : Nat

structure B where
  x : Nat
  y : Nat

/-!
Uses a.x
-/
def foo (a : A) (b : B) : B := {a, b with}

/-!
Uses only b
-/
def boo (a : A) (b : B) : B := {b, a with}

structure C extends B

/-!
Uses a.x
-/
def baz (a : A) (b : B) : C := {a, b with}

/-!
Uses only b
-/
def biz (a : A) (b : B) : C := {b, a with}

/-!
Uses a.x
-/
def faz (a : A) (c : C) : C := {a, c with}

/-!
Uses only b
-/
def fiz (a : A) (c : C) : C := {c, a with}

#print foo
#print boo
#print baz
#print biz
#print faz
#print fiz
