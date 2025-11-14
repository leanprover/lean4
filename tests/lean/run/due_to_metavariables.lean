/--
error: typeclass instance problem is stuck
  HMul ?m.9 ?m.9 String

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to HMul are metavariables. These arguments are inputs, and so they must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f1 x := (x * x : String)

/--
error: typeclass instance problem is stuck
  HMul String ?m.8 (?m.3 x)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to HMul is a metavariable. This argument is an input, and so it must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f2 x := "huh" * x

/--
error: typeclass instance problem is stuck
  HMul (Option ?m.4) ?m.9 (?m.3 x)

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to HMul contain metavariables. These arguments are inputs, and so they must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f3 x := Option.none * x

/--
error: typeclass instance problem is stuck
  LT ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the first type argument to LT is a metavariable. This argument is an input, and so it must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f4 x := x < x

/--
error: typeclass instance problem is stuck
  LT (Option ?m.4)

Note: Lean will not try to resolve this typeclass instance problem because the first type argument to LT contains metavariables. This argument is an input, and so it must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f4 x := Option.none < Option.none

class Many (a b c d e: Type) where
instance : Many Nat Nat Nat Nat Nat where
def test [Many a b c d e] (_x1 : a) (_x2 : b) (_x3 : c) (_x4 : d) (_x5 : e) :=
  3

/--
error: typeclass instance problem is stuck
  Many ?m.1 Nat ?m.1 ?m.1 ?m.1

Note: Lean will not try to resolve this typeclass instance problem because the first, third, fourth, and fifth type arguments to Many are metavariables. These arguments are inputs, and so they must be fully determined before Lean will try to resolve the typeclass.
-/
#guard_msgs in
def f x := test x 3 x x x
