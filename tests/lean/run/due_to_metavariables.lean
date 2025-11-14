/--
error: typeclass instance problem is stuck
  HMul ?m.9 ?m.9 String

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `HMul` are metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def f1 x := (x * x : String)

/--
error: typeclass instance problem is stuck
  HMul String ?m.8 (?m.3 x)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `HMul` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def f2 x := "huh" * x

/--
error: typeclass instance problem is stuck
  HMul (Option ?m.4) ?m.9 (?m.3 x)

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `HMul` contain metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def f3 x := Option.none * x

/--
error: typeclass instance problem is stuck
  LT ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LT` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def f4 x := x < x

/--
error: typeclass instance problem is stuck
  LT (Option ?m.4)

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LT` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
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

Note: Lean will not try to resolve this typeclass instance problem because the first, third, fourth, and fifth type arguments to `Many` are metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def f x := test x 3 x x x

/-
From Joseph's lean4-error-messages#41, this generates two stuck typeclass
problems, `Decidable (x < y)` (unhelpfully the metavariables aren't even
visible!) with a span of the entire ite, and `LT _?` with the span of just the
scrutinee. The error message associated with the smaller range is better.
-/
/--
error: typeclass instance problem is stuck
  LT ?m.13

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LT` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def min x y := if x < y then x else y

def isDigitEven? [Monad m] [Alternative m] (n : Nat) : m Bool := do
  guard (n < 10)
  return n % 2 == 0

/-
From Joseph's lean4-error-messages#81, this is similar to the previous example
and is addressed by preferring any synthetic MVar problem that isn't a
stuck typeclass resolution instance. Preferring smaller ranges generically
would also work here.
-/
/--
error: Application type mismatch: The argument
  isDigitEven? n
has type
  ?m.9 Bool
but is expected to have type
  Prop
in the application
  @ite (Option Nat) (isDigitEven? n)
-/
#guard_msgs in
def myOption (s : String) : Option Nat := do
  let n ← s.toNat?
  if isDigitEven? n then
    return n
  else
    return 2 * n

instance {n} : Functor (Vector · n) where
  map f v := v.map f

/-
From Joseph's lean4-error-messages#56, this is a case where we *might* want to
tweak prioritization in the future. This creates a typeclass resolution
problem over the whole expression `Functor ?m.2`, and higher-order unification
can't solve that `?m.2 = Vector · 3`.
-/
/--
error: Application type mismatch: The argument
  #v[1, 2, 3]
has type
  Vector Nat 3
but is expected to have type
  ?m.2 ?m.6
in the application
  id <$> #v[1, 2, 3]
-/
#guard_msgs in
#eval Functor.map id #v[1, 2, 3]
