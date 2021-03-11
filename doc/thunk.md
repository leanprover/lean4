# Thunks, Tasks, and Threads

A `Thunk` is defined as
```lean
# namespace Ex
# universe u
structure Thunk (α : Type u) : Type u where
  fn : Unit → α
# end Ex
```
A `Thunk` encapsulates a computation without evaluation.
That is, a `Thunk` stores the way of how the value would be computed.
The Lean runtime has special support for `Thunk`s. It caches their values
after they are computed for the first time. This feature is useful for implementing
data structures such as lazy lists.
Here is a small example using a `Thunk`.
```lean
def fib : Nat → Nat
  | 0   => 0
  | 1   => 1
  | x+2 => fib (x+1) + fib x

def f (c : Bool) (x : Thunk Nat) : Nat :=
  if c then
    x.get
  else
    0

def g (c : Bool) (x : Nat) : Nat :=
  f c (Thunk.mk (fun _ => fib x))

#eval g false 1000
```
The function `f` above uses `x.get` to evaluate the `Thunk` `x`.
The expression `Thunk.mk (fun _ => fib x)` creates a `Thunk` for computing `fib x`.
Note that `fib` is a very naive function for computing the Fibonacci numbers,
and it would an unreasonable amount of time to compute `fib 1000`. However, our
test terminates instantaneously because the `Thunk` is not evaluated when `c` is `false`.
Lean has a builtin coercion from any type `a` to `Thunk a`. You write the function `g` above as
```lean
# def fib : Nat → Nat
#  | 0   => 0
#  | 1   => 1
#  | x+2 => fib (x+1) + fib x
# def f (c : Bool) (x : Thunk Nat) : Nat :=
#  if c then
#    x.get
#  else
#    0
def g (c : Bool) (x : Nat) : Nat :=
  f c (fib x)

#eval g false 1000
```
In the following example, we use the macro `dbg_trace` to demonstrate
that the Lean runtime caches the value computed by a `Thunk`.
We remark that the macro `dbg_trace` should be use for debugging purposes
only.
```lean
def add1 (x : Nat) : Nat :=
  dbg_trace "add1: {x}"
  x + 1

def double (x : Thunk Nat) : Nat :=
  x.get + x.get

def triple (x : Thunk Nat) : Nat :=
  double x + x.get

def test (x : Nat) : Nat :=
  triple (add1 x)

#eval test 2
-- add1: 2
-- 9
```
Note that the message `add1: 2` is printed only once.
Now, consider the same example using `Unit -> Nat` instead of `Thunk Nat`.
```lean
def add1 (x : Nat) : Nat :=
  dbg_trace "add1: {x}"
  x + 1

def double (x : Unit -> Nat) : Nat :=
  x () + x ()

def triple (x : Unit -> Nat) : Nat :=
  double x + x ()

def test (x : Nat) : Nat :=
  triple (fun _ => add1 x)

#eval test 2
-- add1: 2
-- add1: 2
-- 9
```
Now, the message `add1: 2` is printed twice.
It may come as a surprise that it was printed twice instead of three times.
As we pointed out, `dbg_trace` is a macro used for debugging purposes only,
and `add1` is still considered to be a pure function.
The Lean compiler performs common subexpression elimination when compiling `double`,
and the produced code for `double` executes `x ()` only once instead of twice.
This transformation is safe because `x : Unit -> Nat` is pure.
