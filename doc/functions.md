# Functions

Functions are the fundamental unit of program execution in any programming language.
As in other languages, a Lean function has a name, can have parameters and take arguments, and has a body.
Lean also supports functional programming constructs such as treating functions as values,
using unnamed functions in expressions, composition of functions to form new functions,
curried functions, and the implicit definition of functions by way of
the partial application of function arguments.

You define functions by using the `def` keyword followed by its name, a parameter list, return type and its body.
The parameter list consists of successive parameters that are separated by spaces.
You can specify an explicit type for each parameter.
If you do not specify a specific argument type, the compiler tries to infer the type from the function body.
An error is returned when it cannot be inferred.
The expression that makes up the function body is typically a compound expression consisting of a number of expressions
that culminate in a final expression that is the return value.
The return type is a colon followed by a type and is optional.
If you do not specify the type of the return value explicitly,
the compiler tries to determine the return type from the final expression.

```lean
def f x := x + 1
```
In the previous example, the function name is `f`, the argument is `x`, which has type `Nat`,
the function body is `x + 1`, and the return value is of type `Nat`.
The following example defines the factorial recursive function using pattern matching.
```lean
def fact x :=
  match x with
  | 0   => 1
  | n+1 => (n+1) * fact n

#eval fact 100
```
By default, Lean only accepts total functions. The `partial` keyword should be used when Lean cannot
establish that a function always terminates.
```lean
partial def g (x : Nat) (p : Nat -> Bool) : Nat :=
  if p x then
    x
  else
    g (x+1) p

#eval g 0 (fun x => x > 10)
```
In the previous example, `g x p` only terminates if there is a `y >= x` such that `p y` returns `true`.
Of course, `g 0 (fun x => false)` never terminates.

# Lambda expressions

A lambda expression is an unnamed function.
You define lambda expressions by using the `fun` keyword. A lambda expression resembles a function definition, except that instead of the `:=` token,
the `=>` token is used to separate the argument list from the function body. As in a regular function definition,
the argument types can be inferred or specified explicitly, and the return type of the lambda expression is inferred from the type of the
last expression in the body.

```lean
def twice (f : Nat -> Nat) (x : Nat) : Nat :=
  f (f x)

#eval twice (fun x => x + 1) 3
#eval twice (fun (x : Nat) => x * 2) 3

#eval List.map (fun x => x + 1) [1, 2, 3]
-- [2, 3, 4]

#eval List.map (fun (x, y) => x + y) [(1, 2), (3, 4)]
-- [3, 7]
```

# Syntax sugar for simple lambda expressions

Simple functions can be defined using parentheses and `.` (or `·`) as a placeholder.
```lean
#check (. + 1)
-- fun a => a + 1
#check (· + 1)
-- fun a => a + 1
#check (2 - .)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (. * .) 1
-- 120

def h (x y z : Nat) :=
  x + y + z

#check (h . 1 .)
-- fun a b => h a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
```
In the previous example, the term `(·.1)` is syntax sugar for `fun x => x.1`. Note that, the ASCII version `(..1)`
is not supported because `..` is a reserved symbol.

# Pipelining

Pipelining enables function calls to be chained together as successive operations. Pipelining works as follows:

```lean
def add1 x := x + 1
def times2 x := x * 2

#eval times2 (add1 100)
#eval 100 |> add1 |> times2
#eval times2 <| add1 <| 100
```
The result of the previous `#eval` commands is 202.
The forward pipeline `|>` operator takes a function and an argument and return a value.
In contrast, the backward pipeline `<|` operator takes an argument and a function and returns a value.
These operators are useful for minimizing the number of parentheses.
```lean
def add1Times3FilterEven (xs : List Nat) :=
  List.filter (. % 2 == 0) (List.map (. * 3) (List.map (. + 1) xs))

#eval add1Times3FilterEven [1, 2, 3, 4]
-- [6, 12]

-- Define the same function using pipes
def add1Times3FilterEven' (xs : List Nat) :=
  xs |> List.map (. + 1) |> List.map (. * 3) |> List.filter (. % 2 == 0)

#eval add1Times3FilterEven' [1, 2, 3, 4]
-- [6, 12]
```
Lean also supports the operator `|>.` which combines forward pipeline `|>` operator with the `.` field notation.
```lean
-- Define the same function using pipes
def add1Times3FilterEven'' (xs : List Nat) :=
  xs.map (. + 1) |>.map (. * 3) |>.filter (. % 2 == 0)

#eval add1Times3FilterEven'' [1, 2, 3, 4]
-- [6, 12]
```

For users familiar with the Haskell programming language,
Lean also supports the notation `f $ a` for the backward pipeline `f <| a`.
