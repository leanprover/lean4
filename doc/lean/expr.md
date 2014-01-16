# Expressions

Lean is based on dependent type theory, and is very similar to the one
used in the [Boole](https://github.com/avigad/boole) and
[Coq](http://coq.inria.fr/) systems.  In contrast to Coq, Lean is
classical.

In Lean, we have the following kind of expressions: _constants_,
,_function applications_, _(heterogeneous) equality_, _local variables_,
_lambdas_, _dependent function spaces_ (aka _Pis_), _let expressions_,
and _Types_.

## Constants

Constants are essentially references to variable declarations, definitions, axioms and theorems in the
environment. In the following example, we use the command `variables` to declare `x` and `y` as integers.
The `check` command displays the type of the given expression. The `x` and `y` in the `check` command
are constants. They reference the objects declared using the command `variables`.

```lean
variables x y : Nat
check x + y
```

In the following example, we define the constant `s` as the sum of `x` and `y` using the `definition` command.
The `eval` command evaluates (normalizes) the expression `s + 1`. In this example, `eval` will just expand
the definition of `s`, and return `x + y + 1`.

```lean
definition s := x + y
eval s + 1
```

## Function applications

In Lean, the expression `f t` is a function application, where `f` is a function that is applied to `t`.
In the following example, we define the function `max`. The `eval` command evaluates the application `max 1 2`,
and returns the value `2`. Note that, the expression `if (x >= y) then x else y` is also a function application.
It is notation for `ite (x >= y) x y`.

```lean
import if_then_else
definition max (x y : Nat) : Nat := if (x >= y) then x else y
eval max 1 2
```

The expression `max 1` is also a valid expression in Lean, and it has type `Nat -> Nat`.

```lean
check max 1
```

In the following command, we define the function `inc`, and evaluate some expressions using `inc` and `max`.

```lean
definition inc (x : Nat) : Nat := x + 1
eval inc (inc (inc 2))
eval max (inc 2) 2 = 3
```
