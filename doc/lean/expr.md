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

## Heterogeneous equality

For technical reasons, in Lean, we have heterogenous and homogeneous equality. In a nutshell, heterogenous is mainly used internally, and
homogeneous are used externally when writing programs and specifications in Lean.
Heterogenous equality allows us to compare elements of any type, and homogenous equality is just a definition on top of the heterogenous equality that expects arguments of the same type.
The expression `t == s` is a heterogenous equality that is true iff `t` and `s` have the same interpretation.
In the following example, we evaluate the expressions `1 == 2` and `2 == 2`. The first evaluates to `false` and the second to `true`.

```lean
eval 1 == 2
eval 2 == 2
```

Since we can compare elements of different types, the following
expression is type correct, but Lean normalizer/evaluator will *not*
reduce it.

```lean
eval 2 == true
```

We strongly discourage users from directly using heterogeneous equality. The main problem is that it is very easy to
write nonsensical expressions like the one above. The expression `t = s` is a homogeneous equality.
It expects `t` and `s` to have the same type. Thus, the expression `2 = true` is type incorrect in Lean.
The symbol `=` is just notation. Internally, homogeneous equality is defined as:

```
definition eq {A : (Type U)} (x y : A) : Bool := x == y
infix 50 = : eq
```

The curly braces indicate that the first argument of `eq` is implicit. The symbol `=` is just a syntax sugar for `eq`.
In the following example, we use the `set_option` command to force Lean to display implicit arguments and
disable notation when pretty printing expressions.

```lean
set_option pp::implicit true
set_option pp::notation false
check 1 = 2

-- restore default configuration
set_option pp::implicit false
set_option pp::notation true
check 1 = 2
```
