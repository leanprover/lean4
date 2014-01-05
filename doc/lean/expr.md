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
environment. In the following example, we use the command `Variables` to declare `x` and `y` as integers.
The `Check` command displays the type of the given expression. The `x` and `y` in the `Check` command
are constants. They reference the objects declared using the command `Variables`.

```lean
Variables x y : Int.
Check x + y.
```

In the following example, we define the constant `s` as the sum of `x` and `y` using the `Definition` command.
The `Eval` command evaluates (normalizes) the expression `s + 1`. In this example, `Eval` will just expand
the definition of `s`, and return `x + y + 1`.

```lean
Definition s := x + y.
Eval s + 1.
```

## Function applications

In Lean, the expression `f t` is a function application, where `f` is a function that is applied to `t`.
In the following example, we define the function `max`. The `Eval` command evaluates the application `max 1 2`,
and returns the value `2`. Note that, the expression `if (x >= y) x y` is also a function application.

```lean
Definition max (x y : Int) : Int := if (x >= y) x y.
Eval max 1 2.
```

The expression `max 1` is also a valid expression in Lean, and it has type `Int -> Int`.

```lean
Check max 1.
```

Remark: we can make the expression `if (x >= y) x y` more "user-friendly" by using custom "Notation".
The following `Notation` command defines the usual `if-then-else` expression. The value `40` is the precedence
of the new notation.

```lean
Notation 40 if _ then _ else _ : if
Check if x >= y then x else y.
```

In the following command, we define the function `inc`, and evaluate some expressions using `inc` and `max`.

```lean
Definition inc (x : Int) : Int := x + 1.
Eval inc (inc (inc 2)).
Eval max (inc 2) 2 = 3.
```

## Heterogeneous equality

For technical reasons, in Lean, we have heterogenous and homogeneous equality. In a nutshell, heterogenous is mainly used internally, and
homogeneous are used externally when writing programs and specifications in Lean.
Heterogenous equality allows us to compare elements of any type, and homogenous equality is just a definition on top of the heterogenous equality that expects arguments of the same type.
The expression `t == s` is a heterogenous equality that is true iff `t` and `s` have the same interpretation.
In the following example, we evaluate the expressions `1 == 2` and `2 == 2`. The first evaluates to `false` and the second to `true`.

```lean
Eval 1 == 2.
Eval 2 == 2.
```

Since we can compare elements of different types, the following expression is type correct and evaluates to `false`.

```lean
Eval 1 == true.
```

This is consistent with the set theoretic semantics used in Lean, where the interpretation of all expressions are sets.
The interpretation of heterogeneous equality is just set equality in the Lean seamtics.

We strongly discourage users from directly using heterogeneous equality. The main problem is that it is very easy to
write expressions that are false like the one above. The expression `t = s` is a homogeneous equality.
It expects `t` and `s` to have the same type. Thus, the expression `1 = true` is type incorrect in Lean.
The symbol `=` is just notation. Internally, homogeneous equality is defined as:

```
Definition eq {A : (Type U)} (x y : A) : Bool := x == y.
Infix 50 = : eq.
```

The curly braces indicate that the first argument of `eq` is implicit. The symbol `=` is just a syntax sugar for `eq`.
In the following example, we use the `SetOption` command to force Lean to display implicit arguments and
disable notation when pretty printing expressions.

```lean
SetOption pp::implicit true.
SetOption pp::notation false.
Check 1 = 2.

(* restore default configuration *)
SetOption pp::implicit false.
SetOption pp::notation true.
Check 1 = 2.
```
