Lean Tutorial
=============

Introduction
------------

Lean is an automatic and interactive theorem prover. It can be used to
create specifications, build mathematical libraries, and solve
constraints. In this tutorial, we introduce basic concepts, the logic
used in Lean, and the main commands.

Getting started
---------------

We can use Lean in interactive or batch mode.
The following example just displays the message `hello world`.

```lean
        print "hello world"
```

All we have to do to run your first example is to call the `lean` executable
with the name of the text file that contains the command above.
If you saved the above command in the file `hello.lean`, then you just have
to execute

       lean hello.lean

As a more complex example, the next example defines a function that doubles
the input value, and then evaluates it on different values.

```lean
      -- defines the double function
      definition double (x : Nat) := x + x

      eval double 10
      eval double 2
      eval double 3 > 4
```

Basics
------

We can also view Lean as a suite of tools for evaluating and processing
expressions representing terms, definitions, and theorems.

Every expression has a unique type in Lean. The command `check` returns the
type of a given expression.

```lean
      check double 3
      check double
```

The last command returns `Nat → Nat`. That is, the type of double is a function
from `Nat` to `Nat`, where `Nat` is the type of the natural numbers.

The command `import` loads existing libraries and extensions. For example,
the following command imports the command `find` that searches the Lean environment
using regular expressions

```lean
      import find

      find "Nat"      -- find all object that start with the prefix Nat
      check Nat::ge   -- display the signature of the Nat::ge definition
```

We say `Nat::ge` is a hierarchical name comprised of two parts: `Nat` and `ge`

The command `using` creates aliases based on a given prefix. For example, the following
command creates aliases for all objects starting with `Nat`

```lean
      using Nat
      check ge       -- display the signature of the Nat::ge definition
```

The command `variable` assigns a type to an identifier. The following command postulates/assumes
that `n`, `m` and `o` have type `Nat`.

```lean
      variable n : Nat
      variable m : Nat
      variable o : Nat
```

The command `variables n m o : Nat` can be used a shorthand for the three commands above.

In Lean, proofs are also expressions, and all functionality provided for manipulating
expressions is also available for manipulating proofs. For example, `refl n` is a proof
for `n == n`. In Lean, `refl` is the reflexivity axiom.

```lean
     check refl n
```

The command `axiom` postulates that a given proposition (aka Boolean formula) is true.
The following commands postulate two axioms `Ax1` and `Ax2` that state that `n = m` and
`m = o`.

```lean
      axiom Ax1 : n = m
      axiom Ax2 : m = o
```

`Ax1` and `Ax2` are not just names. For example, `trans Ax1 Ax2` is a proof that
`n == o`, where `trans` is the transitivity axiom.

```lean
      check trans Ax1 Ax2
```

The expression `trans Ax1 Ax2` is just a function application like any other.
Moreover, in Lean, _propositions are types_. Any Boolean expression `P` can be used
as a type. The elements of type `P` can be viewed as the proofs of `P`.
Moreover, in Lean, _proof checking is type checking_. For example, the Lean type checker
will reject the type incorrect term `trans Ax2 Ax1`.

Because we use _proposition as types_, we must support _empty types_. For example,
the type `false` must be empty, since we don't have a proof for `false`.

Most systems based on _propositions as types_ paradigm are based on constructive logic.
Lean on the other hand is based on classical logic. The _excluded middle_ is a theorem
in Lean, and `em p` is a proof for `p ∨ ¬ p`.

```lean
    variable p : Bool
    check em p
```

The commands `axiom` and `variable` are essentially the same command. We provide both
just to make Lean files more readable. We encourage users to use `axiom` only for
propostions, and `variable` for everything else.

Similarly, a theorem is just a definition. The following command defines a new theorem
called `nat_trans3`

```lean
      theorem nat_trans3 (a b c d : Nat) (H1 : a = b) (H2 : c = b) (H3 : c = d) : a = d
      := trans (trans H1 (symm H2)) H3
```

The theorem `nat_trans3` has 7 parameters, it takes for natural numbers `a`, `b`, `c` and `d,
and three proofs showing that `a = b`, `c = b` and `c = d`, and returns a proof that `a = d`.
In the example above, `symm` is the symmetry theorem. Now, we use `nat_trans3` in a simple
example.

```lean
      variables x y z w : Nat
      axiom Hxy : x = y
      axiom Hzy : z = y
      axiom Hzw : z = w
      check nat_trans3 x y z w Hxy Hzy Hzw
```

The theorem `nat_trans3` is somewhat inconvenient to use because it has 7 parameters.
However, the first four parameters can be inferred from the last 3. We can `_` as placeholder
that instructs Lean to synthesize this expression.

```lean
      check nat_trans3 _ _ _ _ Hxy Hzy Hzw
```

Lean also supports _implicit arguments_.
We mark implicit arguments using curly braces instead of parenthesis.
In the following example, we define the theorem `nat_trans3i` using implicit arguments.

```lean
      theorem nat_trans3i {a b c d : Nat} (H1 : a = b) (H2 : c = b) (H3 : c = d) : a = d
      := trans (trans H1 (symm H2)) H3
```

It is identical to `nat_trans3`, the only difference is the use of curly braces.
Lean will (try to) infer the implicit arguments. The idea behind implicit arguments
is quite simple, we are just instructing Lean to automatically insert the placeholders
`_` for us.

```lean
      check nat_trans3i Hxy Hzy Hzw
```

Sometimes, Lean will not be able to infer the parameters automatically. So, whenever we
define a theorem/definition/axiom/variable containing implicit arguments, Lean will
automatically create an _explicit_ version where all parameters are explicit.
The explicit version uses the same name with a `@` prefix.

```lean
      check @nat_trans3i
```

The axiom `refl`, and the theorems `trans` and `symm` all have implicit arguments.

```lean
      check @refl
      check @trans
      check @symm
```

We can also instruct Lean to display all implicit arguments. This is useful
when debugging non-trivial problems.

```lean
      set_option pp::implicit true   -- show implicit arguments
      check nat_trans3i Hxy Hzy Hzw
      set_option pp::implicit false  -- hide implicit arguments
```

Note that, in the examples above, we have seen two symbols for equality: `=` and `==`.
Moreover, in the previous example, the `check` command stated that `nat_trans3i Hxy Hzy Hzw`
has type `@eq ℕ x w`. For technical reasons, in Lean, we have heterogenous and homogeneous
equality. In a nutshell, heterogenous is mainly used internally, and homogeneous are used externally
when writing programs and specifications in Lean.  Heterogenous equality allows us to compare
elements of any type, and homogenous equality is just a definition on top of the heterogenous
equality that expects arguments of the same type.  The expression `t == s` is a heterogenous equality that is true
iff `t` and `s` have the same interpretation. On the other hand `t = s` is a homogeneous equality,
and is only type correct if `t` and `s` have the same type. The symbol `=` is actually notation for
`eq t s`, where `eq` is defined (using heterogenous equality) as:

```
      definition eq {A : TypeU} (a b : A) : Bool
      := a == b
```

We strongly discourage users from directly using heterogeneous equality. The main problem is that it is very easy to
write nonsensical expressions such as `2 == true`. On the other hand, the expression `2 = true` is type incorrect,
and Lean will report the mistake to the user.

We have seen many occurrences of `TypeU`. It is just a definition: `(Type U)`, where `U` is a _universe variable_.
In Lean, the type of `Nat` and `Bool` is `Type`.

```lean
      check Nat
      check Bool
```

We say `Type` is the type of all _small_ types, but what is the type of `Type`?

```lean
      check Type
```

Lean returns `(Type 1)`. Similarly, the type of `(Type 1)` is `(Type 2)`. In Lean, we also have _universe cumulativity_.
That is, we can provide an element of type `(Type i)` where an element of type `(Type j)` is expected when `i ≤ j`.
This makes the system more convenient to use. Otherwise, we would need a reflexivity axiom for `Type` (i.e., `(Type 0)`),
`Type 1`, `Type 2`, etc. Universe cumulativity improves usability, but it is not enough because
We would still have the question: how big should `i` be? Moreover, if we choose an `i` that is not big enough
we have to go back and correct all libraries. This is not satisfactory and not modular.
So, in Lean, we allow user to declare _universe variables_ and simple constraints between them. The Lean kernel defines
one universe variable `U`, and states that `U ≥ 1` using the command `universe U ≥ 1`.
The Lean type casting library defines another universe variable called `M` and states that `universe M ≥ 1` and `universe M ≥ U + 1`.
Lean reports an universe inconsistency if the universe constraints are inconsistency. For example, it will return an error
if execute the command `universe M ≥ U`. We can view universe variables as placeholders, and we can always solve
the universe constraints and find and assignment for the universe variables used in our developments.
This assignment allows us to produce a Lean specification that is not based on this particular feature.
