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

The command `using` creates aliases based on give prefix. For example, the following
command creates aliases for all objects starting with `Nat`

```lean
      using Nat
      check ge       -- display the signature of the Nat::ge definition
```

In Lean, proofs are also expressions, and theorems are essentially definitions.
In the following example we prove that `double x = 2 * x`

```lean
      theorem double_x_eq_2x (x : Nat) : double x = 2 * x :=
        calc double x  =  x + x      :   refl (double x)
                   ... =  1*x + 1*x  :   { symm (mul::onel x) }
                   ... =  (1 + 1)*x  :   symm (distributel 1 1 x)
                   ... =  2 * x      :   { refl (1 + 1) }
```

In the example above, we provided the proof manually using a calculational proof style.
The terms after `:` are proof terms. They justify the equalities in the left-hand-side.
The proof term `refl (double x)` produces a proof for `t = s` where `t` and `s` have the same
normal form of `(double x)`.  The proof term `{ symm (mul::onel x) }` is a justification for
the equality `x = 1*x`. The curly braces instruct Lean to replace `x` with `1*x`.
Similarly `{ symm (distributel 1 1 x) }` is a proof for `1*x + 1*x = (1 + 1)*x`.
The exact semantics of these expressions is not important at this point.




Objects
-------

In each Lean session, we create an enviroment, a sequence of named
objects such as: definitions, axioms and theorems. Each object has
a unique name. We use `hierarchical names` in Lean, i.e., a sequence
of regular identifiers separated by `::`. Hierarchical names provide
a cheap of simulating modules and namespaces in Lean.

Expressions
-----------

Each expression has a unique type in Lean. The command `check` returns
the type of an expression.

```lean
        check 1+2.
```
