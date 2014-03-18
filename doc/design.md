Design
------

In Lean, the main activity consists in building Environments containing: definitions, theorems, axioms and variable definitions.
We *cannot* make a consistent environment *Env* inconsistent by adding definitions and/or theorems. This is guaranteed by the Lean Kernel.

On the other hand, a user can make the environment inconsistent by adding axioms and variable definitions.
Regarding variable definitions, the inconsistency can be introduced when a user declares that an empty type is inhabited.
Actually, variable definitions and axioms have the same status from the Lean Kernel point of view.
There is no real difference. An command `axiom H : a > 0` is conceptually identical to `variable H : a > 0`.
Similarly, a Theorem is just a definition.
The Kernel does not provide any form of automation. It is just doing "bookkeeping" and type checking.
In Lean, _proof checking is type checking_.

Building objects such as definitions and theorems without any form of automation is quite laborious.
So, one of the main goals of the Lean project is to provide a lot of building blocks to automate the process of creating
new definitions and theorems.

In Lean, we allow users to provide partially specified objects such as definitions and theorems.
A partially specified object is an object with **holes**. Holes mark the parts that must be automatically constructed by Lean.
In a nutshell, Lean can be viewed as a system for synthesizing proofs, terms, types, etc. Here is a simple example:

    variable a : nat
    axiom a > 0
    theorem T : a >= 1 := _

We use `_` to denote holes. In the simple example above, the "whole proof" must be automatically computed by Lean. Here is another simple example:

    variable f : forall (A : Type), A -> A -> A
    definition f00 : nat := f _ 0 0

In this example, Lean will automatically fill the hole with `nat` (the type of the natural numbers).
Here is another example with multiple holes.

    variable g : forall (A : Type), A -> A
    variable a : nat
    variable b : nat
    axiom H1 : a = b
    axiom H2 : (g _ a) > 0
    theorem T1 : (g _ b) > 0 := _

Lean supports multiple frontends. The default frontend provides several features that automatically create holes for users.
For example, we can write:

    variable g {A : Type} (a : A) : A

`g` is a function with two arguments. The curly braces are used to mark _implicit arguments_.
Then, whenever we write `g a`, the system automatically creates `g _ a`.

The _Lean elaborator_ is the module responsible for filling the holes.
Actually, it only manages the collection of tools and components that do all the hard work.
When we provide an object with holes to the elaborator, one of the following outputs is possible

1) The elaborator succeeds and fill all the holes, and the Lean Kernel accepts the elaborated object without holes.

2) The elaborator succeeds and fill all the holes, but the Lean Kernel rejects the elaborated object.
The elaborator uses many different components. Some of these components may have bugs.
The Lean Kernel is the last firewall that will prevent an ill-formed object from being included in the environment.

3) The elaborator fails to fill the holes, and produces a new environment that demonstrates that it is impossible to fill the holes.
We can view the new environment as a counter-example. Moreover, the new environment provides definitions and theorems for all user
defined variables and axioms.

4) Finally, the elaborator may fail because of its own limitations. In this case, it produces error messages and/or unsolved goals.
It might still be possible to fill the hole, but the elaborator does not know how to do it.
Users may react by filling some of the holes themselves, or realizing that it is indeed impossible to fill the holes.

In Lean, we will provide a frontend for the SMT 2.0 standard. It is very straightforward to map the SMT constructs into the framework above.
For example, the SMT commands

    (declare-fun a () Int)
    (declare-fun b () Int)
    (assert (> a 0))
    (assert (< b a))
    (check-sat)

are mapped to

    variable a : int
    variable b : int
    axiom H1 : a > 0
    axiom H2 : b < a
    theorem Unsat : false := _

If Lean can prove `false`, then it produces a proof that demonstrates that the set of SMT assertions is unsatisfiable.
If the set of assertions is satisfiable, then it produces a new environment that provides definitions for `a` and `b`
and theorems for each assertion. Of course, as we discussed above, Lean may also fail and return error messages describing why it failed.
