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

The command `import` loads existing libraries and extensions. The
following command imports the command `find` that searches the Lean
environment using regular expressions

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
for `n = n`. In Lean, `refl` is the reflexivity axiom.

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
`n = o`, where `trans` is the transitivity axiom.

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

Most systems based on the _propositions as types_ paradigm are based on constructive logic.
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

The theorem `nat_trans3` has 7 parameters, it takes for natural numbers `a`, `b`, `c` and `d`,
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
However, the first four parameters can be inferred from the last 3. We can use `_` as placeholder
that instructs Lean to synthesize this expression. The synthesis process is based on type inference, and it is
the most basic forms of automation provided by Lean.

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

Sometimes, Lean will not be able to infer the parameters automatically.
So, whenever we define a theorem/definition/axiom/variable containing implicit arguments, Lean will
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

We can also instruct Lean to display all implicit arguments when it prints expressions.
This is useful when debugging non-trivial problems.

```lean
      set_option pp::implicit true   -- show implicit arguments
      check nat_trans3i Hxy Hzy Hzw
      set_option pp::implicit false  -- hide implicit arguments
```

In the previous example, the `check` command stated that `nat_trans3i Hxy Hzy Hzw`
has type `@eq ℕ x w`. The expression `x = w` is just notational convenience.

We have seen many occurrences of `TypeU`. It is just a definition for: `(Type U)`, where `U` is a _universe variable_.
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
we would still have the question: how big should `i` be? Moreover, if we choose an `i` that is not big enough
we have to go back and correct all libraries. This is not satisfactory and not modular.
So, in Lean, we allow user to declare _universe variables_ and simple constraints between them. The Lean kernel defines
one universe variable `U`, and states that `U ≥ 1` using the command `universe U ≥ 1`.
The Lean type casting library defines another universe variable called `M` and states that `universe M ≥ 1` and `universe M ≥ U + 1`.
Lean reports an universe inconsistency if the universe constraints are inconsistent. For example, it will return an error
if execute the command `universe M ≥ U`. We can view universe variables as placeholders, and we can always solve
the universe constraints and find and assignment for the universe variables used in our developments.
This assignment allows us to produce a Lean specification that is not based on this particular feature.

Propositional logic
-------------------

To manipulate formulas with a richer logical structure, it is important to master the notation Lean uses for building
composite logical expressions out of basic formulas using _logical connectives_. The logical connectives (`and`, `or`, `not`, etc)
are defined in the Lean [kernel](../../src/builtin/kernel.lean). The kernel also defines notational convention for rewriting formulas
in a natural way. Here is a table showing the notation for the so called propositional (or Boolean) connectives.


| Ascii | Ascii alt.  | Unicode  | Definition  |
|-------|--------------|---------|--------------|
| true  |              | ⊤       |   true       |
| false |              | ⊥       |   false      |
| not   |              | ¬       |   not        |
| /\    | &&           | ∧       |   and        |
| ‌\/    | &#124;&#124; | ∨       |   or         |
| ->    |              | →      |  implies     |
| <->   |              | ↔       |  iff         |

`true` and `false` are logical constants to denote the true and false propositions. Logical negation is a unary operator just like
arithmetical negation on numbers. The other connectives are all binary operators. The meaning of the operators is the usual one.
The table above makes clear that Lean supports unicode characters. We can use Ascii or/and unicode versions.
Here is a simple example using the connectives above.

```lean
    variable q : Bool
    check p → q → p ∧ q
    check ¬ p → p ↔ false
    check p ∨ q → q ∨ p
    -- Ascii version
    check p -> q -> p && q
    check not p -> p <-> false
    check p || q -> q \/ p
```

Depending on the platform, Lean uses unicode characters by default when printing expressions. The following commands can be used to
change this behavior.

```lean
    set_option pp::unicode false
    check p → q → p ∧ q
    set_option pp::unicode true
    check p → q → p ∧ q
```

Note that, it may seem that the symbols `->` and `→` are overloaded, and Lean uses them to represent Boolean implication and the type
of functions. Actually, they are not overloaded, they are the same symbols. In Lean, the Boolean `p → q` expression is also the type
of the functions that given a proof for `p`, returns a proof for `q`. This is very convenient for writing proofs.

```lean
   -- Hpq is a function that takes a proof for p and returns a proof for q
   axiom Hpq : p → q
   -- Hq is a proof/certificate for p
   axiom Hp  : p
   -- The expression Hpq Hp is a proof/certificate for q
   check Hpq Hp
```

In composite expressions, the precedences of the various binary
connectives are in order of the above table, with `and` being the
strongest and `iff` the weakest. For example, `a ∧ b → c ∨ d ∧ e`
means `(a ∧ b) → (c ∨ (d ∧ e))`. All of them are right-associative.
So, `p ∧ q ∧ r` means `p ∧ (q ∧ r)`. The actual precedence and fixity of all
logical connectives is defined in the Lean [kernel definition file](../../src/builtin/kernel.lean).

Finally, `not`, `and`, `or` and `iff` are the actual names used when
defining the Boolean connectives. They can be used as any other function.

```lean
   check and
   check or
   check not
```

Lean supports _currying_ `and true` is a function from `Bool` to `Bool`.

```lean
   check and true
   definition id := and true
   eval id true
   eval id false
```

Functions
---------

There are many variable-binding constructs in mathematics. Lean expresses
all of them using just one _abstraction_, which is a converse operation to
function application. Given a variable `x`, a type `A`, and a term `t` that
may or may not contain `x`, one can construct the so-called _lambda abstraction_
`fun x : A, t`, or using unicode notation `λ x : A, t`. Here is some simple
examples.

```lean
   check fun x : Nat, x + 1
   check fun x y : Nat, x + 2 * y
   check fun x y : Bool, not (x ∧ y)
   check λ x : Nat, x + 1
   check λ (x : Nat) (p : Bool), x = 0 ∨ p
```

In many cases, Lean can automatically infer the type of the variable. Actually,
In all examples above, the type can be automatically inferred.

```lean
   check fun x, x + 1
   check fun x y, x + 2 * y
   check fun x y, not (x ∧ y)
   check λ x, x + 1
   check λ x p, x = 0 ∨ p
```

However, Lean will complain that it cannot infer the type of the
variable in `fun x, x` because any type would work in this example.

The following example shows how to use lambda abstractions in
function applications

```lean
   eval (fun x y, x + 2 * y) 1
   eval (fun x y, x + 2 * y) 1 2
   eval (fun x y, not (x ∧ y)) true false
```

Lambda abstractions are also used to create proofs for propositions of the form `A → B`.
This should be natural since Lean views `A → B` as the type of functions that given
a proof for `A` returns a proof for `B`.
For example, a proof for `p → p` is just `fun H : p, H` (the identity function).

```lean
    check fun H : p, H
```

Definitional equality
---------------------

Recall that the command `eval t` computes a normal form for the term `t`.
In Lean, we say two terms are _definitionally equal_ if the have the same
normal proof. For example, the terms `(λ x : Nat, x + 1) a` and `a + 1`
are definitionally equal. The Lean type/proof checker uses the normalizer/evaluator when
checking types/proofs. So, we can prove that two definitionally equal terms
are equal using just `refl`. Here is a simple example.

```lean
   theorem def_eq_th (a : Nat) : ((λ x : Nat, x + 1) a) = a + 1
   := refl (a+1)
```

Provable equality
-----------------

In the previous examples, we have used `nat_trans3 x y z w Hxy Hzy Hzw`
to show that `x = w`. In this case, `x` and `w` are not definitionally equal,
but they are provably equal in the environment that contains `nat_trans3` and
axioms `Hxy`, `Hzy` and `Hzw`.

Proving
-------

The Lean kernel contains basic theorems for creating proof terms.  The
basic theorems are useful for creating manual proofs. The are also the
basic building blocks used by all automated proof engines available in
Lean. The theorems can be broken into three different categories:
introduction, elimination, and rewriting. First, we cover the introduction
and elimination theorems for the basic Boolean connectives.

### And (conjuction)

The expression `and_intro H1 H2` creates a proof for `a ∧ b` using proofs
`H1 : a` and `H2 : b`. We say `and_intro` is the _and-introduction_ operation.
In the following example we use `and_intro` for creating a proof for
`p → q → p ∧ q`.

```lean
   check fun (Hp : p) (Hq : q), and_intro Hp Hq
```

The expression `and_eliml H` creates a proof `a` from a proof `H : a ∧ b`.
Similarly `and_elimr H` is a proof for `b`. We say they are the _left/right and-elimination_.

```lean
   -- Proof for p ∧ q → p
   check fun H : p ∧ q, and_eliml H
   -- Proof for p ∧ q → q
   check fun H : p ∧ q, and_elimr H
```

Now, we prove `p ∧ q → q ∧ p` with the following simple proof term.

```lean
    check fun H : p ∧ q, and_intro (and_elimr H) (and_eliml H)
```

Note that the proof term is very similar to a function that just swaps the
elements of a pair.

### Or (disjuction)

The expression `or_introl H1 b` creates a proof for `a ∨ b` using a proof `H1 : a`.
Similarly, `or_intror a H2` creates a proof for `a ∨ b` using a proof `H2 : b`.
We say they are the _left/right or-introduction_.

```lean
   -- Proof for p → p ∨ q
   check fun H : p, or_introl H q
   -- Proof for q → p ∨ q
   check fun H : q, or_intror p H
```

The or-elimination rule is slightly more complicated. The basic idea is the
following, we can prove `c` from `a ∨ b`, by showing we can prove `c`
by assuming `a` or by assuming `b`. It is essentially a proof by cases.
`or_elim Hab Hac Hbc` takes three arguments `Hab : a ∨ b`, `Hac : a → c` and `Hbc : b → c` and produces a proof for `c`.
In the following example, we use `or_elim` to prove that `p v q → q ∨ p`.

```lean
   check fun H : p ∨ q,
           or_elim H
              (fun Hp : p, or_intror q Hp)
              (fun Hq : q, or_introl Hq p)
```

### Not (negation)

`not_intro H` produces a proof for `¬ a` from `H : a → false`. That is,
we obtain `¬ a` if we can derive `false` from `a`. The expression
`absurd_elim b Ha Hna` produces a proof for `b` from `Ha : a` and `Hna : ¬ a`.
That is, we can deduce anything if we have `a` and `¬ a`.
We now use `not_intro` and `absurd_elim` to produce a proof term for
`(a → b) → ¬ b → ¬ a`

```lean
   variables a b : Bool
   check fun (Hab : a → b) (Hnb : ¬ b),
             not_intro (fun Ha : a, absurd_elim false (Hab Ha) Hnb)
```

Here is the proof term for `¬ a → b → (b → a) → c`

```lean
   variable c : Bool
   check fun (Hna : ¬ a) (Hb : b) (Hba : b → a),
             absurd_elim c (Hba Hb) Hna
```

### Iff (if-and-only-if)

The expression `iff_intro H1 H2` produces a proof for `a ↔ b` from `H1 : a → b` and `H2 : b → a`.
`iff_eliml H` produces a proof for `a → b` from `H : a ↔ b`. Similarly,
`iff_elimr H` produces a proof for `b → a` from `H : a ↔ b`.
Note that, in Lean, `a ↔ b` is definitionally equal to `a = b` when `a` and `b` have type `Bool`.
Here is the proof term for `a ∧ b ↔ b ∧ a`

```lean
   check iff_intro (fun H : a ∧ b, and_intro (and_elimr H) (and_eliml H))
                   (fun H : b ∧ a, and_intro (and_elimr H) (and_eliml H))
```

### True and False

The expression `trivial` is a proof term for `true`, and `false_elim a H`
produces a proof for `a` from `H : false`.

Other basic operators used in proof construction are `eqt_intro`, `eqt_elim`, `eqf_intro` and `eqf_elim`.
`eqt_intro H` produces a proof for `a ↔ true` from `H : a`.
`eqt_elim H` produces a proof for `a` from `H : a ↔ true`.
`eqf_intro H` produces a proof for `a ↔ false` from `H : ¬ a`.
`eqf_elim H` produces a proof for `¬ a` from `H : a ↔ false`.

```lean
    check @eqt_intro
    check @eqt_elim
    check @eqf_intro
    check @eqf_elim
```

### Rewrite rules

The Lean kernel also contains many theorems that are meant to be used as rewriting/simplification rules.
The conclusion of these theorems is of the form `t = s` or `t ↔ s`. For example, `and_id a` is proof term for
`a ∧ a ↔ a`. The Lean simplifier can use these theorems to automatically create proof terms for us.
The expression `(by simp [rule-set])` is similar to `_`, but it tells Lean to synthesize the proof term using the simplifier
using the rewrite rule set named `[rule-set]`. In the following example, we create a simple rewrite rule set
and use it to prove a theorem that would be quite tedious to prove by hand.

```lean
    -- import module that defines several tactics/strategies including "simp"
    import tactic
    -- create a rewrite rule set with name 'simple'
    rewrite_set simple
    -- add some theorems to the rewrite rule set 'simple'
    add_rewrite and_id and_truer and_truel and_comm and_assoc and_left_comm iff_id : simple
    theorem th1 (a b : Bool) : a ∧ b ∧ true ∧ b ∧ true ∧ b ↔ a ∧ b
    := (by simp simple)
```

In Lean, we can combine manual and automated proofs in a natural way. We can manually write the proof
skeleton and use the `by` construct to invoke automated proof engines like the simplifier for filling the
tedious steps. Here is a very simple example.

```lean
   theorem th2 (a b : Bool) : a ∧ b ↔ b ∧ a
   := iff_intro
        (fun H : a ∧ b, (by simp simple))
        (fun H : b ∧ a, (by simp simple))
```
