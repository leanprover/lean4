/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Tactic.Omega.Frontend

/-!
# `omega`

This is an implementation of the `omega` algorithm, currently without "dark" and "grey" shadows,
although the framework should be compatible with adding that part of the algorithm later.

The implementation closely follows William Pugh's
"The omega test: a fast and practical integer programming algorithm for dependence analysis"
https://doi.org/10.1145/125826.125848.

The `MetaM` level `omega` tactic takes a `List Expr` of facts,
and tries to discharge the goal by proving `False`.

The user-facing `omega` tactic first calls `false_or_by_contra`, and then invokes the `omega` tactic
on all hypotheses.

### Pre-processing

In the `false_or_by_contra` step, we:
* if the goal is `False`, do nothing,
* if the goal is `¬ P`, introduce `P`,
* if the goal is `x ≠ y`, introduce `x = y`,
* otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.

The `omega` tactic pre-processes the hypotheses in the following ways:
* Replace `x > y` for `x y : Nat` or `x y : Int` with `x ≥ y + 1`.
* Given `x ≥ y` for `x : Nat`, replace it with `(x : Int) ≥ (y : Int)`.
* Push `Nat`-to-`Int` coercions inwards across `+`, `*`, `/`, `%`.
* Replace `k ∣ x` for a literal `k : Nat` with `x % k = 0`,
  and replace `¬ k ∣ x` with `x % k > 0`.
* If `x / m` appears, for some `x : Int` and literal `m : Nat`,
  replace `x / m` with a new variable `α` and add the constraints
  `0 ≤ - m * α + x ≤ m - 1`.
* If `x % m` appears, similarly, introduce the same new constraints
  but replace `x % m` with `- m * α + x`.
* Split conjunctions, existentials, and subtypes.
* Record, for each appearance of `(a - b : Int)` with `a b : Nat`, the disjunction
  `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`.
  We don't immediately split this; see the discussion below for how disjunctions are handled.

After this preprocessing stage, we have a collection of linear inequalities
(all using `≤` rather than `<`) and equalities in some set of atoms.

TODO: We should identify atoms up to associativity and commutativity,
so that `omega` can handle problems such as `a * b < 0 && b * a > 0 → False`.
This should be a relatively easy modification of the `lookup` function in `OmegaM`.
After doing so, we could allow the preprocessor to distribute multiplication over addition.

### Normalization

Throughout the remainder of the algorithm, we apply the following normalization steps to
all linear constraints:
* Make the leading coefficient positive (thus giving us both upper and lower bounds).
* Divide through by the GCD of the coefficients, rounding the constant terms appropriately.
* Whenever we have both an upper and lower bound for the same coefficients,
  check they are compatible. If they are tight, mark the pair of constraints as an equality.
  If they are inconsistent, stop further processing.

### Solving equalities

The next step is to solve all equalities.

We first solve any equalities that have a `±1` coefficient;
these allow us to eliminate that variable.

After this, there may be equalities remaining with all coefficients having absolute value greater
than one. We select an equality `c₀ + ∑ cᵢ * xᵢ = 0` with smallest minimal absolute value
of the `cᵢ`, breaking ties by preferring equalities with smallest maximal absolute value.
We let `m = ∣cⱼ| + 1` where `cⱼ` is the coefficient with smallest absolute value..
We then add the new equality `(bmod c₀ m) + ∑ (bmod cᵢ m) xᵢ = m α` with `α` being a new variable.
Here `bmod` is "balanced mod", taking values in `[- m/2, (m - 1)/2]`.
This equality holds (for some value of `α`) because the left hand side differs from the left hand
side of the original equality by a multiple of `m`.
Moreover, in this equality the coefficient of `xⱼ` is `±1`, so we can solve and eliminate `xⱼ`.

So far this isn't progress: we've introduced a new variable and eliminated a variable.
However, this process terminates, as the pair `(c, C)` lexicographically decreases,
where `c` is the smallest minimal absolute value and `C` is the smallest maximal absolute value
amongst those equalities with minimal absolute value `c`.
(Happily because we're running this in metaprogramming code, we don't actually need to prove this
termination! If we later want to upgrade to a decision procedure, or to produce counterexamples
we would need to do this. It's certainly possible, and existed in an earlier prototype version.)

### Solving inequalities

After solving all equalities, we turn to the inequalities.

We need to select a variable to eliminate; this choice is discussed below.

#### Shadows

The omega algorithm indicates we should consider three subproblems,
called the "real", "dark", and "grey" shadows.
(In fact the "grey" shadow is a disjunction of potentially many problems.)
Our problem is satisfiable if and only if the real shadow is satisfiable
and either the dark or grey shadow is satisfiable.

Currently we do not implement either the dark or grey shadows, and thus if the real shadow is
satisfiable we must fail, and report that we couldn't find a contradiction, even though the
problem may be unsatisfiable.

In practical problems, it appears to be relatively rare that we fail because of not handling the
dark and grey shadows.

Fortunately, in many cases it is possible to choose a variable to eliminate such that
the real and dark shadows coincide, and the grey shadows are empty. In this situation
we don't lose anything by ignoring the dark and grey shadows.
We call this situation an exact elimination.
A sufficient condition for exactness is that either all upper bounds on `xᵢ` have unit coefficient,
or all lower bounds on `xᵢ` have unit coefficient.
We always prefer to select the value of `i` so that this condition holds, if possible.
We break ties by preferring to select a value of `i` that minimizes the number of new constraints
introduced in the real shadow.

#### The real shadow: Fourier-Motzkin elimination

The real shadow for a variable `i` is just the Fourier-Motzkin elimination.

We begin by discarding all inequalities involving the variable `i`.

Then, for each pair of constraints `f ≤ c * xᵢ` and `c' * xᵢ ≤ f'`
with both `c` and `c'` positive (i.e. for each pair of an lower and upper bound on `xᵢ`)
we introduce the new constraint `c * f' - c' * f ≥ 0`.

(Note that if there are only upper bounds on `xᵢ`, or only lower bounds on `xᵢ` this step
simply discards inequalities.)

#### The dark and grey shadows

For each such new constraint `c' * f - c * f' ≤ 0`, we either have the strengthening
`c * f' - c' * f ≥ c * c' - c - c' + 1`
or we do not, i.e.
`c * f' - c' * f ≤ c * c' - c - c'`.
In the latter case, combining this inequality with `f' ≥ c' * xᵢ` we obtain
`c' * (c * xᵢ - f) ≤ c * c' - c - c'`
and as we already have `c * xᵢ - f ≥ 0`,
we conclude that `c * xᵢ - f = j` for some `j = 0, 1, ..., (c * c' - c - c')/c'`
(with, as usual the division rounded down).

Note that the largest possible value of `j` occurs with `c'` is as large as possible.

Thus the "dark" shadow is the variant of the real shadow where we replace each new inequality
with its strengthening.
The "grey" shadows are the union of the problems obtained by taking
a lower bound `f ≤ c * xᵢ` for `xᵢ` and some `j = 0, 1, ..., (c * m - c - m)/m`, where `m`
is the largest coefficient `c'` appearing in an upper bound `c' * xᵢ ≤ f'` for `xᵢ`,
and adding to the original problem (i.e. without doing any Fourier-Motzkin elimination) the single
new equation `c * xᵢ - f = j`, and the inequalities
`c * xᵢ - f > (c * m - c - m)/m` for each previously considered lower bound.

As stated above, the satisfiability of the original problem is in fact equivalent to
the satisfiability of the real shadow, *and* the satisfiability of *either* the dark shadow,
or at least one of the grey shadows.

TODO: implement the dark and grey shadows!

### Disjunctions

The omega algorithm as described above accumulates various disjunctions,
either coming from natural subtraction, or from the dark and grey shadows.

When we encounter such a disjunction, we store it in a list of disjunctions,
but do not immediately split it.

Instead we first try to find a contradiction (i.e. by eliminating equalities and inequalities)
without the disjunctive hypothesis.
If this fails, we then retrieve the first disjunction from the list, split it,
and try to find a contradiction in both branches.

(Note that we make no attempt to optimize the order in which we split disjunctions:
it's currently on a first in first out basis.)

The work done eliminating equalities can be reused when splitting disjunctions,
but we need to redo all the work eliminating inequalities in each branch.

## Future work
* Implementation of dark and grey shadows.
* Identification of atoms up to associativity and commutativity of monomials.
* Further optimization.
  * Some data is recomputed unnecessarily, e.g. the GCDs of coefficients.
* Sparse representation of coefficients.
  * I have a branch in which this is implemented, modulo some proofs about algebraic operations
    on sparse arrays.
* Case splitting on `Int.abs`?
-/
