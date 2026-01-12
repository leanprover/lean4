/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
public import Init.Grind.Interactive
public import Init.Grind.Config
public section
namespace Lean.Parser.Tactic
open Parser.Tactic.Grind

/--
`grind` is a tactic inspired by modern SMT solvers. **Picture a virtual whiteboard**:
every time grind discovers a new equality, inequality, or logical fact,
it writes it on the board, groups together terms known to be equal,
and lets each reasoning engine read from and contribute to the shared workspace.
These engines work together to handle equality reasoning, apply known theorems,
propagate new facts, perform case analysis, and run specialized solvers
for domains like linear arithmetic and commutative rings.

See [the reference manual's chapter on `grind`](lean-manual://section/grind-tactic) for more information.

`grind` is *not* designed for goals whose search space explodes combinatorially,
think large pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards,
or a 200‑variable Sudoku encoded as Boolean constraints.  Such encodings require
 thousands (or millions) of case‑splits that overwhelm `grind`’s branching search.

For **bit‑level or combinatorial problems**, consider using **`bv_decide`**.
`bv_decide` calls a state‑of‑the‑art SAT solver (CaDiCaL) and then returns a
*compact, machine‑checkable certificate*.

### Equality reasoning

`grind` uses **congruence closure** to track equalities between terms.
When two terms are known to be equal, congruence closure automatically deduces
equalities between more complex expressions built from them.
For example, if `a = b`, then congruence closure will also conclude that `f a` = `f b`
for any function `f`. This forms the foundation for efficient equality reasoning in `grind`.
Here is an example:
```
example (f : Nat → Nat) (h : a = b) : f (f b) = f (f a) := by
  grind
```

### Applying theorems using E-matching

To apply existing theorems, `grind` uses a technique called **E-matching**,
which finds matches for known theorem patterns while taking equalities into account.
Combined with congruence closure, E-matching helps `grind` discover
non-obvious consequences of theorems and equalities automatically.

Consider the following functions and theorems:
```
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
The theorem `gf` asserts that `g (f x) = x` for all natural numbers `x`.
The attribute `[grind =]` instructs `grind` to use the left-hand side of the equation,
`g (f x)`, as a pattern for E-matching.
Suppose we now have a goal involving:
```
example {a b} (h : f b = a) : g a = b := by
  grind
```
Although `g a` is not an instance of the pattern `g (f x)`,
it becomes one modulo the equation `f b = a`. By substituting `a`
with `f b` in `g a`, we obtain the term `g (f b)`,
which matches the pattern `g (f x)` with the assignment `x := b`.
Thus, the theorem `gf` is instantiated with `x := b`,
and the new equality `g (f b) = b` is asserted.
`grind` then uses congruence closure to derive the implied equality
`g a = g (f b)` and completes the proof.

The pattern used to instantiate theorems affects the effectiveness of `grind`.
For example, the pattern `g (f x)` is too restrictive in the following case:
the theorem `gf` will not be instantiated because the goal does not even
contain the function symbol `g`.

```
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

You can use the command `grind_pattern` to manually select a pattern for a given theorem.
In the following example, we instruct `grind` to use `f x` as the pattern,
allowing it to solve the goal automatically:
```
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
You can enable the option `trace.grind.ematch.instance` to make `grind` print a
trace message for each theorem instance it generates.

You can also specify a **multi-pattern** to control when `grind` should apply a theorem.
A multi-pattern requires that all specified patterns are matched in the current context
before the theorem is applied. This is useful for theorems such as transitivity rules,
where multiple premises must be simultaneously present for the rule to apply.
The following example demonstrates this feature using a transitivity axiom for a binary relation `R`:
```
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z

grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```
By specifying the multi-pattern `R x y, R y z`, we instruct `grind` to
instantiate `Rtrans` only when both `R x y` and `R y z` are available in the context.
In the example, `grind` applies `Rtrans` to derive `R a c` from `R a b` and `R b c`,
and can then repeat the same reasoning to deduce `R a d` from `R a c` and `R c d`.

Instead of using `grind_pattern` to explicitly specify a pattern,
you can use the `@[grind]` attribute or one of its variants, which will use a heuristic to
generate a (multi-)pattern. The complete list is available in the reference manual. The main ones are:

- `@[grind →]` will select a multi-pattern from the hypotheses of the theorem (i.e. it will use the theorem for forwards reasoning).
  In more detail, it will traverse the hypotheses of the theorem from left-to-right, and each time it encounters a minimal indexable
  (i.e. has a constant as its head) subexpression which "covers" (i.e. fixes the value of) an argument which was not
  previously covered, it will add that subexpression as a pattern, until all arguments have been covered.
- `@[grind ←]` will select a multi-pattern from the conclusion of theorem (i.e. it will use the theorem for backwards reasoning).
  This may fail if not all the arguments to the theorem appear in the conclusion.
- `@[grind]` will traverse the conclusion and then the hypotheses left-to-right, adding patterns as they increase the coverage,
  stopping when all arguments are covered.
- `@[grind =]` checks that the conclusion of the theorem is an equality, and then uses the left-hand-side of the equality as a pattern.
  This may fail if not all of the arguments appear in the left-hand-side.

Here is the previous example again but using the attribute `[grind →]`
```
opaque R : Int → Int → Prop
@[grind →] axiom Rtrans {x y z : Int} : R x y → R y z → R x z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```

To control theorem instantiation and avoid generating an unbounded number of instances,
`grind` uses a generation counter. Terms in the original goal are assigned generation zero.
When `grind` applies a theorem using terms of generation `≤ n`, any new terms it creates
are assigned generation `n + 1`. This limits how far the tactic explores when applying
theorems and helps prevent an excessive number of instantiations.

#### Key options:
- `grind (ematch := <num>)` controls the number of E-matching rounds.
- `grind [<name>, ...]` instructs `grind` to use the declaration `name` during E-matching.
- `grind only [<name>, ...]` is like `grind [<name>, ...]` but does not use theorems tagged with `@[grind]`.
- `grind (gen := <num>)` sets the maximum generation.

### Linear integer arithmetic (`lia`)

`grind` can solve goals that reduce to **linear integer arithmetic (LIA)** using an
integrated decision procedure called **`lia`**.  It understands

* equalities   `p = 0`
* inequalities  `p ≤ 0`
* disequalities `p ≠ 0`
* divisibility  `d ∣ p`

The solver incrementally assigns integer values to variables; when a partial
assignment violates a constraint it adds a new, implied constraint and retries.
This *model-based* search is **complete for LIA**.

#### Key options:

* `grind -lia` disable the solver (useful for debugging)
* `grind +qlia` accept rational models (shrinks the search space but is incomplete for ℤ)

#### Examples:

```
-- Even + even is never odd.
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind

-- Mixing equalities and inequalities.
example {x y : Int} :
    2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  grind

-- Reasoning with divisibility.
example (a b : Int) :
    2 ∣ a + 1 → 2 ∣ b + a → ¬ 2 ∣ b + 2 * a := by
  grind

example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  grind

-- Types that implement the `ToInt` type-class.
example (a b c : UInt64)
    : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

### Algebraic solver (`ring`)

`grind` ships with an algebraic solver nick-named **`ring`** for goals that can
be phrased as polynomial equations (or disequations) over commutative rings,
semirings, or fields.

*Works out of the box*
All core numeric types and relevant Mathlib types already provide the required
type-class instances, so the solver is ready to use in most developments.

What it can decide:

* equalities of the form `p = q`
* disequalities `p ≠ q`
* basic reasoning under field inverses (`a / b := a * b⁻¹`)
* goals that mix ring facts with other `grind` engines

#### Key options:

* `grind -ring` turn the solver off (useful when debugging)
* `grind (ringSteps := n)` cap the number of steps performed by this procedure.

#### Examples

```
open Lean Grind

example [CommRing α] (x : α) : (x + 1) * (x - 1) = x^2 - 1 := by
  grind

-- Characteristic 256 means 16 * 16 = 0.
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16) * (x - 16) = x^2 := by
  grind

-- Works on built-in rings such as `UInt8`.
example (x : UInt8) : (x + 16) * (x - 16) = x^2 := by
  grind

example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 = 9 - c^4 := by
  grind

example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

### Other options

- `grind (splits := <num>)` caps the *depth* of the search tree.  Once a branch performs `num` splits
  `grind` stops splitting further in that branch.
- `grind -splitIte` disables case splitting on if-then-else expressions.
- `grind -splitMatch` disables case splitting on `match` expressions.
- `grind +splitImp` instructs `grind` to split on any hypothesis `A → B` whose antecedent `A` is **propositional**.
- `grind -linarith` disables the linear arithmetic solver for (ordered) modules and rings.

### Additional Examples

```
example {a b} {as bs : List α} : (as ++ bs ++ [b]).getLastD a = b := by
  grind

example (x : BitVec (w+1)) : (BitVec.cons x.msb (x.setWidth w)) = x := by
  grind

example (as : Array α) (lo hi i j : Nat) :
    lo ≤ i → i < j → j ≤ hi → j < as.size → min lo (as.size - 1) ≤ i := by
  grind
```
-/
syntax (name := grind)
  "grind" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  (" => " grindSeq)? : tactic

/--
`grind?` takes the same arguments as `grind`, but reports an equivalent call to `grind only`
that would be sufficient to close the goal. This is useful for reducing the size of the `grind`
theorems in a local invocation.
-/
syntax (name := grindTrace)
  "grind?" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  : tactic

/--
`cutsat` solves linear integer arithmetic goals.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `lia` solver.
Please use `grind` instead if you need additional capabilities.

**Deprecated**: Use `lia` instead.
-/
syntax (name := cutsat) "cutsat" optConfig : tactic

/--
`lia` solves linear integer arithmetic goals.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `lia` solver.
Please use `grind` instead if you need additional capabilities.
-/
syntax (name := lia) "lia" optConfig : tactic

/--
`grobner` solves goals that can be phrased as polynomial equations (with further polynomial equations as hypotheses)
over commutative (semi)rings, using the Grobner basis algorithm.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `grobner` solver.
Please use `grind` instead if you need additional capabilities.
-/
syntax (name := grobner) "grobner" optConfig : tactic

/-!
Sets symbol priorities for the E-matching pattern inference procedure used in `grind`
-/

-- The following symbols are never used in E-matching patterns
attribute [grind symbol 0] Eq HEq Iff And Or Not ite dite
/-
Remark for `ite` and `dite`: recall the then/else branches
are only internalized after `grind` decided whether the condition is
`True`/`False`. Thus, they **must** not be used a `grind` patterns.
-/

-- The following symbols are only used as the root pattern symbol if there isn't another option
attribute [grind symbol low] HAdd.hAdd HSub.hSub HMul.hMul HSMul.hSMul Dvd.dvd HDiv.hDiv HMod.hMod

-- TODO: improve pattern inference heuristics and reduce priority for LT.lt and LE.le
-- attribute [grind symbol low] LT.lt LE.le
end Lean.Parser.Tactic
