    # Grind Tactic Manual

## 1. Quick Start

* **Availability** – `grind` ships with Lean 4 (no extra installation) and is usable in any Lean file—just write `by grind`. No extra `import` is required beyond what your own definitions already need.

* **Library support** – Lean’s standard library is already annotated with `[grind]` attributes, so common lemmas are discovered automatically. Mathlib will be annotated gradually, starting with its most frequently used theories.

* **First proof**

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  grind
```

This succeeds instantly using congruence closure.

* **Power examples** – showcasing `grind`'s satellite solvers:

  * *Algebraic reasoning* (commutative‑ring solver):

    ```lean
    example [CommRing α] [NoNatZeroDivisors α] (a b c : α)
        : a + b + c = 3 →
          a^2 + b^2 + c^2 = 5 →
          a^3 + b^3 + c^3 = 7 →
          a^4 + b^4 = 9 - c^4 := by
      grind
    ```

  * *Finite‑field style reasoning* (works in `Fin 11`):

    ```lean
    example (x y : Fin 11) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
      grind
    ```

  * *Linear integer arithmetic with case analysis*:

    ```lean
    example (x y : Int) :
        27 ≤ 11*x + 13*y →
        11*x + 13*y ≤ 45 →
        -10 ≤ 7*x - 9*y →
        7*x - 9*y ≤ 4 → False := by
      grind
    ```

* **Useful flags**

  * `by grind (splits := 3) (ematch := 2)` – limit case splits / E‑matching rounds.

## 2. What is `grind`?

A proof‑automation tactic inspired by modern SMT solvers. **Picture a virtual white‑board:** every time `grind` discovers a new equality, inequality, or Boolean literal it writes that fact on the board, merges equivalent terms into buckets, and invites each engine to read from—and add back to—the same workspace. The cooperating engines are: congruence closure, constraint propagation, E‑matching, guided case analysis, and a suite of satellite theory solvers (linear integer arithmetic, commutative rings, …). Lean supports dependent types and a powerful type‑class system, and `grind` produces ordinary Lean proof terms for every fact it adds.

## 3. What `grind` is *not*.

`grind` is *not* designed for goals whose search space explodes combinatorially—think large‑`n` pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards, or a 200‑variable Sudoku encoded as Boolean constraints.  Such encodings require thousands (or millions) of case‑splits that overwhelm `grind`’s branching search.

* **Bit‑level or pure Boolean combinatorial problems** → use **`bv_decide`**.
  `bv_decide` calls a state‑of‑the‑art SAT solver (e.g. CaDiCaL or Kissat) and then returns a *compact, machine‑checkable certificate*.  All heavy search happens outside Lean; the certificate is replayed and verified inside Lean, so trust is preserved (verification time scales with certificate size).
* **Full SMT problems that need substantial case analysis across multiple theories** (arrays, bit‑vectors, rich arithmetic, quantifiers, …) → use the forthcoming **`lean‑smt`** tactic—a tight Lean front‑end for CVC5 that replays unsat cores or models inside Lean.

## 4. Congruence Closure

### 4.1  What is congruence closure?

Congruence closure maintains **equivalence classes of terms** under the reflexive–symmetric–transitive closure of "is equal to" *and* the rule that equal arguments yield equal function results.  Formally, if `a = a'` and `b = b'`, then `f a b = f a' b'` is added.  The algorithm merges classes until a fixed point is reached.

Think of a **shared white‑board**:

1. Every hypothesis `h : t₁ = t₂` writes a line connecting `t₁` and `t₂`.
2. Each merge paints both terms the same color.  Soon whole constellations (`f a`, `g (f a)`, …) share the color.
3. If `True` and `False` ever land in the same color—or likewise two different constructors of the **same inductive type** such as `none` and `some 1`—the goal is closed by contradiction.

### 4.2  How it differs from `simp`

* `simp` **rewrites** a goal, replacing occurrences of `t₁` with `t₂` as soon as it sees `h : t₁ = t₂`.  The rewrite is directional and destructive.
* `grind` **accumulates** equalities bidirectionally.  No term is rewritten; instead, both representatives live in the same class.  All other engines (E‑matching, theory solvers, propagation) can query these classes and add new facts, then the closure updates incrementally.

This makes congruence closure especially robust in the presence of symmetrical reasoning, mutual recursion, and large nestings of constructors where rewriting would duplicate work.

### 4.3  Minimal examples

```lean
example {α} (f g : α → α) (x y : α) (h₁ : x = y) (h₂ : f y = g y) : f x = g x := by
  -- After h₁, x and y share a class; h₂ adds f y = g y; closure bridges to f x = g x
  grind

example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  -- Pair constructor obeys congruence, so once a = b the tuples are equal
  grind
```

### 4.4  Debugging tip

When `grind` *fails* it prints the remaining subgoal **followed by all equivalence classes**.  The two largest classes are shown as **True propositions** and **False propositions**, listing every literal currently known to be provable or refutable.  Inspect these lists to spot missing facts or contradictory assumptions.

## 5. Constraint Propagation

Constraint propagation works on the **True** and **False** buckets of the white‑board.  Whenever a literal is added to one of those buckets, `grind` fires dozens of small *forward rules* to push its logical consequences:

* Boolean connectives — e.g. if `A` is **True**, mark `A ∨ B` **True**; if `A ∧ B` is **True**, mark both `A` and `B` **True**; if `A ∧ B` is **False**, at least one of `A`, `B` becomes **False**.
* Inductive datatypes — two different constructors (`none` vs `some _`) collapsing into the same class yield contradiction; equal tuples yield equal components.
* Projections and casts — from `h : (x, y) = (x', y')` we derive `x = x'` and `y = y'`; any term `cast h a` is merged with `a` immediately (using a heterogeneous equality) so both live in the same class.
* Structural eta and definitional equalities — `⟨a, b⟩.1` propagates to `a`, etc.

Below is a **representative slice** of the propagators so you can see the style they follow.  Each follows the same skeleton: inspect the truth‑value of sub‑expressions, push equalities (`pushEq`) or truth‑values (`pushEqTrue` / `pushEqFalse`), and optionally close the goal if a contradiction (`closeGoal`) arises.  A few high‑signal examples:

```lean
/-- Propagate equalities *upwards* for conjunctions. -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <| mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left) a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    pushEq e a <| mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right) a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    pushEqFalse e <| mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left) a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    pushEqFalse e <| mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right) a b (← mkEqFalseProof b)

/-- Truth flows *down* when the whole `And` is proven `True`. -/
builtin_grind_propagator propagateAndDown ↓And := fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    pushEqTrue a <| mkApp3 (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    pushEqTrue b <| mkApp3 (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```

Other frequently‑triggered propagators follow the same pattern:

| Propagator                            | Handles                         | Notes                                          |
| ------------------------------------- | ------------------------------- | ---------------------------------------------- |
| `propagateOrUp` / `propagateOrDown`   | `a ∨ b`                         | True/False pushes for disjunctions             |
| `propagateNotUp` / `propagateNotDown` | `¬ a`                           | Links `¬ a` with the Boolean of `a`            |
| `propagateEqUp` / `propagateEqDown`   | `a = b`                         | Bridges Booleans, detects constructor clash    |
| `propagateIte` / `propagateDIte`      | `ite` / `dite`                  | Replaces chosen branch once condition is fixed |
| `propagateEtaStruct`                  | structures tagged `[grind ext]` | Generates η‑expansion `a = ⟨a.1, …⟩`           |

Many specialised variants for `Bool` mirror these rules exactly (e.g. `propagateBoolAndUp`).

#### 5.5  Propagation‑only examples

These goals are closed *purely* by constraint propagation—no case splits, no theory solvers:

```lean
-- Boolean connective: a && !a is always false.
example (a : Bool) : (a && !a) = false := by
  grind

-- Conditional (ite): once the condition is true, ite picks the 'then' branch.
example (c : Bool) (t e : Nat) (h : c = true) : (if c then t else e) = t := by
  grind

-- Negation propagates truth downwards.
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```

These snippets run instantly because the relevant propagators (`propagateBoolAndUp`, `propagateIte`, `propagateBoolNotDown`) fire as soon as the hypotheses are internalised.

> **Note**  If you toggle `set_option trace.grind.eqc true`, `grind` will print a line every time two equivalence classes merge—handy for seeing propagation in action.

**Implementation tip**  `grind` is still under active development. Until the API has stabilised we recommend **refraining from custom elaborators or satellite solvers**. If you really need a project‑local propagator, use the user‑facing `grind_propagator` command rather than `builtin_grind_propagator` (the latter is reserved for Lean’s own code). When adding new propagators keep them *small and orthogonal*—they should fire in ≤1 µs and either push one fact or close the goal. This keeps the propagation phase predictable and easy to debug.

We continuously expand and refine the rule set—expect the **Info View** to show increasingly rich `True`/`False` buckets over time. The full equivalence classes are displayed automatically **only when `grind` fails**, and only for the first subgoal it could not close—use this output to inspect missing facts and understand why the subgoal remains open.

## 6. Case Analysis

### 6.1  Selection heuristics

`grind` decides which sub‑term to split on by combining three sources of signal:

1. **Structural flags** — quick booleans that enable whole syntactic classes:

   * `splitIte`  (default **true**) → split every `if … then … else …` term.
   * `splitMatch` (default **true**)→ split on all `match` expressions (the `grind` analogue of Lean’s `split` tactic, just like `splitIte`).
   * `splitImp`  (default **false**) → when `true` splits on any hypothesis `A → B` whose antecedent `A` is **propositional**.  Arithmetic antecedents are special‑cased: if `A` is an arithmetic literal (`≤`, `=`, `¬`, `Dvd`, …) `grind` will split **even when `splitImp := false`** so the integer solver can propagate facts.

👉 Shorthand toggles: `by grind -splitIte +splitImp` expands to `by grind (splitIte := false) (splitImp := true)`.
2\. **Global limit** — `splits := n` caps the *depth* of the search tree.  Once a branch performs `n` splits `grind` stops splitting further in that branch; if the branch cannot be closed it reports that the split threshold has been reached.
3\. **Manual annotations** — you may mark *any* inductive predicate or structure with

```lean
attribute [grind cases] Even Sorted
```

and `grind` will treat every instance of that predicate as a split candidate.

### 6.2  Examples

```lean
-- splitIte demonstration
example (c : Bool) (x y : Nat) (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind

example (c : Bool) (x y : Nat) (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  -- The following tactic fails because we need one case split
  fail_if_success grind (splits := 0)
  grind (splits := 1)

-- User‑defined predicate with [grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n+2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  -- With the attribute, grind immediately splits on the Even hypothesis
  grind

example (h : Even (n + 2)) : Even n := by
  grind

example (h : y = match x with | 0 => 1 | _ => 2) : y > 0 := by
  -- `grind` fails if we disable `splitMatch`
  fail_if_success grind -splitMatch
  grind
```

### 6.3  Tips

* Increase `splits` *only* when the goal genuinely needs deeper branching; each extra level multiplies the search space.
* Disable `splitMatch` when large pattern‑matching definitions explode the tree.
* You can combine flags: `by grind -splitMatch (splits := 10) +splitImp`.
* The `[grind cases]` attribute is *scoped*; you can use the modifiers `local`/`scoped` if you only want extra splits inside a section or namespace.

## 7. E‑matching

TBD
Pattern annotations (`[grind =]`, `[grind →]`, …), anti‑patterns, local vs global attributes, debugging with the attribute `[grind?]`. Flags: `ematch`, `instances`, `matchEqs`.

## 8. Linear Integer Arithmetic Solver
TBD
Model‑building CutSAT‑style procedure, model‑based theory combination. Flags: `+qlia`, `-mbtc`.

## 9. Algebraic Solver (Commutative Rings, Fields)
TBD
Grobner‑style basis construction, class parameters (`IsCharP`, `NoNatZeroDivisors`), step budget `algSteps`.

## 10. Normalizer / Pre‑processor
TBD
Canonicalization pass; extending with `[grind norm]` (expert only).

## 11. Diagnostics
TBD
Threshold notices, learned equivalence classes, integer assignments, algebraic basis, performed splits, instance statistics.

## 12. Troubleshooting & FAQ
TBD

## 13. Bigger Examples
TBD
