# Quasi-Quoted `Expr` Patterns (`expr` Quotations)

`expr` quotations provide native syntax `` `(expr[rel]| p) `` for matching, destructuring,
inspecting, and building Lean `Expr` values directly inside Lean expressions and tactics.

For internal module layout and architectural design rationale, see
[expr_quot_adr.md](expr_quot_adr.md).

## Surface Syntax and Defaults

An `expr` quotation has the form `` `(expr[/engine] [[±items]] [±flags]| body) ``:

- **No whitespace before `expr`**: write `` `(expr| ...) `` with no space between `` `( `` and
  `expr`. Because `expr` is a non-reserved keyword parsed after `` `( ``, identifiers such as
  `expr` remain usable in ordinary code, and dynamic quotations such as `` `(exprFoo| ...) ``
  continue to parse normally.
- **Pattern vs. term default relation**:
  - In **pattern positions** (`match`, `fun |`, `if let`, `let ... |`, `do match`, `for case`),
    the default engine is `/structural`.
  - In **term positions** (evaluating `` `(expr| t) `` to build an `Expr`), the default engine is
    `/defeq` (used to check `$e` splice types).

## Matching Relations, Flags, and `[items]`

Each `` `(expr[rel]| ...) `` quotation accepts an optional `/engine`, an optional `[±item, ...]`
unfold override list, and zero or more `±flag` overrides (`inst`, `beta`, `zeta`, `proj`, `eta`):

| Engine | Default `inst` | Default `beta`/`zeta`/`proj`/`eta` | Semantics |
|---|---|---|---|
| `structural` (default) | `false` | all `false` | Syntactic modulo `mdata`, head mvars, proofs |
| `reducible` | `true` | all `true` | `Meta.isDefEq` at `.reducible` |
| `instances` | `true` | all `true` | `Meta.isDefEq` at `.instances` |
| `defeq` (term default) | `true` | all `true` | `Meta.isDefEq` at `.default` |
| `sym` | `true` | all `true` | `Sym` modulo `beta`/`eta`/`let`/`zetaDelta`/projs/offsets |

### Flags and `[items]`

- **`+inst` in `/structural`**: keeps matching strictly structural on ordinary subterms while
  checking instance-implicit arguments by definitional equality at `.instances` transparency.
- **`[±decl, ±simpSet, ±$x]`**: rules apply left-to-right (**last wins**). Removing an unfold
  rule (`-c` or `-simp`) when neither the base engine nor an earlier `+` item unfolds it is a
  static error (or a runtime error for local `-$x`). Local `$x` (or `$(e)`) items must evaluate
  to a free variable referring to a dependent `let` declaration in the current `LocalContext`
  (non-dependent `have` declarations and ordinary hypotheses cannot be unfolded).
- **`/sym` restrictions**: `/sym` requires a `[MonadSym m]` monad (such as `SymM`, `GrindM`,
  `GoalM`, `Sym.Simp.SimpM`, `Sym.DSimp.DSimpM`, or `GrindTacticM` inside `sym =>` tactics). It
  rejects `[items]`, local `$x` items, and disabling `-inst`/`-beta`/`-zeta`/`-proj`/`-eta`.

### User-Observable Semantics

- **`let` look-through and re-wrapping**:
  - `/structural +zeta` performs faithful non-substituting `let` look-through: any captured
    subterm mentioning looked-through `let` variables is re-wrapped with only the dependent `let`
    bindings it actually needs, unless a direct local free variable already exists.
  - In `isDefEq`-based engines (`/reducible`, `/instances`, `/defeq`), outer or inspected `let`
    bindings independent of pattern binders are lifted and re-wrapped when possible. When a `let`
    value depends on a pattern binder (or fallback `zeta` unfolding is required), `Meta.isDefEq`
    substitutes the `let` and captured subterms may be in `isDefEq`-normalized form.
- **Lazy metavariables under `/structural`**: `/structural` resolves assigned metavariables at
  inspected heads without eagerly traversing uninspected subtrees. If your match arm inspects
  captured subterms structurally and expects nested assigned metavariables to be resolved, call
  `instantiateMVars` on the capture.
- **`/sym` numeral and offset matching**: in `/sym`, a raw numeral pattern such as
  `` `(expr/sym| 5) `` matches numeral `5` (and reducible equivalents like `1 + 4`), whereas
  `` `(expr/sym| Nat.succ ?n) `` or `` `(expr/sym| (?n : Nat) + 1) `` uses `Sym`'s offset
  representation to decompose numeral literals such as `5` into `n := 4`. Matching under `/sym`
  rejects unresolved instance constraints and never leaks temporary metavariables into the
  caller's `MetavarContext`.
- **Automatic discrimination-tree indexing**: consecutive single-slot match arms on the same
  column sharing `/structural` (with or without `+inst`, and no `[items]` or reduction flags),
  `/reducible` (with default reduction flags), or `/sym` — without local `$x` overrides — are
  automatically indexed in exact source order.

## Pattern Bindings, Native Control Flow, and Term Building

### Pattern Binders, Pins, and Wildcards

- **Binders (`?x`)**: `?x` binds a local variable `x : Expr` on its first occurrence.
- **Higher-order patterns (`?P x y`)**: applying a pattern variable to distinct bound variables
  captures a lambda abstraction (for example, `?P : Nat → Nat` in `` `(expr| ∀ x : Nat, ?P x) ``).
- **Pins (`$e` and nonlinear `$x`)**: `$e` (or `$(e)`) pins an in-scope `Expr` value evaluated
  in the enclosing context. Writing `$x` after an earlier `?x` in the same pattern creates a
  nonlinear self-pin requiring both positions to match modulo the pattern's relation.
- **Wildcards (`_` / `?_`)**: match any subterm without binding a variable; multiple `_`
  wildcards in one pattern are independent and never unify distinct subterms.

### Native Control Flow

`expr` quotations work directly inside Lean's native pattern-matching constructs:

- `match`, `fun |`, `if let`, `let ... |`, and `do match`, including multi-column and nested
  matches mixing ordinary constructors (e.g. `Option`, `Prod`) with `` `(expr| ...) `` patterns.
- `match (modulo := rel) ...` (both term-mode and `do`-mode): sets a default relation for every
  `` `(expr| ...) `` pattern in the match. A per-pattern `/engine` replaces `(modulo := rel)`
  completely, while per-pattern `[items]` and `±flags` extend it.
- `for case pat in src do ...` (and `for case h : pat in src` / `for h : case pat in src`):
  iterates over `src` and skips elements that do not match `pat` via `continue`. Writing
  `for case` with an irrefutable pattern is reported as a redundant alternative.
- **Why `match h : e` is rejected**: equality proof binders `h : discr` are rejected on any
  discriminant column matched with `expr` quotations because matched `Expr`s need only satisfy
  the chosen matching relation, not propositional equality.

### Term Construction (`` `(expr[rel]| t) ``)

In term position, `` `(expr[rel]| t) `` elaborates into `MetaM Expr` (or `m Expr` with
`[MonadSym m]` for `/sym`):

- Preserves `let` and `fun` structure without unwanted beta-reduction (e.g. `$f $x` stays an
  application even if `f` is a lambda).
- Preserves caller pointer sharing and leaves caller metavariables inside `$e` splices
  unassigned. Under `/sym`, results are maximally shared with kernel projections folded.
- Checks `$e` splice types against expected types under `rel` (default `/defeq`) and synthesizes
  splice-dependent type-class instances at runtime.
- Turns `?h` and `?_` into fresh `.syntheticOpaque` metavariables in the caller's context on
  each evaluation (repeated `?h` within one quotation shares one metavariable; each `?_` is
  distinct).
- **Type-annotation performance tip**: annotating splice types concretely (for example,
  `($a : Nat) + 1` instead of untyped `$a + 1`) resolves type-class instances statically at
  compile time instead of running runtime instance synthesis on every template evaluation.
- **Outer elaboration scope for splices**: `$e` splices are elaborated in the **enclosing**
  `TermElabM` context, outside the quotation's own elaborator, macro scopes, and numeral
  defaulting context.

## Sources and Goal/Context Primitives

- **`localHypTypes (reverse := false) (except := [])`**: yields non-implementation-detail
  `(hyp, type)` pairs from the current local context (oldest first by default) with assigned
  metavariables instantiated in `type`.
- **`localHypDecls (reverse := false) (except := [])`**: yields `(hyp, type, val?)` triples from
  the current local context; `val?` is `some v` only for dependent `let` declarations (`have`
  declarations yield `none`), with metavariables instantiated in `type` and `val`.
- **`firstHyp` / `firstHyp?` (`TacticM`) and `MVarId.firstHyp` / `MVarId.firstHyp?` (`MetaM` /
  `MonadBacktrack`)**: try `f h ty` across `localHypTypes` (`reverse := true` newest first by
  default), enter the goal's local context automatically, and roll back state atomically on
  failure without admitting `sorry` or leaking diagnostics (`firstHyp` throws
  `"firstHyp: no hypothesis matched"` if no hypothesis succeeds).
- **`subterms e (dedup := true) (includeAppPrefixes := false)` + `ExprContext.fill`**: lazy
  outermost-first stream of closed `(subterm, ctx)` pairs. With `dedup := true` (default),
  structurally equal subterms are visited once along their first context path; set
  `dedup := false` to visit every occurrence with its own `ExprContext`. `ctx.fill e'`
  substitutes `e'` into the hole while preserving unchanged subtrees. Note that `subterms`
  traverses `e` syntactically without calling `instantiateMVars`.
- **`matchDiscriminants e (alsoCasesOn := false) (dedup := true)`**: lazy outermost-first
  stream of closed `match` (and optionally `casesOn`) discriminants paired with `ExprContext`.
  Unlike `subterms`, `matchDiscriminants` instantiates assigned metavariables first.

## Idioms for Porting Rocq `match goal` Tactics

- **Backtracking hypothesis search**: use `firstHyp` (`TacticM`) or `goal.firstHyp` (`MetaM` /
  `MonadBacktrack`) when an arm may mutate the goal before failing (such as `specialize` or
  recursive search). Its `reverse := true` default matches Rocq's newest-first order; handle
  multi-hypothesis patterns by nesting `except` and pinning shared terms with `$P`:
  ```lean
  firstHyp fun h1 ty1 => do
    let `(expr/reducible| (?P : Prop) → _) := ty1 | failure
    firstHyp (except := [h1]) fun h2 ty2 => do
      let `(expr/reducible| $P) := ty2 | failure
      ...
  ```
- **Contextual `change` and `rewrite`**: match a target subterm and its `ExprContext` via
  ``for case (`(expr| pat), ctx) in subterms ...`` and apply contextual `change` with
  `goal.replaceTargetDefEq (ctx.fill e')`. For contextual `rewrite`, pass an equality `eq`
  directly to `goal.rewrite (← goal.getType) eq` (followed by `goal.replaceTargetEq`);
  `kabstract` handles dependent occurrences (such as `Decidable` instances in `ite`) cleanly
  without fragile path-to-occurrence mapping.
- **Direct `MVarId` steps over `Syntax` round-tripping**: drive tactics from `FVarId`/`Expr`
  using `goal.assign`, `goal.cases`, `goal.clear`, `goal.note`, and `replaceMainGoal` rather
  than quoting tactic syntax with `Term.exprToSyntax`, which breaks on inaccessible `h✝` names
  or stale contexts. When tactic syntax is unavoidable (such as `generalize ... at *`), call
  `Term.exprToSyntax` inside `withMainContext`.
- **Context and metavariable hygiene**: `firstHyp` and `MVarId.firstHyp` enter the goal's
  context automatically; when calling `localHypTypes` or `localHypDecls` directly in `TacticM`,
  wrap the block in `withMainContext`. `getMainTarget` and `localHypTypes` instantiate
  metavariables, whereas `subterms` traverses syntactically (call `instantiateMVars` first on
  `MVarId.getType` or `inferType` results).
- **Filtering `match` discriminants**: Lean's compiled `match` expressions often carry
  generalized index discriminants alongside the value being split; filter `matchDiscriminants`
  with a typed pattern such as `` `(expr/reducible| (?x : MyType)) ``.

## Diagnostics

- **``#check_pattern `(expr[rel]| p)``**: elaborates only the pattern path (never evaluating a
  term template) and prints the resolved relation/flags/items, binders and higher-order arities,
  pins, wildcards and unresolved implicits, fixed vs. polymorphic instances, universe
  parameters, closed proof entries, and discrimination-tree indexing eligibility and keys.
- **`trace.Meta.Match.expr`**: zero-overhead when disabled; when enabled, reports indexed
  candidates tried, match hits, and the first mismatch subterm `(pattern vs scrutinee)` across
  all engines.
- **Error hints and linters**:
  - Repeated `?x` in a pattern suggests `$x`; an unbound `$x` identifier pin suggests `?x`.
  - `linter.exprQuot.numeralDefaulting` (default `true`): warns when a pattern numeral relies
    on `OfNat` defaulting to `Nat` and suggests adding a type annotation such as `(0 : Nat)`.
  - `linter.exprQuot.syntaxHole` (default `true`): warns on named `?x` inside ordinary syntax
    quotations in `Expr`-typed match patterns or `Expr`/`m Expr`-typed term positions (never
    `?_` or `Syntax`/`TSyntax` quotations).
