# Quasi-Quoted `Expr` Patterns (`expr` Quotations)

`expr` quotations provide native syntax `` `(expr[rel]| p) `` for matching, destructuring,
inspecting, and building Lean `Expr` values directly inside Lean expressions and tactics.

## Architecture and Modules

- **`Lean.Meta.ExprPattern`** (`src/Lean/Meta/ExprPattern.lean`):
  Runtime representation and matching/building core:
  - Relation configuration: `ExprMatchEngine` (`structural`, `reducible`, `instances`,
    `defeq`, `sym`), `ExprMatchItem`, `ExprMatchFlags`, `ExprMatchRel`,
    `ResolvedExprMatchRel`, static resolution caching (`ExprMatchRel.resolveStaticCached`),
    and dynamic local `$x` validation (`ResolvedExprMatchRel.withLocalItems`).
  - Compiled representations: `ExprPattern` and `ExprTemplate` with per-pattern precomputation
    (`captureVars` wildcard elision, `closedProofs` closed proof types, `patLevelNodes`
    universe-parameter node index).
  - Dispatchers: linear CPS combinators (`matchOrElse`, `matchSiteOrElse`,
    `matchResolvedOrElse`, `matchSymSiteOrElse`, `matchSymResolvedOrElse`), shared-relation
    `DiscrTree` dispatchers (`matchIndexedOrElse`, `matchSymIndexedOrElse`), and `MonadSym`.
  - Context and sources: `ExprContext` (`ExprContext.fill`), `localHypTypes`,
    `localHypDecls`, `MVarId.firstHyp?`, `MVarId.firstHyp`, `subterms`, and
    `matchDiscriminants`.
- **`Lean.Elab.ExprQuot`** (`src/Lean/Elab/ExprQuot.lean`):
  Front-end preprocessing (`?x` binders, higher-order `?P x y`, `$e` pins/splices, `_`/`?_`
  wildcards), elaboration into deduplicated `(siteId, ExprPattern.decode ...)` /
  `ExprTemplate.decode ...` expressions (`exprPatExt`, `exprPatArrExt`, `exprTmplExt`) hoisted
  into shared closed terms by LCNF `ExtractClosed` (`ClosedTermCache`), `(modulo := rel)` macro
  expansion, native `match` compilation (`compileExprMatch`), `for case` support, and diagnostics
  (`#check_pattern`, `checkSyntaxHoleInExprMatchPatterns`, `numeralDefaulting` lint).
- **`Lean.Elab.Tactic.FirstHyp`** (`src/Lean/Elab/Tactic/FirstHyp.lean`):
  Defines `firstHyp?` and `firstHyp` for backtracking hypothesis search over the main goal with
  atomic state rollback and no `sorry` leakage on failing branches.
- **`Lean.Elab.Tactic.Grind.Sym`** (`src/Lean/Elab/Tactic/Grind/Sym.lean`):
  Defines the low-priority `MonadSym GrindTacticM` instance so `` `(expr/sym| ...) `` works
  directly inside `sym =>` tactics. Note: `Grind/Sym.lean` uses
  `public import Lean.Elab.Tactic.Grind.Basic` so `Grind.Basic` requires no edits and avoids
  cyclic dependencies (`#synth MonadLiftT MetaM GrindTacticM` continues routing through
  `TermElabM`).
- **Diagnostics hooks**:
  - `src/Lean/Linter/Init.lean`: `linter.exprQuot.syntaxHole` and
    `linter.exprQuot.numeralDefaulting` (both `defValue := true`).
  - `src/Lean/Elab/Quotation/Util.lean`, `Quotation.lean`, `Match.lean`,
    `BuiltinDo/Match.lean`: strictly scoped `syntaxHole` lint triggers.
  - `src/Lean/Parser/Command.lean` & `src/Lean/Elab/ExprQuotCommand.lean`: `#check_pattern`.

## Matching Relations, Flags, and `[items]`

Each `` `(expr[rel]| ...) `` quotation accepts an optional `/engine`, `[items]`, and `±flags`:

| Engine | Default `inst` | Default `beta`/`zeta`/`proj`/`eta` | Semantics |
|---|---|---|---|
| `structural` (default) | `false` | all `false` | Syntactic modulo `mdata`, head mvars, proofs |
| `reducible` | `true` | all `true` | `Meta.isDefEq` at `.reducible` |
| `instances` | `true` | all `true` | `Meta.isDefEq` at `.instances` |
| `defeq` (term default) | `true` | all `true` | `Meta.isDefEq` at `.default` |
| `sym` | `true` | Sym rules | Structural + `beta`/`eta`/`let`/`zetaDelta`/projs/offsets |

Flags and `[items]` details:
- **`+inst`** in `structural`: keeps structural matching on ordinary subterms while checking
  instance-implicit arguments by `Meta.isDefEq` at `.instances`.
- **`[±decl, ±simpSet, ±$x]`**: rules apply left-to-right (`last wins`). Removing an unfold
  rule (`-c` or `-simp`) when neither the base engine nor an earlier `+` item unfolds it is a
  static error (or runtime error for local `-$x`). Local `$x` items must refer to dependent
  `let` declarations in the current `LocalContext`.
- **Lazy look-through and `let`-rewrapping**:
  - `/structural +zeta` performs faithful non-substituting `let` look-through: any captured
    subterm mentioning looked-through `let` variables is re-wrapped with only the dependent
    `let` bindings needed (`rewrapLets`), unless a direct local fvar already exists.
  - In `isDefEq` engines (`/reducible`, `/instances`, `/defeq`), `liftInspectedLetsGo` lifts
    and re-wraps outer or inspected `let` expressions when independent of pattern binders, but
    falls back to `Meta.isDefEq` `let`-substitution when a `let` value depends on a pattern
    binder (and captures may be in `isDefEq`-normalized form).
- **Performance fast paths**:
  - `PatHeadGuard` (`fastRejectStructural`) performs an `O(1)` head+arity fast-reject before
    state allocation in `/structural` matching when tracing is disabled.
  - Pattern variables that are unnamed wildcards occurring once (`captureVars[k] = false`) are
    never materialized on empty/closed captures.
  - Closed subterms compare syntactically (`pe == e`, including pointer equality) **before**
    falling back to `isProof` / type comparison via precomputed `closedProofs`.
  - `.const` and `.sort` universe levels are checked structurally and unified consistently
    across repeated `levelParams` occurrences (`patLevelNodes`).
  - Compiled `ExprPattern` and `ExprTemplate` values serialize into compact lossless 6-bit ASCII
    DAG strings (`ExprPattern.encode`/`decode`, `ExprTemplate.encode`/`decode`) so LCNF
    `ExtractClosed`/`ClosedTermCache` hoists and deduplicates them cleanly inside the enclosing
    declaration without extra `addAndCompile` auxiliary declarations.
  - Pins (`$e`) pre-seed `σ` directly without rebuilding `lam` per match, and static relations
    cache resolved `[items]` per call site (`siteId`).
- **`/sym` engine notes**:
  - `/sym` requires `[MonadSym m]` (`SymM` or `GrindTacticM`), rejects `[items]`, local
    `$x` items, and disabling `-inst`/`-beta`/`-zeta`/`-proj`/`-eta`.
  - Compiled `Sym.Pattern` values (built via `Sym.mkPatternFromLambda`) and closed templates
    (`Sym.shareCommon` + `Sym.instantiateRevS`) are cached per quotation site in
    `Sym.SymExtension`. Fresh temporary metavariables and unresolved instances fail cleanly.

## Indexing (`DiscrTree`) vs Linear Fallback

When consecutive single-slot match alternatives share the same index-sound relation without
local `$x` unfold items (`ExprMatchRel.isIndexSound`), `compileExprMatch` emits an indexed
dispatcher (`matchIndexedOrElse` or `matchSymIndexedOrElse`) preserving exact ascending source
order and single-evaluation deduplication:
- **`.structural` / `.structural +inst`**: builds a `DiscrTree` using structural head keys
  (skipping `[instImplicit]` args as `*` when `+inst` is active). Lookup uses lazy head-only
  mvar resolution (`resolveHeadMVarPure`) — never full-scrutinee `instantiateMVars`, keeping
  non-matching deep spines with unassigned metavariables `O(|pattern|)`.
- **`.reducible`**: uses `Meta.DiscrTree` with reducible normalization and a `Nat` literal
  fallback (`reduceToNatLit?`).
- **`.sym`**: uses `Sym.Simp.DiscrTree` modulo `letE`, `zetaDelta`, `beta`, `eta`, and offsets.
  Note on `Nat` patterns: in `/sym`, a raw numeral pattern such as `` `(expr/sym| 5) `` lowers
  to `OfNat.ofNat ... 5` or `.lit 5` matching numeral `5` (and reducible equivalents like
  `1 + 4` via `Sym` structural comparison when keys permit), whereas `` `(expr/sym| Nat.succ ?n) ``
  or `` `(expr/sym| (?n : Nat) + 1) `` uses `Sym`'s offset representation (`*` at root in the
  index) to decompose raw numeral literals such as `5` into `n := 4`.

## Pattern Bindings, Term Building, and Sources

- **Pattern binders and pins**: `?x` binds the first occurrence, `?P x y` binds higher-order
  abstractions (`?P : Nat → Nat` when applied to distinct bound variables), `$e` pins an
  in-scope `Expr` (and `$x` after `?x` creates a nonlinear self-pin). Wildcards `_`/`?_` do not
  bind variables, so multiple `_`s never unify distinct subterms.
- **Native control flow**: works in `match`, `fun |`, `if let`, `let ... |`, `do match`,
  `match (modulo := rel)`, and `for case pat in src` (which skips non-matching elements). Note
  that `match h : e` on quotation patterns is rejected because matched `Expr`s need only satisfy
  the chosen relation, not propositional equality.
- **Term building (`` `(expr[rel]| t) ``)**: preserves `let`/`fun` structure without unwanted
  beta-reduction, checks `$e` splice types under `rel`, synthesizes dependent type-class
  instances at runtime (`inspectClassGoalInputs?`), and turns `?h`/`?_` into fresh
  `.syntheticOpaque` metavariables.
  - Type annotation perf hint: writing concrete types on splices (`($a : Nat)` instead of
    untyped `$a + 1`) resolves instances statically at compile time instead of running
    runtime type-class synthesis on every template instantiation.
  - Outer macro expansion depth note: `$e` splices (e.g., inside `mkConst` / macro-generated
    terms) are elaborated in the **enclosing** `TermElabM` context, outside the quotation's
    pattern elaborator and numeral-defaulting context.
- **Sources and `ExprContext`**:
  - `localHypTypes (reverse := false) (except := [])`: yields non-implDetail hypotheses in the
    local context (oldest first by default) with metavariables instantiated.
  - `localHypDecls (reverse := false) (except := [])`: also includes dependent `let` values.
  - `firstHyp` / `firstHyp?` (`TacticM`) and `MVarId.firstHyp` / `MVarId.firstHyp?` (`MetaM` /
    `MonadBacktrack`): try `f h ty` across `localHypTypes` (`reverse := true` newest first by
    default), entering the goal's local context automatically and rolling back state atomically on
    failure (`firstHyp` throws `"firstHyp: no hypothesis matched"` when none succeeds).
  - `subterms e (dedup := true)` and `matchDiscriminants e`: yield closed subterms outermost
    first, each paired with an `ExprContext`. Because `dedup := true` by default, shared DAG
    subterms are visited once along their first context path. `ExprContext.fill` substitutes a
    replacement expression back into the hole while preserving unchanged subtrees. Note that
    `subterms` traverses `e` syntactically without calling `instantiateMVars`, while
    `matchDiscriminants` instantiates metavariables first.

## Idioms for Porting Rocq `match goal` Tactics

- **Backtracking hypothesis search**: Use `firstHyp` (`TacticM`) or `goal.firstHyp` (`MetaM` /
  `MonadBacktrack`) when an arm may mutate the goal before failing (e.g. `specialize` or recursive
  search). Its `reverse := true` default matches Rocq's newest-first order; handle multi-hypothesis
  patterns by nesting `except` and pinning shared terms with `$P`:
  ```lean
  firstHyp fun h1 ty1 => do
    let `(expr/reducible| (?P : Prop) → _) := ty1 | failure
    firstHyp (except := [h1]) fun h2 ty2 => do
      let `(expr/reducible| $P) := ty2 | failure
      ...
  ```
- **Contextual `change` and `rewrite`**: Match a target subterm and its `ExprContext` via
  ``for case (`(expr| pat), ctx) in subterms ...`` and apply contextual `change` with
  `goal.replaceTargetDefEq (ctx.fill e')`. For contextual `rewrite`, pass an equality `eq` directly
  to `goal.rewrite (← goal.getType) eq` (followed by `goal.replaceTargetEq`); `kabstract` handles
  dependent occurrences (such as `Decidable` instances in `ite`) cleanly without fragile
  path-to-occurrence mapping.
- **Direct `MVarId` steps over `Syntax` round-tripping**: Drive tactics from `FVarId`/`Expr` using
  `goal.assign`, `goal.cases`, `goal.clear`, `goal.note`, and `replaceMainGoal` rather than
  quoting tactic syntax with `Term.exprToSyntax`, which breaks on inaccessible `h✝` names or stale
  contexts. When tactic syntax is unavoidable (e.g. `generalize ... at *`), call
  `Term.exprToSyntax` inside `withMainContext`.
- **Context and metavariable hygiene**: `firstHyp` and `MVarId.firstHyp` enter the goal's context
  automatically; when calling `localHypTypes` or `localHypDecls` directly in `TacticM`, wrap the
  block in `withMainContext`. `getMainTarget` and `localHypTypes` instantiate metavariables,
  whereas `subterms` traverses syntactically (call `instantiateMVars` first on `MVarId.getType`
  or `inferType` results).
- **Filtering `match` discriminants**: Lean's compiled `match`es often carry generalized index
  discriminants alongside the value being split; filter `matchDiscriminants` with a typed pattern
  such as `` `(expr/reducible| (?x : MyType)) ``.

## Diagnostics

- **`#check_pattern `(expr[rel]| p)`**: elaborates only the pattern path (never evaluating a
  template) and prints relation/flags/items, binders and higher-order arities, pins,
  wildcards/unresolved implicits, fixed vs pattern-bound instances, universe parameters, closed
  proof fast-path entries, and `DiscrTree` indexing eligibility/keys.
- **`trace.Meta.Match.expr`**: zero-overhead when disabled; when enabled, reports candidates
  tried, match hits, and the first mismatch subterm `(pattern vs scrutinee)` across all engines.
- **Errors and linters**:
  - Repeated `?x` suggests `$x`; unbound `$x` suggests `?x`.
  - `linter.exprQuot.numeralDefaulting` (default `true`): warns when a pattern numeral
    relies on `OfNat` defaulting to `Nat`.
  - `linter.exprQuot.syntaxHole` (default `true`): warns on named `?x` inside ordinary syntax
    quotations only in `Expr`-typed match patterns or `Expr`/`m Expr`-typed term positions
    (never `?_` or `Syntax`/`TSyntax` quotations).
