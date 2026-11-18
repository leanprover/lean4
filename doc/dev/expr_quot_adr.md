# Architectural Decision Records: `expr` Quotations

This document records the internal module map and architectural decisions behind Lean's
quasi-quoted `Expr` pattern and term-building subsystem (`` `(expr[rel]| ...) ``). For
user-facing syntax, semantics, and porting idioms, see [expr_quot.md](expr_quot.md).

## Internal Module and Extension Map

- **`Lean.Meta.ExprPattern`** (`src/Lean/Meta/ExprPattern.lean`):
  Runtime representation, matching engines, template instantiation, indexing, and sources:
  - Relations and site caching: `ExprMatchEngine`, `ExprMatchItem`, `ExprMatchFlags`,
    `ResolvedExprMatchFlags`, `ExprMatchRel`, `ResolvedExprMatchRel`, `resolvedRelCacheRef`
    (`ExprMatchRel.resolveStaticCached`), `ResolvedExprMatchRel.withLocalItems`.
  - Patterns and engines: `ExprPattern`, `PatHeadGuard`, `ExprPattern.compile`, `matchStructural?`,
    `matchDefEq?`, `MonadSym`, `matchSymCore?`, CPS dispatchers (`matchOrElse`, `matchSiteOrElse`,
    `matchResolvedOrElse`, `matchSymSiteOrElse`, `matchSymResolvedOrElse`), and `DiscrTree`
    dispatchers (`matchIndexedOrElse`, `matchSymIndexedOrElse`).
  - Serialization and templates: `ExprTemplate`, `ExprTemplateVarKind`, 6-bit ASCII DAG codec
    (`ExprPattern.encode`/`decode`, `ExprTemplate.encode`/`decode`), `inspectClassGoalInputs?`,
    `validateTempHolePlans`, `materializeHolePlans`, `ExprTemplate.instantiateResolved`/`Site`,
    and `SymExtension`-cached `/sym` runtime (`exprSymPatExt`, `exprSymTmplExt`, `exprSymIdxExt`).
  - Goal and expression sources: `ExprContext` (`ExprContext.fill`), `localHypTypes`,
    `localHypDecls`, `MVarId.firstHyp?`/`firstHyp`, `subterms`, `matchDiscriminants`.
- **`Lean.Elab.ExprQuot`** (`src/Lean/Elab/ExprQuot.lean`):
  Macro expansion (`expandMatchModulo`, `expandDoMatchModulo`), relation elaboration
  (`elabExprMatchRel`), pattern preprocessing and elaboration (`elabExprQuotHoleApp`,
  `elabExprQuotPatSlot`, `elabExprQuotPattern`), per-module deduplication extensions
  (`exprPatExt`, `exprPatArrExt`, `exprTmplExt`), join-point `match` compiler
  (`compileExprMatch`), term-position template elaborator (`elabExprQuotTerm`), and diagnostics
  (`checkSyntaxHoleInExprMatchPatterns`, `checkNumeralDefaultingMVars`, `inspectExprQuotPattern`).
- **`Lean.Elab.ExprQuotCommand`** (`src/Lean/Elab/ExprQuotCommand.lean`):
  `#check_pattern` command elaborator (`elabCheckPattern`), isolated above `Lean.Elab.Command` and
  `Lean.Elab.ExprQuot` so `Lean.Elab.BuiltinCommand` has no `ExprQuot` dependency.
- **`Lean.Elab.Tactic.FirstHyp`** (`src/Lean/Elab/Tactic/FirstHyp.lean`):
  `TacticM` backtracking hypothesis search (`firstHyp?`, `firstHyp`) with atomic `SavedState`
  rollback and `sorry`/info-tree hygiene.
- **`Lean.Elab.Tactic.Grind.Sym`** (`src/Lean/Elab/Tactic/Grind/Sym.lean`):
  Generic low-priority `{m} [MonadLiftT GrindTacticM m] : Meta.MonadSym m` instance, kept out of
  `Grind.Basic` to avoid import cycles and preserve `MonadLiftT MetaM GrindTacticM`.
- **Parser, Elaborator, `Sym`, and Diagnostics Hooks**:
  - `src/Lean/Parser/Term.lean`, `Do.lean`, `Command.lean`: `exprQuot`, `exprQuotRel`,
    `matchModulo`, `doMatchModulo`, `doForCaseDecl`, `doForProofCaseDecl`, `checkPattern`,
    internal node kinds `exprQuotHoleApp` and `exprQuotPatSlot`.
  - `src/Lean/Elab/PatternVar.lean`, `Elab/Do/PatternVar.lean`, `Elab/Do/Legacy.lean`,
    `Elab/Do/InferControlInfo.lean`, `Elab/BuiltinDo/For.lean`: pattern-variable collection,
    `for case` macro expansion (`expandDoFor`, `wrapForCaseMatch`), and `ControlInfo.forLoop`.
  - `src/Lean/Elab/Match.lean`, `Elab/BuiltinDo/Match.lean`: parameterized alt-view elaboration
    (`elabMatchAltViewCore`, `elabMatchAltViewsCore`, `elabDoMatchAltCore`) forwarding to
    `compileExprMatch`.
  - `src/Lean/Meta/Sym/Pattern.lean`: `mkPatternCoreFromVars` and `mkPatternFromLambda`.
  - `src/Lean/Linter/Init.lean`, `Elab/Quotation/Util.lean`, `Elab/Quotation.lean`:
    `linter.exprQuot.syntaxHole`, `linter.exprQuot.numeralDefaulting`, `elabStxQuot`, and
    error-only `checkSyntaxHoleInStxMatch` in `elabMatchSyntax`.

---

## ADR-001: Surface Syntax and Stage0-Safe Parsing

**Status:** Accepted

**Context:**
`expr` quotations must coexist with Lean's ordinary syntax quotations (`` `(term) ``), dynamic
quotations (`Parser.Term.dynamicQuot`: `` "`(" >> ident >> "| " ... ``), and existing `match` /
`do match` / `for` ASTs consumed by `stage0` bootstrap code and downstream macros. Registering a
fused token such as `` "`(expr" `` alters Lean's lexer table globally, and inserting optional
children directly into `Parser.Term.«match»` or `Parser.Term.doMatch` shifts fixed child indices
(`stx[i]`) across `stage0` and user macros.

**Decision:**
- Parse `` `(expr[rel]| p) `` in `Parser.Term.exprQuot` (`default+1` priority) using an `atomic`
  two-token header with an explicit whitespace guard (`` "`(" `` + `checkNoWsBefore` +
  `nonReservedSymbol "expr"` + `exprQuotRel` + `"| "`).
- Keep `Parser.Term.«match»` and `Parser.Term.doMatch` completely unchanged. Define dedicated
  `low`-priority `Parser.Term.matchModulo` and `Parser.Term.doMatchModulo` parsers accepting
  `moduloParam` alongside `(dependent := ...)`, `(generalizing := ...)`, and `(motive := ...)` in
  any order, and expand them via `expandMatchModulo` and `expandDoMatchModulo` (sharing
  `mergeOptMatchParam`, `validateAndLiftModuloPins`, and `rewriteMatchAltsModulo`) into standard
  `«match»` and `doMatch` nodes.
- Keep `Parser.Term.doFor`'s child layout unchanged by adding `doForCaseDecl` and
  `doForProofCaseDecl` only inside `doForDeclItem`, expanded by `expandDoFor` + `wrapForCaseMatch`.
- Register internal node kinds `exprQuotHoleApp` and `exprQuotPatSlot` via `registerBuiltinNodeKind`
  to transport preprocessed hole applications and extracted quotation slots without inventing new
  user-visible tokens.

**Alternatives Considered:**
1. *Single fused token `` "`(expr" ``*: risks splitting identifiers starting with `expr` immediately
   after `` `( `` (breaking dynamic quotations such as `` `(exprFoo| ...) ``) and pollutes the
   global token table.
2. *Adding `optional moduloParam` inside `«match»` / `doMatch`*: changes AST child offsets for
   every `match` node, requiring coordinated `stage0` updates and breaking external macros that
   index `stx[k]` directly.

**Consequences & Trade-offs:**
- Zero `stage0` bootstrap churn and zero breakage for existing `match`, `do match`, `for`, and
  dynamic quotation syntax; `expr` remains a non-reserved identifier.
- `matchModulo` / `doMatchModulo` duplicate the surrounding optional-clause grammar at `low`
  priority, and `expandMatchModulo` / `expandDoMatchModulo` must lift dynamic `$x` pins from
  `(modulo := [...])` into enclosing `have` bindings (`validateAndLiftModuloPins`) so pins evaluate
  once rather than once per rewritten pattern arm.

---

## ADR-002: Native `match` / `do match` Compilation into LCNF Join Points

**Status:** Accepted

**Context:**
Users match `Expr` values alongside ordinary inductive constructors (`Option`, `Prod`, `List`),
guards, `if let`, `let ... |`, `fun |`, and `do` control flow. A standalone macro DSL (such as a
bespoke `match_goal` command) duplicates pattern-matching ergonomics, fails to compose with
ordinary constructor patterns, and typically expands into nested `if`-trees that duplicate RHS code
or emit bogus exhaustiveness/redundancy messages.

**Decision:**
- Parameterize Lean's existing match elaborators rather than forking them: factor shared prefix
  elaboration into `elabMatchAltViewCore` and `elabMatchAltViewsCore` (`src/Lean/Elab/Match.lean`)
  and `elabDoMatchAltCore` (`src/Lean/Elab/BuiltinDo/Match.lean`), adding `elabExprMatchAltView`
  and `elabExprMatchAlt`.
- When `hasExprQuotInAltViews` holds, replace each `` `(expr| ...) `` with an `exprQuotPatSlot`
  (`extractAltExprQuots`), pass `?x` binder names via `extraPatternVarNames` into `generalize` so
  match generalization never shadows quotation binders, run ordinary LHS elaboration and
  discriminant refinement, elaborate each slot sequentially (`withElaboratedExprSlots`), and hand
  off to `compileExprMatch`.
- `compileExprMatch` checks exhaustiveness and irrefutable-shadow redundancy using non-emitted
  `Meta.Match.mkMatcher` calls (`_irref_check` and `_shadow_check`, reporting rendered quotation
  syntax via `renderExprMatchAltPatterns` and `reportUnusedAltMsg`). It binds non-fvar
  discriminants once (`bindDiscrsAndDispatch`), binds each arm's RHS as a non-dependent
  `implDetail` join point (`__do_jp` in `bindAltJPsAndDispatch`), groups consecutive arms sharing
  an ordinary pattern skeleton (`canGroupSameSkeleton`, `buildGroupChain`), and threads fall-through
  continuations through `__do_jp` join points (`withFailJP`) without duplicating RHS code or
  emitting `sorryAx` on exhaustive matches (synthesizing `sorry` only for error recovery when
  `!isExhaustive`).
- Reject `match h : e` (`checkNoEqProofOnQuotDiscrs`) on any column containing an `expr` quotation
  because matched `Expr`s satisfy the chosen relation `rel` rather than propositional equality `Eq`.

**Alternatives Considered:**
1. *Bespoke `match_expr_quot` / `match_goal` macro*: could not seamlessly mix ordinary inductive
   patterns with `Expr` patterns, would lose `if let`/`let ... |`/`fun |`/`do` integration, and
   would diverge from Lean's exhaustiveness and redundancy reporting.
2. *Desugaring into nested `Option.rec` / `if-then-else` chains without join points*: duplicates
   fallback arms exponentially when multi-slot or mixed-constructor patterns fail mid-arm.

**Consequences & Trade-offs:**
- Works uniformly across `match`, `fun |`, `if let`, `let ... |`, `do match`, and `for case`,
  producing real LCNF join points and accurate redundancy diagnostics (`match.ignoreUnusedAlts`
  compatible).
- `match h : e` is disallowed on quotation-matched columns (though still permitted on non-quotation
  columns of the same multi-column `match`). Dependent matches skip discriminant `let`-hoisting and
  index grouping so dependent motives and `combineOrigEqs` remain type-correct.

---

## ADR-003: Orthogonal Goal/Subterm Primitives over Monolithic Rocq `match goal`

**Status:** Accepted

**Context:**
Rocq's `match goal with | [ H1 : P, H2 : Q |- context C[t] ] => ...` bundles hypothesis search,
backtracking, multi-hypothesis Cartesian matching, subterm traversal, and contextual rewriting into
one monolithic language construct. In Lean, implicit multi-hypothesis search hides `O(H^k)`
blowups, obscures rollback semantics across `TacticM`/`MetaM`/`InfoTree` state, and makes
dependent contextual rewrites brittle.

**Decision:**
Provide small, orthogonal, composable primitives that pair with native `match` and `for case`:
- **Context snapshots**: `localHypTypes` and `localHypDecls` (`reverse := false`, `except := []`,
  instantiating metavariables and excluding `isImplementationDetail`; `localHypDecls` exposes
  `val?` only for dependent `let`s).
- **Backtracking hypothesis search**: `MVarId.firstHyp?` / `MVarId.firstHyp` (`MetaM` /
  `MonadBacktrack` via `observing?`) and `Elab.Tactic.firstHyp?` / `firstHyp` (`TacticM`), both
  defaulting to `reverse := true` (newest first, matching Rocq) and supporting `except`. The
  `TacticM` version wraps execution in `Term.withoutTacticIncrementality true`,
  `Term.withoutErrToSorry`, and `withoutRecover`, using a single `saveState` per hypothesis and
  `s.restore (restoreInfo := true)` on failure — guaranteeing atomic rollback of goals, `MCtx`,
  messages, and `InfoTree`s with zero `sorry` leakage.
- **Lazy subterm/discriminant streams + zipper context**: `subterms` (`dedup := true` via
  `ExprSet` DAG deduplication, `includeAppPrefixes := false`, syntactic without `instantiateMVars`)
  and `matchDiscriminants` (`alsoCasesOn := false`, `dedup := true`, calling
  `instantiateMVarsIfNeeded` and `matchMatcherApp?`), each yielding `(subterm, ctx : ExprContext)`.
  `ExprContext.fill` rebuilds the enclosing expression via `updateApp!`/`updateLambdaE!`/etc. to
  preserve unchanged subtrees.
- **Refutable loop clauses**: `for case pat in src` expands to
  `match x with | pat => body | _ => continue` (`wrapForCaseMatch`), integrating cleanly with
  `localHypTypes`, `subterms`, and `matchDiscriminants` while diagnosing irrefutable patterns as
  redundant alternatives.
- **Dependent contextual rewrites**: use `ExprContext.fill` with `MVarId.replaceTargetDefEq` for
  contextual `change`, and delegate dependent contextual rewrites (such as `ite` with `Decidable`
  dependencies) to `MVarId.rewrite` (`kabstract`) rather than path-based occurrence rewriting.

**Alternatives Considered:**
1. *Monolithic `match_goal` macro with implicit backtracking and `context C[...]` syntax*: hides
   `O(H^k)` search complexity, requires ad-hoc syntax for `except`/ordering/guards, and breaks when
   syntactic hole replacement invalidates dependent proof/instance arguments.
2. *Pure `for` loops with manual `saveState`*: boilerplate-heavy and error-prone in `TacticM`,
   where forgetting `withoutErrToSorry` or `restoreInfo := true` leaks `sorry` or stale info trees.

**Consequences & Trade-offs:**
- Multi-hypothesis matching is explicit (`firstHyp` nested with `except := [h1]` and `$P` pins),
  making search order and asymptotic cost visible at the call site.
- `subterms` intentionally avoids calling `instantiateMVars` so callers inspecting already
  instantiated targets (`getMainTarget`, `localHypTypes`) pay no extra pass; raw `MVarId.getType`
  callers must instantiate metavariables first.

---

## ADR-004: Five-Engine Relation Hierarchy, `+inst` Hybrid Mode, and `let` Re-Wrapping

**Status:** Accepted

**Context:**
Metaprogramming workloads span a wide spectrum: tight structural AST inspection (`structural`),
matching modulo type-class instances or reducible abbreviations (`+inst`, `reducible`, `instances`),
full definitional equality (`defeq`), and maximally shared symbolic execution (`sym`). Naively
using `Meta.isDefEq` everywhere is slow and over-normalizes `let` bindings, while pure syntactic
matching breaks on non-canonical instances or `let`-bound terms.

**Decision:**
- Define five engines in `ExprMatchEngine` (`structural`, `reducible`, `instances`, `defeq`, `sym`)
  with orthogonal `±flag` overrides (`inst`, `beta`, `zeta`, `proj`, `eta`) and ordered `[±items]`
  (constants, simp sets, and dynamic local dependent-`let` `$x` fvars; last wins).
- Use an intentional **pattern/term default asymmetry**: pattern elaboration (`elabExprMatchRel`)
  defaults to `.structural` (predictable, zero unintended unfolding), whereas term construction
  (`elabExprQuotTerm`) passes `defaultEngine := .defeq` so splice type-checking accepts
  definitionally equal types seamlessly.
- Cache static `[items]` resolution per call site (`ExprMatchRel.resolveStaticCached` via
  `resolvedRelCacheRef`, keyed by `siteId` and validated against `env.constGen`,
  `env.declChangeLog.size`, `env.isExporting`, and `env.header.mainModule`, refreshing `simpSlots`
  in `O(1)`), and validate dynamic local `$x` items at runtime via
  `ResolvedExprMatchRel.withLocalItems`.
- Support **`+inst` hybrid mode** in `/structural`: `structDirectMatch` tries structural argument
  matching first and falls back to `matchInstArgDefEq` (guarded by `isInstArgAt`), running
  `withNewMCtxDepth <| withTransparency .instances <| isDefEq` only on `[instImplicit]` arguments.
- Precompute structural fast paths in `ExprPattern.compile`:
  - `PatHeadGuard` + `fastRejectStructural`: `O(1)` root head+arity rejection before allocating
    `StructState` when `!rel.hasUnfolding`, no unfold items, and tracing is off.
  - `computeCaptureVars` (`captureVars` / `shouldCapture`): skips materializing single-occurrence
    unnamed wildcards unless bound-variable escape checking is needed.
  - Syntactic-before-`isProof` + `collectClosedProofs` (`closedProofs`): `structGo` checks
    `!pe.hasLooseBVars && pe == e` (leveraging pointer equality) before `matchProofIrrel`, which
    resolves closed pattern proofs in `O(1)` via `closedProofs[pe]?`.
  - `computePatLevelNodes` (`patLevelNodes` / `hasPatLevelFast` / `matchLevel`): avoids traversing
    closed subterms for pattern universe parameters while unifying repeated `levelParams`
    consistently.
- Preserve `let` structure without unnecessary substitution:
  - `/structural +zeta` records looked-through bindings as `LetEntry` values and calls `rewrapLets`,
    wrapping captured subterms only in the dependent `let`s they reference.
  - `matchDefEq?` runs `liftInspectedLetsGo` / `liftInspectedLetsStep` to lift outer/inspected
    `let`s whose type and value are independent of pattern binders, tries `runDefEqOnce` with
    `zeta := false` first, falls back to `zeta := true` only when `mayIntroduceLet` indicates
    unfolding may expose a `let` (or when `let`s depend on binders), and re-wraps lifted `let`s
    with `rewrapLets`.

**Alternatives Considered:**
1. *Single `isDefEq`-based engine with `TransparencyMode` only*: cannot express pure syntactic
   matching, `+inst` hybrid matching, or faithful non-substituting `let` re-wrapping, and pays
   `isDefEq` overhead on every arm.
2. *Uniform default engine for patterns and templates*: defaulting patterns to `/defeq` causes
   accidental unfolding in AST matchers; defaulting templates to `/structural` rejects valid
   splices whose inferred type is only definitionally equal to the expected type.

**Consequences & Trade-offs:**
- Fine-grained control over cost and unfolding with `O(1)` fast-reject on structural hot paths.
- `isDefEq` engines still fall back to `let`-substitution when a `let` depends on a pattern binder
  or is exposed only inside `isDefEq`, so captures under `/reducible`/`/instances`/`/defeq` may be
  in `isDefEq`-normalized form; users needing strict `let` preservation should use
  `/structural +zeta`.

---

## ADR-005: `SymM` / `GrindTacticM` Integration, `MonadSym`, and `SymExtension` Caching

**Status:** Accepted

**Context:**
`GrindTacticM` (`ReaderT Context (StateRefT State TermElabM)`) lifts `MetaM` through `TermElabM`.
Its `liftSymM` helper delegates to `liftGrindM`, which executes inside `Grind.withGTransparency`
(`src/Lean/Elab/Tactic/Grind/Basic.lean`). Meanwhile, `Sym.SymM` itself lifts `MetaM`. If we added
a direct `MonadLift Sym.SymM GrindTacticM` instance, Lean's typeclass search could resolve
`MonadLiftT MetaM GrindTacticM` via `MetaM → Sym.SymM → GrindTacticM`, silently hijacking every
lifted `MetaM` operation inside `GrindTacticM` to run under `withGTransparency`. In addition,
`/sym` matching and template building must cache compiled `Sym.Pattern` values, maximally shared
templates, and `DiscrTree`s per `Sym.State` without relying on fragile pointer addresses.

**Decision:**
- Introduce a dedicated `Meta.MonadSym` class (`src/Lean/Meta/ExprPattern.lean`) with a standard
  instance `[MonadLiftT Sym.SymM m] : MonadSym m` covering `SymM`, `GrindM`, `GoalM`, `SimpM`,
  `DSimpM`, and monad transformers over them.
- Declare `public instance (priority := low) {m} [MonadLiftT GrindTacticM m] : Meta.MonadSym m`
  using `liftM (liftSymM x)` in `src/Lean/Elab/Tactic/Grind/Sym.lean` (which already imports
  `Grind.Basic` and `ExprPattern`), leaving `Grind.Basic` untouched to avoid import cycles and
  keeping `MonadLiftT MetaM GrindTacticM` routed through `TermElabM`.
- Add `Sym.mkPatternFromLambda` (factoring `mkPatternCoreFromVars`) in
  `src/Lean/Meta/Sym/Pattern.lean` so compiled `ExprPattern` lambdas undergo standard `Sym`
  preprocessing (`foldProjs`, `unfoldReducible`, `betaReduce`, `zetaReduce`, `etaReduceAll`,
  `normalizeLevels`).
- Register three `SymExtension`s (`exprSymPatExt`, `exprSymTmplExt`, `exprSymIdxExt`) backed by
  `SymSiteKeyCache` (`getOrMkSymSiteKey`) and `SymIdxCacheState`, keyed by compile-time
  `siteId : Name` and invalidated by `env.constGen` (falling back to structural keys when
  `siteId.isAnonymous`), rather than transient `ObjectPtr` keys. Cache maximally shared closed
  templates once (`Sym.shareCommon (← Sym.foldProjs tmpl.lam)`) and instantiate with
  `Sym.instantiateRevS`. Reject unresolved instances (`res.unresolvedInsts`) and leaked temporary
  metavariables (`symHasFreshTemp`) cleanly inside `withNewMCtxDepth`.

**Alternatives Considered:**
1. *`instance : MonadLift Sym.SymM GrindTacticM`*: hijacks `MonadLiftT MetaM GrindTacticM` through
   `withGTransparency`, breaking `GrindTacticM` elaboration and meta calls.
2. *Placing the `GrindTacticM` `MonadSym` instance in `Grind.Basic`*: forces `Grind.Basic` to
   import `ExprPattern`, creating unnecessary coupling and import-graph pressure.
3. *Keying `Sym` caches by `ObjectPtr`*: unsafe across GC/relocation/module reloads and breaks
   sharing across identically deduplicated call sites.

**Consequences & Trade-offs:**
- `` `(expr/sym| ...) `` works uniformly in `SymM`, `GrindM`, `GoalM`, `SimpM`, `DSimpM`,
  `GrindTacticM` (`sym =>` tactics), and transformer stacks (`StateT`/`ReaderT`) with zero
  per-iteration `Sym.Pattern` recompilation or extra `Sym.State.share` nodes.
- `/sym` intentionally rejects `[items]`, local `$x` overrides, and disabling any default flag
  (`validateSymRelCore` / `validateSymFlags`) so `Sym`'s canonical normal form stays sound.

---

## ADR-006: Shared-Relation `DiscrTree` Indexing and Lazy Head-Only MVar Resolution

**Status:** Accepted

**Context:**
Goal-directed tactics and symbolic executors frequently dispatch over 6–50 `` `(expr| ...) `` arms.
Linear CPS dispatch scales as `O(N)` per scrutinee, while naively calling `instantiateMVars` on the
entire scrutinee before `DiscrTree` lookup makes deep terms containing unassigned metavariables
`O(|scrutinee|)` even when a pattern mismatches at depth 1. Furthermore, `DiscrTree` candidate sets
can arrive out of source order or with duplicates (e.g. wildcard + concrete keys), and `/reducible`
/ `/sym` numeral and offset patterns (`5` vs `Nat.succ ?n` vs `?n + 1`) have subtle soundness
interactions with `DiscrTree` keys.

**Decision:**
- Detect maximal consecutive runs (`>= 2`) of simple all-var single-slot arms on the same
  discriminant column with no local `$x` items, identical static behavior
  (`ExprMatchRel.sameStaticBehavior`), and index-sound relation (`ExprMatchRel.isIndexSound`:
  `.structural` with no items/reduction flags, `.reducible` with `beta`/`zeta`/`proj`/`eta` all
  `true`, or `.sym`) in `indexedRunEnd?` and `buildIndexedSlotRun`.
- Emit `ExprPattern.matchIndexedOrElse` (`.structural`/`.reducible`, cached per `siteId` in
  `metaIndexCacheRef`) or `ExprPattern.matchSymIndexedOrElse` (`.sym`, cached in `exprSymIdxExt`).
- Preserve exact source-order semantics and at-most-once evaluation via `sortAndDedupCands` before
  `dispatchCandidates` invokes `tryAt[idx]`.
- In `/structural` indexing (`structuralPatKeys`), emit `.star` for closed proofs and for
  `[instImplicit]` arguments when `+inst` is active. During lookup (`structuralDiscrTreeGetMatch`,
  `structuralTrieGetMatch`, `structuralScrutineeStep`), resolve assigned metavariables lazily at
  inspected heads only via pure `resolveHeadMVarPure` — never calling full-scrutinee
  `instantiateMVars`.
- In `/reducible` indexing (`reduciblePatKeys`), record `hasNatLitKey` on `CachedMetaIndex` when
  any pattern lowers to a `.lit (.natVal _)`; during lookup (`matchIndexedCandidates`), call
  `reduceToNatLit?` (guarded by `withIncRecDepth`) **only** when `hasNatLitKey` is `true`.
- In `/sym` indexing (`annotateSymNatAndOffsets`, `mkSymPatDiscrTreeKeys`), mark offsets
  (`Sym.isOffset?`, `Sym.isQuasiOffset`), `Nat` values/literals, `Nat.zero`, lambdas, and sorts
  with `DiscrTree.mkNoindexAnnotation` (yielding root key `#[.star]`) so offset patterns like
  `Nat.succ ?n` or `(?n : Nat) + 1` still retrieve raw numeral literals such as `5`. Lookup
  (`symDiscrTreeGetMatch`, `symRootMatch`, `symTrieGetMatch`) lazily unfolds `letE`,
  `Sym.getLetValueS?`, head-beta, and `Sym.etaReduce` via `symResolveMVars` under `withIncRecDepth`.

**Alternatives Considered:**
1. *Reordering arms across non-consecutive or heterogeneous-relation blocks*: violates Lean's
   top-to-bottom match priority semantics.
2. *Using `Meta.DiscrTree.getMatch` for `/structural`*: eagerly normalizes/instantiates scrutinees
   and breaks `O(|pattern|)` scaling on deep terms with unassigned metavariables.
3. *Unconditionally calling `reduceToNatLit?` on every `/reducible` indexed lookup*: adds wasted
   `whnf` work on every dispatch even when no arm matches a `Nat` literal.

**Consequences & Trade-offs:**
- Exact semantic equivalence with linear sequential matching (verified differentially across
  structural, reducible, and `/sym` corpuses), `O(|pattern|)` deep-spine scaling under
  `/structural`, and zero `reduceToNatLit?` overhead on non-numeral `/reducible` tables.
- `.instances`, `.defeq`, local `$x` items, and `/structural` with `+beta`/`+zeta`/`+proj`/`+eta`
  or `[items]` fall back to linear CPS dispatch (`ExprMatchRel.isIndexSound = false`).

---

## ADR-007: Compact 6-Bit ASCII DAG Serialization and LCNF `ExtractClosed` Hoisting

**Status:** Accepted

**Context:**
Elaborating an `ExprPattern` or `ExprTemplate` directly into nested Lean term constructors
(`Expr.app (Expr.const ...) ...`) causes severe compile-time slowdowns in elaboration, kernel
type-checking, and LCNF compilation for large patterns. Conversely, emitting an `addAndCompile`
auxiliary declaration for every pattern or template bloats the environment, persists garbage across
elaboration retries, and interacts poorly with `withoutModifyingEnv` and parallel/async elaboration.

**Decision:**
- Serialize closed compiled `ExprPattern` and `ExprTemplate` values into compact, lossless,
  DAG-interned binary tables (`DagEncState`, `internName`, `internLevel`, `internExpr`, LEB128
  varints, versioned with `patternBlobVersion := 1` and `templateBlobVersion := 2`) packed into
  printable 6-bit ASCII string literals (`encodeBytesAscii`/`decodeBytesAscii`,
  `ExprPattern.encode`/`decode`/`decodeExcept`, `ExprTemplate.encode`/`decode`/`decodeExcept`).
- Deduplicate compiled patterns, pattern arrays, and templates per module using `.local`
  `EnvExtension`s (`exprPatExt`, `exprPatArrExt`, `exprTmplExt`) in `mkAuxPatExpr`,
  `mkAuxPatArrExpr`, and `mkAuxTmplExpr`, emitting a single closed expression
  `ExprPattern.decode "..."` or `ExprTemplate.decode "..."` paired with a unique `siteId`
  (`mkUniqueSiteId`).
- Rely on LCNF's `extractClosed` pass (`src/Lean/Compiler/LCNF/ExtractClosed.lean`) and
  `ClosedTermCache` (`src/Lean/Compiler/ClosedTermCache.lean`) to automatically hoist and
  deduplicate these closed `decode` calls into once-initialized closed constants inside the
  enclosing declaration — emitting **zero** `addAndCompile` auxiliary declarations.

**Alternatives Considered:**
1. *Direct recursive `Expr`/`ExprPattern` constructor ASTs*: simple, but triggers quadratic/large
   kernel type-checking and LCNF compile-time regressions on realistic patterns.
2. *`addAndCompile` auxiliary declarations per quotation*: bloats the `Environment` with extra
   constants, leaks across retry/backtracking boundaries, and adds per-quotation compilation
   overhead.
3. *Native `.olean` `EnvExtension` payload table*: eliminates the codec entirely, but requires
   `.olean` persistence hooks and cross-stage/module serialization plumbing.

**Consequences & Trade-offs:**
- Zero extra `Environment` declarations, clean retry/module isolation, fast kernel checking (one
  string literal per pattern/template), and automatic once-per-process hoisting by `extractClosed`.
- **Candid upstream trade-off**: the self-contained codec (`src/Lean/Meta/ExprPattern.lean`, ~690
  lines) adds maintenance surface and a small one-time decode cost at module initialization
  compared to storing native `Expr` blobs in a dedicated `.olean` `EnvExtension`. However, the
  representation is completely encapsulated behind `mkAuxPatExpr` / `mkAuxTmplExpr` and can be
  swapped to an `.olean` table upstream later without changing surface syntax or runtime APIs.

---

## ADR-008: Template Hole Hygiene and Zero-Overhead Scoped Diagnostics

**Status:** Accepted

**Context:**
Term-position templates `` `(expr[rel]| t) `` mix splice type-checking, runtime type-class
synthesis, and fresh `?h`/`?_` hole creation; temporary metavariables created inside
`withNewMCtxDepth` become dangling if they escape into a materialized hole's type. Separately,
writing an ordinary syntax quotation `` `(?x + ?y) `` on an `Expr` value is a common mistake, yet
diagnostics for it must not slow down ordinary `match` elaboration, misdiagnose `Syntax`/`TSyntax`
quotations, or duplicate `InfoTree` entries.

**Decision:**
- **Compile-time determination & runtime hole hygiene**:
  - At elaboration time (`elabExprQuotTerm`), `computeTemplateDetermined` computes a fixed point
    over splice types and `inspectClassGoalInputs?` (tracking non-`outParam` arguments and
    non-output universe levels) to classify abstracted metavariables into `.splice`, `.hole`,
    `.tc`, and `.infer`, rejecting under-determined holes/instances/universes statically via
    `reportTermBuildErrors`.
  - At runtime (`ExprTemplate.instantiateResolved` and `instantiateSymCore`), splice checks,
    implicit unification, and `resolveReadyTCs` (using `isTCGoalReady` -> `inspectClassGoalInputs?`)
    run inside `withNewMCtxDepth` so caller metavariables stay untouched. Before exiting
    `withNewMCtxDepth`, `validateTempHolePlans` checks each `HolePlaceholder`'s instantiated type
    with `hasTempMVar` / `levelHasTempMVar`, passing `allowed := priorTmpHoles` (permitting
    telescoping holes while rejecting any unresolved inner-depth metavariable or level mvar). Only
    after `withNewMCtxDepth` returns does `materializeHolePlans` allocate `.syntheticOpaque`
    metavariables in the caller's `MCtx`, rewriting earlier hole references via `tmpHoleMap` and
    guarding against forward cycles with `hasAnyMVarInSet`.
- **Zero-overhead scoped diagnostics**:
  - `checkSyntaxHoleInExprMatchPatterns` (`src/Lean/Elab/ExprQuot.lean`, called from `Match.lean`
    and `BuiltinDo/Match.lean`) pre-scans patterns purely syntactically via `extractNonExprQuot?`
    (`unwrapPatSyntaxParens`), returning immediately with **0** `inferType`/`whnf` calls on
    ordinary `match` expressions.
  - `Quotation.elabStxQuot` (`src/Lean/Elab/Quotation.lean`) guards on
    `linter.exprQuot.syntaxHole` and `isExprOrMonadExpr expectedType?` before running
    `collectNamedSyntaxHoles` (`Quotation/Util.lean`, ignoring `?_`, antiquotations, nested
    quotations, and `exprQuot`).
  - `Quotation.elabMatchSyntax` records `Term.saveState` and
    `savedNumMsgs := log.reported.size + log.unreported.size` (`O(1)`), runs `match_syntax.expand`
    and `elabTerm` once on the happy path (zero duplicate `InfoTree`s), and invokes
    `checkSyntaxHoleInStxMatch` only if `hasNewErrorSince` detects a new error or an `.error`
    exception is thrown.
  - `checkNumeralDefaultingMVars` activates only when `linter.exprQuot.numeralDefaulting` is true
    and inspects pending `OfNat ?α _` synthetic metavariables before default synthesis.
  - `#check_pattern` (`src/Lean/Elab/ExprQuotCommand.lean`) lives in its own module above
    `Lean.Elab.Command` and `Lean.Elab.ExprQuot` and calls `inspectExprQuotPattern` inside
    `withoutModifyingEnv`, keeping `Lean.Elab.BuiltinCommand` free of `ExprQuot` imports.

**Alternatives Considered:**
1. *Materializing `?h`/`?_` holes directly inside `withNewMCtxDepth`*: leaks inner-depth mvars or
   allows temporary unification variables to linger in materialized hole types.
2. *Eagerly elaborating discriminants in `elabMatchSyntax` before `match_syntax.expand`*: slows
   every syntax-matching function and duplicates `InfoTree` hover/type entries on the happy path.
3. *Checking `inferType` on every `match` discriminant in `Match.lean`*: imposes unnecessary `whnf`
   and type-inference work on ordinary matches that contain no quotations at all.

**Consequences & Trade-offs:**
- Zero dangling inner-depth metavariables in materialized template holes, zero `inferType`/`whnf`
  overhead on ordinary `match` expressions, and zero duplicate `InfoTree`s in `elabMatchSyntax`.
- On failing syntax matches whose discriminant is an `Expr`, `elabMatchSyntax` briefly restores
  `savedState` to emit the targeted `` `(expr| ...) `` diagnostic and linter warning, then
  restores `postState` if no `Expr` column was found so original errors remain intact.
