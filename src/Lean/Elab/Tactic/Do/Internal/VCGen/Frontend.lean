/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.SuggestInvariant
public import Lean.Elab.Tactic.Do.VCGen
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.Driver
public import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProcAttr
public import Lean.Meta.Sym.Simp.Attr
public import Lean.Meta.Sym.Simp.ControlFlow
public import Lean.Meta.Sym.Simp.EvalGround
public import Lean.Meta.Sym.Simp.Forall
public import Lean.Meta.Sym.Simp.Rewrite
public import Lean.Meta.Sym.Simp.Simproc
public import Lean.Elab.Tactic.Grind.Main
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Sym.ProofInstInfo

open Lean Parser Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do Lean.Elab.Tactic.Do.Internal.SpecAttr

namespace Lean.Elab.Tactic.Do.Internal

/-!
`vcgen` tactic frontend: parse the user-facing argument syntax into a
`VCGen.Context`, run `VCGen.run`, and replace the main goal with the
resulting invariants and VCs.
-/

/-- A local helper for running config elaborators in TermElabM. -/
private def runTacticM (x : TacticM α) (goals : List MVarId := [])  : TermElabM α :=
  x.run { elaborator := `mvcgen } |>.run' { goals }

namespace VCGen

/--
Parse the optional `[...]` argument list for `vcgen`, partitioning entries into
spec theorems and simp lemmas. Follows the same approach as
`Lean.Elab.Tactic.Do.VCGen.mkContext`: each entry is first tried as a spec theorem,
and on failure falls back to a simp/unfold lemma processed via `mkSimpContext`.
-/
public def mkContext (lemmas : Syntax) (goal : MVarId) (ignoreStarArg := false) :
    TermElabM (VCGen.Context × VCGen.Scope) := do
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut simpTermThms : Array SimpTheorem := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      -- Try to interpret as a spec theorem erasure; fall back to simp erasure. A definition
      -- registered with `attribute [spec] foo` contributes its unfold equations to the database, so
      -- `[-foo]` must erase each of those proofs, not just a proof named `foo`.
      let mut erased := false
      try
        if let some fvar ← Term.isLocalIdent? arg[1] then
          if let some specThm ← mkSpecTheoremFromLocal fvar.fvarId! then
            specThms := specThms.erase specThm.proof
            erased := true
        else
          let id := arg[1]
          let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id)
            | withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
          for proof in (← specEraseProofs declName) do
            specThms := specThms.erase proof
            erased := true
      catch _ => pure ()
      unless erased do
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        try
          let some thm ← mkSpecTheoremFromConst declName
            | throwError "not a spec theorem"
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        try
          let some thm ← mkSpecTheoremFromLocal fvar
            | throwError "not a spec theorem"
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ =>
        -- A term that is not a bare identifier (e.g. `show l = r from h`, `foo x`, `@foo`).
        -- Mirror `simp`: elaborate once, register a spec proof as a spec, and any other proof as a
        -- simp lemma (which `addSimpSpecs` turns into an equational spec).
        let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef term do
          let e ← Term.elabTerm term .none
          Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
          let e ← instantiateMVars e
          if e.hasSyntheticSorry then
            return none
          let e := e.eta
          if e.hasMVar then
            let r ← abstractMVars e
            return some (r.paramNames, r.expr)
          else
            return some (#[], e)
        if let some (levelParams, proof) := thm? then
          if let some thm ← mkSpecTheoremFromStx term proof then
            specThms := specThms.insert thm
          else
            let thms ← mkSimpTheoremFromExpr (.stx (← mkFreshId) arg) levelParams proof
            simpTermThms := simpTermThms ++ thms
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a simp context from the collected per-call simp/unfold arguments only. Global
  -- `@[spec]`-registered equations and unfold definitions already live in the internal spec
  -- database (inserted at annotation time), so the context is not seeded from `mvcgen_simp`.
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  let res ← runTacticM (goals := [goal]) <| mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := pure {})
    (ignoreStarArg := ignoreStarArg)
  let mut simpThms := res.ctx.simpTheorems[0]?.getD {}
  for thm in simpTermThms do
    simpThms := simpThms.addSimpTheorem thm
  -- Add local spec hypotheses when `*` is used.
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          if let some thm ← mkSpecTheoremFromLocal fvar then
            specThms := specThms.insert thm
        catch _ => continue
  let backwardRules ← VCGen.mkBackwardRules
  let allSpecThms ← addSimpSpecs specThms simpThms
  let ctx : VCGen.Context := { backwardRules }
  return (ctx, { specs := allSpecThms })

/-- True iff `m` carries a `WPMonad m _ _` instance, i.e. it is a genuine weakest-precondition monad
rather than a deep-embedding program type with a bespoke `WP`. The `Pred`/`EPred` `outParam`s are left
as metavariables for instance search to fill; instance search runs at default transparency, while the
caller reduces types at reducible transparency. -/
private def isWPMonad (m : Expr) : MetaM Bool := withDefault do
  try
    let wpm ← mkConstWithFreshMVarLevels ``Std.Internal.Do.WPMonad
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType wpm)
    unless ← isDefEq args[0]! m do return false
    return (← synthInstance? (mkAppN wpm args)).isSome
  catch _ => return false

/-- Infer the program type of a `vcgen` goal, the key for frame-procedure selection and the expected
type for elaborating `frames`/`until` patterns. Peels leading binders, then reads the program type
from a bare `wp …` target, a `pre ⊑ wp …` entailment, or a `Triple`. When the program type is `m α`
with `m` a `WPMonad`, the monad `m` is returned (frameprocs are keyed by monad); otherwise the whole
program type is returned, so deep embeddings key on their own head. Returns `none` when the goal
exposes no program. -/
public def inferProgType? (goalType : Expr) : MetaM (Option Expr) := withReducible do
  forallTelescopeReducing goalType fun _ body => do
    let body := body.consumeMData
    let progTy? : Option Expr :=
      if let some info := isWPApp? body then
        some info.Prog
      else if let some (_, _, _, rhs) := body.app4? ``Lean.Order.PartialOrder.rel then
        (isWPApp? rhs).map (·.Prog)
      else
        body.withApp fun head args =>
          if head.isConstOf ``Std.Internal.Do.Triple && args.size ≥ 3 then some args[2]! else none
    let some progTy := progTy? | return none
    let progTy ← whnf progTy
    if progTy.isApp then
      if ← isWPMonad progTy.appFn! then
        return some progTy.appFn!
    return some progTy

end VCGen

/-- Warn about `vcgen` config options that are accepted by the parser but currently
ignored at runtime. As more options gain implementation support, drop their checks
here. Options with implemented semantics (`trivial`, `elimLets`, `stepLimit`,
`invariants?`) are silently accepted. -/
private def warnIgnoredConfig (config : VCGen.Config) : MetaM Unit := do
  let default : VCGen.Config := {}
  if config.leave != default.leave then
    logWarning "vcgen: the `leave` config option is currently ignored."

/--
Build `Sym.Simp.Methods` from a variant name and extra theorems.
Supports the anonymous (default) variant. Named variants require a public
`elabSimpMethods` API in `Lean.Elab.Tactic.Grind.Sym` (see TODO below).
-/
private def elabSymSimpParts
    (variantId? : Option (TSyntax `ident))
    (extraIds? : Option (Array (TSyntax `ident)))
    : MetaM Sym.Simp.Methods := do
  let variantName := variantId?.map (·.getId) |>.getD .anonymous
  if !variantName.isAnonymous then
    -- TODO: `resolveExtraTheorems`, `elabVariant`, and `elabSymSimproc` in
    -- `Lean.Elab.Tactic.Grind.Sym` are module-private (non-`public section`).
    -- To support named variants here, we need a public API such as:
    --   `public def elabSymSimp (syn : Syntax) : GrindTacticM (Sym.Simp.Methods × ...)`
    -- exposed from that module, plus a lightweight `GrindTacticM` runner
    -- (the simproc elaborators only use `CoreM`/`MetaM` capabilities).
    throwError "named Sym.simp variants are not yet supported in `vcgen`; \
      use `vcgen simplifying_assumptions [thm₁, thm₂, ...]` with the default variant instead"
  -- Resolve extra theorems (local hypotheses first, then global constants)
  let mut extraThms : Array Sym.Simp.Theorem := #[]
  if let some ids := extraIds? then
    let lctx ← getLCtx
    for id in ids do
      if let some decl := lctx.findFromUserName? id.getId then
        extraThms := extraThms.push (← Sym.Simp.mkTheoremFromExpr decl.toExpr)
      else
        let declName ← realizeGlobalConstNoOverload id
        extraThms := extraThms.push (← Sym.Simp.mkTheoremFromDecl declName)
  -- Build default variant methods
  let symThms ← Sym.Simp.getSymSimpTheorems
  let pre := Sym.Simp.simpControl >> Sym.Simp.simpArrowTelescope
  let mut post : Sym.Simp.Simproc := Sym.Simp.evalGround >> symThms.rewrite
  if !extraThms.isEmpty then
    let mut thms : Sym.Simp.Theorems := {}
    for thm in extraThms do thms := thms.insert thm
    post := post >> thms.rewrite
  return { pre, post }

private def elabSimplifyingAssumptions (simpClause : Syntax) : MetaM (Option Sym.Simp.Methods) := do
  if simpClause.getNumArgs == 0 then return none
  let variantId? := if simpClause[1].getNumArgs != 0 then some ⟨simpClause[1][0]⟩ else none
  let extraIds? := if simpClause[2].getNumArgs != 0
    then some (simpClause[2][1].getSepArgs.map (⟨·⟩)) else none
  pure (some (← elabSymSimpParts variantId? extraIds?))

/--
Pre-parse the optional `invariantAlts` syntax into a map from invariant number
to alt syntax. Bullet form `· $rhs` is positional (1-based: bullet at index `i`
maps to key `i+1`); labelled form `| inv<n> $args* => $rhs` is keyed by the
parsed `n`, so out-of-order labels are supported.

Returns `none` for the `invariants?` form (delegated to upstream `elabInvariants`)
and `none` when no `invariants` clause is provided. Errors on mixed bullet/labelled
forms (one or the other is enforced by the `dotOrCase` flag in the upstream
elaborator; we replicate that check here).
-/
private def parseInvariantMap (stx : Syntax) :
    TermElabM (Option (Std.HashMap Nat Syntax)) := do
  let some altsStx := stx.getOptional? | return none
  -- The `invariants?` (suggest) form is handled separately by upstream's `elabInvariants`.
  match altsStx with
  | `(invariantAlts| invariants? $_*) => return none
  | _ => pure ()
  let stx' : TSyntax ``invariantAlts := ⟨altsStx⟩
  match stx' with
  | `(invariantAlts| $_invariantsKW $alts*) =>
    if alts.isEmpty then return some {}
    let mut map : Std.HashMap Nat Syntax := {}
    let mut dotOrCase := LBool.undef
    for h : i in 0...alts.size do
      let alt := alts[i]
      match alt with
      | `(invariantDotAlt| · $_rhs) =>
        if dotOrCase matches .false then
          throwErrorAt alt "Alternation between labelled and bulleted invariants is not supported."
        dotOrCase := .true
        map := map.insert (i + 1) alt
      | `(invariantCaseAlt| | $tag $_args* => $_rhs) =>
        if dotOrCase matches .true then
          throwErrorAt alt "Alternation between labelled and bulleted invariants is not supported."
        dotOrCase := .false
        let n? : Option Nat := do
          let `(binderIdent| $tag:ident) := tag | some (i + 1) -- positional fallback
          let .str .anonymous s := tag.getId | none
          s.dropPrefix? "inv" >>= String.Slice.toNat?
        let some n := n? | throwErrorAt tag s!"Could not parse invariant label; expected `inv<n>`."
        if map.contains n then
          throwErrorAt tag s!"Duplicate invariant alternative for `inv{n}`."
        map := map.insert n alt
      | _ => throwErrorAt alt "Expected `invariantDotAlt` or `invariantCaseAlt`."
    return some map
  | _ => return none

/--
Run after VC generation: iterate the (unfiltered) `invariants` array returned by
`VCGen.run`, look up each entry in the pre-parsed `alts` map by its 1-based
position (which equals the `inv<n>` tag the entry carries — `VCGen.run` assigns
tags consecutively), and elaborate the matching alt. Invariants that were already
elaborated inline by `Driver.emitVC` (tracked in `inlineHandled`) are skipped, so
we don't warn about alts that were already consumed there. -/
private def elabRemainingInvariants (alts : Std.HashMap Nat Syntax)
    (invariants : Array MVarId) (inlineHandled : Std.HashSet Nat) : SymM Unit := do
  let mut handled := inlineHandled
  for h : i in 0...invariants.size do
    let n := i + 1
    if handled.contains n then continue
    let some alt := alts[n]? | continue
    handled := handled.insert n
    discard <| VCGen.elabInvariant alts n invariants[i]
  -- Warn on user-provided alts that matched no invariant goal (neither inline nor post-hoc).
  for (n, alt) in alts.toArray do
    unless handled.contains n do
      logWarningAt alt s!"Invariant alternative `inv{n}` does not match any invariant goal."

/-- Parsed `vcgen` arguments shared by the two entry points. -/
private structure ParsedArgs where
  config : VCGen.Config
  ctx : VCGen.Context
  scope : VCGen.Scope
  invariantAlts? : Option (Std.HashMap Nat Syntax)
  frameDB : FrameDB

/-- Build a `Sym.Pattern` from `e` by abstracting the metavariables `xs` into pattern variables.
`checkTypeMask?` is `none` because `until` holes appear as function arguments, whose types the
enclosing application already constrains. -/
private def mkUntilPattern (xs : Array Expr) (e : Expr) : MetaM Sym.Pattern := do
  let pattern := e.abstract xs
  let mut varTypes := #[]
  for h : i in [0:xs.size] do
    varTypes := varTypes.push ((← inferType xs[i]).abstractRange i xs)
  let mut fnInfos : AssocList Name Sym.ProofInstInfo := {}
  for declName in pattern.getUsedConstants do
    if let some info ← Sym.mkProofInstInfo? declName then
      fnInfos := fnInfos.insertNew declName info
  let varInfos? ← Sym.mkProofInstArgInfo? xs
  return { levelParams := [], varTypes, pattern, fnInfos, varInfos?, checkTypeMask? := none }

/-- Run a program-pattern elaboration in the goal context: ignore type-class failures, disable `sorry`
elaboration, and restore the meta state afterwards while keeping info trees so hovers work on the
pattern. Shared by `elabUntilPattern` and `elabFrameDB`. -/
private def withPatternElab (k : TermElabM α) : TermElabM α :=
  Term.withoutModifyingElabMetaStateWithInfo <|
  withTheReader Term.Context ({ · with ignoreTCFailures := true }) <|
  Term.withoutErrToSorry k

/-- Elaborate a program pattern term `p` against the program monad `m` (expected type `m _`, so
overloaded heads resolve), returning its pattern variables (the collected metavariables: holes and
synthetic holes) and the resulting `Sym.Pattern`. -/
private def elabProgPattern (progTy : Expr) (p : Term) : TermElabM (Array Expr × Sym.Pattern) := do
  -- A monad `m : Type → Type` expects the program at `m _` so its overloaded head resolves; a
  -- deep-embedding program type is already saturated and is used directly.
  let expectedTy ← if (← inferType progTy).isArrow
    then pure (mkApp progTy (← mkFreshTypeMVar)) else pure progTy
  let e ← instantiateMVars (← Term.elabTerm p (some expectedTy))
  let xs := (e.collectMVars {}).result.map Expr.mvar
  return (xs, ← mkUntilPattern xs e)

/-- Build an `until` pattern (holes `_` allowed, as in `conv in $t`) against the goal program type
`progTy` as expected type, so overloaded heads resolve. The holes become pattern variables. -/
private def elabUntilPattern (progTy : Expr) (p : Term) : TermElabM Sym.Pattern :=
  withPatternElab <| withRef p do
    return (← elabProgPattern progTy p).2

/-- Build a `frames` database against the goal program type `progTy` as expected type. Each
alternative's program pattern (a head applied to binder/`_` arguments) is elaborated at `progTy`; a
named binder `x` becomes a synthetic hole `?x` so its name can be recovered and bound to the matched
argument when the frame term is elaborated in `solve`. -/
private def elabFrameDB (progTy : Expr) (alts : Array Syntax) : TermElabM FrameDB :=
  withPatternElab do
    let mut tree : DiscrTree Nat := .empty
    let mut entries : Array FrameEntry := #[]
    for h : i in [0:alts.size] do
      let alt := alts[i]
      let `(frameAlt| | $head:ident $args* => $frame) := alt
        | throwErrorAt alt "Expected a `frames` alternative `| f a _ c => frame`."
      -- Named binders become synthetic holes `?x`; `_` stays a plain hole.
      let argTerms ← args.mapM fun arg => do
        match arg with
        | `(binderIdent| $x:ident) =>
          pure (⟨Syntax.node .none ``Lean.Parser.Term.syntheticHole #[mkAtom "?", x.raw]⟩ : Term)
        | _ => `(_)
      let progPat ← `($head $argTerms*)
      let (xs, pat) ← withRef alt <| elabProgPattern progTy progPat
      let varNames ← xs.mapM fun x => do
        let nm := (← x.mvarId!.getDecl).userName
        return if nm.isAnonymous then none else some nm
      entries := entries.push { pat, varNames, frameStx := frame, srcIdx := i }
      tree := Sym.insertPattern tree pat i
      trace[Elab.Tactic.Do.vcgen] "`frames` pattern elaborated to {pat.pattern}"
    return { tree, entries }

/-- Parse `vcgen` arguments. -/
private def parseArgs (stx : Syntax) (goal : MVarId) : TermElabM ParsedArgs := goal.withContext do
  if mvcgen.warning.get (← getOptions) then
    logWarningAt stx "The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` \
      that will eventually replace it. Avoid using it in production projects."
  let config ← runTacticM <| elabConfig stx[1]
  warnIgnoredConfig config
  -- `elimLets` defaults to `false` in `vcgen` (vs. `true` in upstream `mvcgen`):
  -- existing tests rely on let-bindings being preserved in VC local contexts so that
  -- `case vcN bs* =>` patterns line up. Re-enabling on opt-in would require detecting
  -- explicit `(elimLets := true)` at the syntax level (upstream `Config` can't
  -- distinguish "default true" from "user-set true"); not yet wired.
  let (ctx, scope) ← VCGen.mkContext stx[2] goal
  -- The program type, inferred once from the goal, is the expected type for the `frames`/`until`
  -- program patterns (so overloaded heads resolve). A goal with no program cannot be a `vcgen` goal.
  let some progTy ← VCGen.inferProgType? (← goal.getType)
    | throwError "vcgen: could not determine the program type of the goal"
  let frameProcs ← VCGen.getFrameProcs
  let untilPat? ← if stx[3].isNone then pure none
    else some <$> elabUntilPattern progTy ⟨stx[3][1]⟩
  let frameDB ← if stx[4].isNone then pure ({} : FrameDB)
    else elabFrameDB progTy stx[4][1].getArgs
  let invariantAlts? ← parseInvariantMap stx[5]
  let hypSimpMethods ← elabSimplifyingAssumptions stx[6]
  let ctx := { ctx with
    hypSimpMethods,
    frameProcs,
    latticeOps := VCGen.mkLatticeOpTable frameProcs.latticeOps,
    trivial := config.trivial,
    useJP := config.jp,
    errorOnMissingSpec := config.errorOnMissingSpec,
    debug := config.debug,
    internalize := config.internalize,
    invariantAlts := invariantAlts?.getD {},
    untilPat? }
  return { config, ctx, scope, invariantAlts?, frameDB }

/-- `vcgen` step inside `sym => …` blocks. -/
@[builtin_grind_tactic Lean.Parser.Tactic.Grind.vcgen]
def evalSymVCGen : Lean.Elab.Tactic.Grind.GrindTactic := fun stx => do
  let goal ← Lean.Elab.Tactic.Grind.getMainGoal
  let args ← parseArgs stx goal.mvarId
  let result ← Lean.Elab.Tactic.Grind.liftGrindM do
    let result ← VCGen.run goal args.ctx args.scope args.config.stepLimit (frameDB := args.frameDB)
    if let some alts := args.invariantAlts? then
      elabRemainingInvariants alts result.invariants result.inlineHandledInvariants
    return result
  if let some frameStx := result.unmatchedFrames[0]? then
    throwErrorAt frameStx "`frames` alternative matched no program in the goal"
  if args.invariantAlts?.isNone then
    runTacticM (goals := result.invariants.toList) <|
      elabInvariants stx[5] result.invariants (suggestInvariant (result.vcs.map (·.mvarId)))
  let invariants ← result.invariants.filterM (not <$> ·.isAssigned)
  let newGoals ← Lean.Elab.Tactic.Grind.liftGrindM do
    let invGoals ← invariants.toList.mapM Grind.mkGoalCore
    return invGoals ++ result.vcs.toList
  Lean.Elab.Tactic.Grind.replaceMainGoal newGoals

/-- Validate the optional `with` clause of `vcgen`. It must be a `grind`-mode step so it can share
`vcgen`'s internalised E-graph; the `vcgenDischarge` category's `tactic` alternative is a catch-all
that exists only so a non-`grind` step is reported here with a helpful error rather than a raw
`expected grind` parser error. -/
private def elabVCGenDischarge (w? : Option (TSyntax `vcgenDischarge)) :
    TacticM (Option (TSyntax `grind)) :=
  match w? with
  | none   => return none
  | some w =>
    if w.raw.getKind == ``Lean.Parser.Tactic.vcgenDischargeGrind then
      return some ⟨w.raw[0]⟩
    else
      throwErrorAt w
        m!"`vcgen … with` expects a `grind`-mode discharging step, not a general tactic"
          ++ MessageData.hint' m!"Examples: `vcgen … with finish`, `vcgen … with intro`."

/-- Tactic-level `vcgen`. Reuses the grind-mode implementation by re-quoting the
input as `Grind.vcgen …` and running it inside a `GrindTacticM` context built
without `withProtectedMCtx`, so leftover `Grind.Goal`s flow back as the new tactic
goals. The optional `with $g:grind` clause runs as `<;> $g` and lets the user-supplied
grind step share an internalised E-graph with `vcgen`. -/
@[builtin_tactic Lean.Parser.Tactic.vcgen]
public def elabVCGen : Tactic := fun stx => withMainContext do
  let `(tactic| vcgen%$tk $cfg:optConfig $[[$lems,*]]? $[until $u:term]? $[frames $fas*]? $(invs)?
        $[simplifying_assumptions $(sa)? $[[$thms,*]]?]? $[with $w:vcgenDischarge]?) := stx
    | throwUnsupportedSyntax
  let g? ← elabVCGenDischarge w
  -- Without `with`, no downstream grind step will read the E-graph, so opt out of
  -- internalisation; `with` keeps the default `internalize := true`.
  let cfg ← match g? with
    | some _ => pure cfg
    | none   => do
        let off ← `(optConfig| -internalize)
        pure (Lean.Parser.Tactic.appendConfig off cfg)
  let core ← `(grind| vcgen%$tk $cfg:optConfig $[[$lems,*]]? $[until $u:term]? $[frames $fas*]? $(invs)?
        $[simplifying_assumptions $(sa)? $[[$thms,*]]?]?)
  let step ← match g? with
    | some g => `(grind| $core <;> $g)
    | none   => pure core
  let goal ← getMainGoal
  -- `clean := false` keeps inaccessible binder names (no `exposeNames`), so users can
  -- still rename them with `case vcN h => …`.
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) <|
    Grind.evalGrindTactic step
  replaceMainGoal (state.goals.map (·.mvarId))

end Lean.Elab.Tactic.Do.Internal
