/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.Basic
import Lean.Elab.Match
import Lean.Elab.MatchAltView
import Lean.Data.Array

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

-- cf. Term.expandNonAtomicDiscrs?
private def elabNonAtomicDiscrs (motive? : Option (TSyntax ``motive)) (discrs : TSyntaxArray ``matchDiscr) (k : TSyntaxArray ``matchDiscr → DoElabM α) : DoElabM α := do
  if motive?.isSome then
    -- We do not pull non atomic discriminants when match type is provided explicitly by the user
    return ← k discrs
  -- Recall that
  -- matchDiscr := leading_parser optional (ident >> ":") >> termParser
  if ← discrs.allM fun discr => Term.isAtomicDiscr discr.raw[1] then
    return ← k discrs
  let rec loop (i : Nat) (newDiscrs : TSyntaxArray ``matchDiscr) : DoElabM α := do
    if h : i < discrs.size then
      let discr := discrs[i]
      let `(matchDiscr| $[$h? :]? $term) := discr | throwUnsupportedSyntax
      if (← Term.isAtomicDiscr term) then
        loop (i + 1) (newDiscrs.push discr)
      else
        withFreshMacroScope do
          let e ← Term.withSynthesize (postpone := .yes) <| Term.elabTerm term none
          let discrNew ← `(matchDiscr| $[$h? :]? $(← Term.exprToSyntax e))
          loop (i + 1) (newDiscrs.push discrNew)
    else
      k newDiscrs
  loop 0 #[]

private abbrev DoMatchAltView := Term.MatchAltView ``doSeq

/--
Like `mkForallFVars (discr.map (·.toExpr)) ty`, but handles non-FVar discriminants by trying to
`kabstract`.

The caller should ensure that `ty` has its MVar dependencies on the discriminants eliminated before
calling this function lest we end up with incomplete abstraction.
-/
private def abstractDiscrs (discrs : Array Expr) (type : Expr) : MetaM Expr := do
  let mut type := type
  for d in discrs.reverse do
    type ← kabstract type d
    let n ← d.fvarId?.casesOn (pure `x) (·.getUserName)
    type := mkForall (← mkFreshUserName n) .default (← inferType d) type
  return type

/--
Like `mkForallFVars (discr.map (·.toExpr)) ty`, but handles non-FVar discriminants by trying to
`kabstract`.

This function also calls `elimMVarDeps` to eliminate MVar dependencies on discriminants before
calling `abstractDiscrs`, so that metavariables are handled correctly.
-/
private def abstractDiscrsM (discrs : Array Expr) (type : Expr) : MetaM Expr := do
  let type ← elimMVarDeps discrs type
  abstractDiscrs discrs type

/-- How much generalization over free variables should happen. -/
inductive FVarGeneralizationPredicate where
  | minimal
  | when (p : LocalDecl → Bool)

def FVarGeneralizationPredicate.satisfies (p : FVarGeneralizationPredicate) (decl : LocalDecl) : Bool :=
  match p with
  | .minimal => false
  | .when p => p decl

private def abstractDiscrsGeneralizingIf (p : FVarGeneralizationPredicate) (discrs : Array Expr) (type : Expr) :
    MetaM (Array FVarId × Expr) := do
  -- `elimMVarDeps` ensures that `Expr.abstract` in `kabstract` is sufficient and exposes otherwise
  -- hidden forward dependencies to `Expr.containsFVar`.
  let type ← elimMVarDeps discrs type
  if p matches .minimal then
    let type ← abstractDiscrs discrs type
    if ← isTypeCorrect type then
      return (#[], type)
  -- Otherwise, we have to generalize even if `p matches .minimal`.
  -- Compute the set of forward dependencies of the discriminants. This is the largest potential
  -- set to generalize over. When `(generalizing := false)`, we will only generalize over a
  -- necessary subset to make the motive type correct.
  -- If there are metavariables involved, we get a lot of weak dependencies; we can simplify the
  -- match prior to constructing the matcher when all metavariables must be assigned.
  let gens ← getFVarsToGeneralize discrs (ignoreLetDecls := true)
  trace[Elab.do.match] "all generalization candidates: {gens.map mkFVar}, type: {type}"
  -- All the continuations are in `ysFVarIds`. Generalizing all of them would be too aggressive
  -- to do by default (and it's the job of `Term.generalizeFVars`), but we need to generalize the
  -- subset that are indices of the types of continuation variables.
  -- We do so by
  -- 1. Go through the locals `ysFVarIds` from back to front
  --   i. We keep the local corresponding to continuation variables
  --   ii. We keep the local that occur in the types of previously kept locals
  -- 2. Abstract `resultType` over the kept locals
  let mut kept := #[]
  for y in gens.reverse do
    let decl ← y.getDecl
    if type.containsFVar y || p.satisfies decl then
      kept := kept.push decl
    else if ← kept.anyM fun k => localDeclDependsOn k y then
      kept := kept.push decl
  let contDiscrDecls := kept.reverse
  let contDiscrs := contDiscrDecls.map (·.toExpr)
  trace[Elab.do.match] "kept: {contDiscrs}"
  let discrs := discrs ++ contDiscrs
  let type ← abstractDiscrs discrs type
  try check type catch ex =>
    throwError "Invalid match expression. Inferred motive is not type correct: {indentExpr type}Please report this as a bug. Message: {ex.toMessageData}"
  return (contDiscrDecls.map (·.fvarId), type)

/--
`replaceFVarsInForallBoundedDomain forallTelescope maxFVars vs es` calls `dom.replaceFVarsM vs es`
on the first `maxFVars` forall domain types `dom` in `forallTelescope`.
Crucially, it does *not* call `replaceFVarsM vs es` on the range; that is what differentiates it
from a simple call to `forallTelescope.replaceFVarsM vs es`.
-/
private def replaceFVarsInForallBoundedDomain (forallTelescope : Expr) (maxFVars : Nat) (vs : Array Expr) (es : Array Expr) : MetaM Expr :=
  loop #[] forallTelescope
where
  loop (fvars : Array Expr) (ty : Expr) : MetaM Expr := do
    let defaultCase := mkForallFVars fvars (ty.instantiateRev fvars)
    if fvars.size < maxFVars then
      match ty with
      | .forallE n d b bi =>
        let d     := d.instantiateRev fvars
        let d ← d.replaceFVarsM vs es -- This is the operation that we want to carry out!
        withLocalDecl n bi d fun fv => do
        loop (fvars.push fv) b
      | _ => defaultCase
    else defaultCase

/--
A generalizer that generalizes muts and continuation variables in addition to calling the regular,
optional `Term.generalizeFVars` generalizer.

Generalization of muts and continuation variables is not optional, just like discriminant refinement.
If we wouldn't refine mut types, we would get errors when assigning the mut tuple types of join
points and `break`.
Example: If we do not generalize `mut s : Fin x` in a match on `x`, we still abstract
`?σ := ?σ' x` (from `jp : resTy → ?σ → m γ`) and later on solve `?σ' x := Fin x` by
`?σ' := fun x => Fin x`; so we'd generalize join point types but not the actual muts, leading to
a failure when synthesizing jump sites.
-/
private def generalizeMutsContsFVars (initialGenFVars : Array FVarId) (mutVars : Array Ident)
    (contGeneralizers : Std.HashMap Name ContFVarGeneralizer) (doGeneralize : Bool) : Term.Generalizer k := fun discrs matchType altViews => do
  let genPredicate decl :=
    doGeneralize || mutVars.any (·.getId == decl.userName) || contGeneralizers.contains decl.userName
  let discrExprs := discrs.map (·.expr)
  -- `matchType` is of the form `∀ds, type`; we want `type[ds := discrs]` and re-do the abstraction
  -- on our terms.
  let resultType := matchType.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs
  let (newGenFVars, matchType) ← abstractDiscrsGeneralizingIf (.when genPredicate) discrExprs resultType
  trace[Elab.do.match] "newGenFVars: {newGenFVars.map mkFVar}, matchType: {matchType}"
  if newGenFVars.isEmpty then
    return { discrs, toClear := initialGenFVars, matchType, altViews, refined := !initialGenFVars.isEmpty }
  let (discrs, altViews) ← Term.addGeneralizedDiscrsAndAlts newGenFVars discrs altViews
  return { discrs, toClear := initialGenFVars ++ newGenFVars, matchType, altViews, refined := true }

/-
  let numOrigDiscrs := discrExprs.size
  -- We keep `resultType` in an instantiated form that scopes over `ds` instead of `∀ds, resultType`.
  -- Otherwise every generalizer would need to `forallBoundedTelescope` again.
  -- However, the original `generalizeFVars` generalizer expects and returns the `∀ds, resultType` form.
  let (discrExprs, resultType) ← do
    trace[Elab.do.match] "before forallBoundedTelescope {numOrigDiscrs}: {(discrExprs, resultType)}"
    forallBoundedTelescope resultType numOrigDiscrs fun ds resultType => do
    trace[Elab.do.match] "after forallBoundedTelescope {numOrigDiscrs}: {(discrExprs, ds, resultType)}"
    genMuts discrExprs ds resultType fun discrExprs ds resultType => do
    trace[Elab.do.match] "after generalizing muts: {(discrExprs, ds, resultType)}"
    genConts discrExprs ds resultType fun discrExprs ds resultType => do
    return (discrExprs, ← mkForallFVars ds resultType)
  trace[Elab.do.match] "after generalizing conts and introducing forall: {(discrExprs, resultType)}"
  let res ← Term.generalizeFVars doGeneralize discrExprs resultType
  trace[Elab.do.match] "generalization result: {res.map fun r => (r.fst.map mkFVar, r.snd)}"
  let newDiscrFVars := discrExprs.drop numOrigDiscrs |>.map Expr.fvarId!
  return match res with
    | some (ys, resultType) => some (newDiscrFVars ++ ys, resultType)
    | none => some (newDiscrFVars, resultType)

where
  genMuts {α} (discrExprs : Array Expr) (ds : Array Expr) (resultType : Expr)
    (k : Array Expr → Array Expr → Expr → TermElabM α) : TermElabM α := do
    let numOrigDiscrs := discrExprs.size
    let rec loop (i : Nat) (discrExprs : Array Expr) (ds : Array Expr) : TermElabM α := do
      if h : i < mutVars.size then
        let mutVar := mutVars[i]
        let decl ← getLocalDeclFromUserName mutVar.getId
        let type ← decl.type.abstractM discrExprs
        if type.hasLooseBVars then
          let type := type.instantiateRev ds
          -- We use `mkFreshUserName` because `elabDiscr` does it, too
          withLocalDeclD (← mkFreshUserName mutVar.getId) type fun mutD => do
            loop (i + 1) (discrExprs.push decl.toExpr) (ds.push mutD)
        else
          loop (i + 1) discrExprs ds
      else
        let mutDiscrExprs := discrExprs.drop numOrigDiscrs
        let mutDs := ds.drop numOrigDiscrs
        trace[Elab.do.match] "mutDiscrExprs: {mutDiscrExprs}, mutDs: {mutDs}, resultType: {resultType}"
        check resultType
        let resultType ← resultType.replaceFVarsM mutDiscrExprs mutDs
        trace[Elab.do.match] "resultType after replacing mutDiscrExprs: {resultType}"
        check resultType
        k discrExprs ds resultType
    loop 0 discrExprs ds

  genConts {α} (discrExprs : Array Expr) (ds : Array Expr) (resultType : Expr)
    (k : Array Expr → Array Expr → Expr → TermElabM α) : TermElabM α := do
    let ysFVarIds ← getFVarsToGeneralize discrExprs (ignoreLetDecls := true)
    trace[Elab.do.match] "all generalization candidates: {ysFVarIds.map mkFVar}"
    -- All the continuations are in `ysFVarIds`. Generalizing all of them would be too aggressive
    -- to do by default (and it's the job of `Term.generalizeFVars`), but we need to generalize the
    -- subset that are indices of the types of continuation variables.
    -- We do so by
    -- 1. Go through the locals `ysFVarIds` from back to front
    --   i. We keep the local corresponding to continuation variables
    --   ii. We keep the local that occur in the types of previously kept locals
    -- 2. Abstract `resultType` over the kept locals
    let mut kept := #[]
    for y in ysFVarIds.reverse do
      let decl ← y.getDecl
      if contGeneralizers.contains decl.userName then
        kept := kept.push decl
      else if ← kept.anyM fun k => localDeclDependsOn k y then
        kept := kept.push decl
    -- This part is very similar to `Term.generalizeFVars`, but we use `replaceFVarsM` instead of
    -- `replaceFVars`.
    let contDiscrDecls := kept.reverse
    let contDiscrExprs := contDiscrDecls.map (·.toExpr)
    let resultType ← mkForallFVars contDiscrExprs resultType
        -- TODO: This is not the right place for the comment below.
        -- `resultType` has the join point result type as range, which contains the `doBlockResultType`.
        -- Usually it does not depend on `mut` variables,
        -- but with control effect lifting (e.g., in a `try` block), it can, because
        --   * The type of a `mut b` may depend on a previous `mut a`
        --   * The `doBlockResultType` may instantiate to a `StateT` wrapper when there's a
        --     reassignment of `b`, so that `doBlockResultType` may depend on `a`.
        -- In this case we want to replace every `a` with the refined `a`.
    -- Simply doing `resultType.replaceFVarsM discrExprs ds` would also generalize the motive even
    -- if it was user-specified. We only want to replace in the types of `contDiscExprs`, which form
    -- a forall telescope. Hence a special operation that leaves the range of the telescope unchanged.
    let resultType ← replaceFVarsInForallBoundedDomain resultType contDiscrExprs.size discrExprs ds
    forallBoundedTelescope resultType contDiscrExprs.size fun contDs resultType => do
    trace[Elab.do.match] "kept: {contDiscrExprs}, contDs: {contDs}, resultType: {resultType}"
    k (discrExprs ++ contDiscrExprs) (ds ++ contDs) resultType
-/
private def elabDoMatchCore (doGeneralize : Bool) (motive? : Option (TSyntax ``motive))
    (discrs : TSyntaxArray ``matchDiscr) (alts : Array DoMatchAltView) (dec : DoElemCont) :
    DoElabM Expr := do
  elabNestedActionsArray discrs fun discrs => do
  elabNonAtomicDiscrs motive? discrs fun discrs => do
--  let (discrs, matchType, altLHSS, isDep, rhss) ← Term.commitIfDidNotPostpone do
  let ⟨discrs, resultMotive, isDep⟩ ← Term.withSynthesize (postpone := .yes) <|
     Term.elabMatchTypeAndDiscrs discrs motive? dec.resultType

  let mi := (← read).monadInfo
  let discrExprs := discrs |>.map (·.expr)
  if (mi.m.abstract discrExprs).hasLooseBVars then
    throwError "Invalid match expression: monad {mi.m} depends on one of the discriminants. \
      This is not supported by the `do` elaborator."

  -- We do not support custom motives or `generalizing := false`. We always produce our own motive
  -- by abstracting the expected type (`dec.resultType`) over the discriminants.
  -- We *do* take the instantiated motive produced by `elabMatchTypeAndDiscrs` though because it
  -- has instantiated metavariables in the result type.
  let resultType := resultMotive.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs

  let discrExprs := discrs.map (·.expr)
  -- The initial generalization pass is minimal, just to make the motive type correct.
  let (genFVars, resultMotive) ← abstractDiscrsGeneralizingIf .minimal discrExprs resultType
  let (discrs, alts) ← Term.addGeneralizedDiscrsAndAlts genFVars discrs alts
  let discrExprs := discrs.map (·.expr)

  let doBlockResultType := (← read).doBlockResultType
  trace[Elab.do.match] "doBlockResultType: {doBlockResultType}"
  let matchType ← mkMonadicType doBlockResultType
  let matchMotive ← abstractDiscrsM discrExprs matchType
  check matchMotive
  trace[Elab.do.match] "discrExprs: {discrExprs}, resultMotive: {resultMotive}, matchMotive: {matchMotive}"
  let returnType := (← getReturnCont).resultType
  trace[Elab.do.match] "returnType: {returnType}"
  let outerLCtx ← getLCtx

  let elabDoMatchRhs (discrs : Array Term.Discr) (patterns : List Match.Pattern) (rhs : TSyntax ``doSeq) (matchMotive : Expr) :
      DoElabM Expr := do
    let discrExprs := discrs.map (·.expr)
    let discrExprs' := (← patterns.mapM (·.toExpr)).toArray
    trace[Elab.do.match] "discriminants after generalization: {discrExprs}, substitute with patterns: {discrExprs'}"

    let doBlockResultMotive ← withLCtx' outerLCtx <| abstractDiscrsM discrExprs doBlockResultType
    check doBlockResultMotive
    let doBlockResultType := doBlockResultMotive.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs'

    let resultMotive ← withLCtx' outerLCtx <| abstractDiscrsM discrExprs resultType
    check resultMotive
    let resultType := resultMotive.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs'

    let returnMotive ← withLCtx' outerLCtx <| abstractDiscrsM discrExprs returnType
    check returnMotive
    let returnType := returnMotive.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs'

    trace[Elab.do.match] "resultType: {resultType}\nreturnType: {returnType}\ndoBlockResultType: {doBlockResultType}\nmatchMotive: {matchMotive}\nrhs: {rhs}"
    let ctx ← read
    let contInfo := { ctx.contInfo.toContInfo with returnCont.resultType := returnType }.toContInfoRef
    let ctx := { ctx with contInfo, doBlockResultType }
    withReader (fun _ => ctx) do elabDoSeq rhs { dec with resultType }

  let mutVars := (← read).mutVars
  let contGeneralizers := (← read).contFVarGeneralizers
  let (discrs, matchType, alts, refined) ← controlAtTermElabM fun runInBase =>
    Term.elabMatchAlts discrs matchMotive alts
    -- Term.elabMatchAlts discrs matchType alts
      (generalizer := generalizeMutsContsFVars genFVars mutVars contGeneralizers doGeneralize)
      (elabRhs := (runInBase <| elabDoMatchRhs · · · ·))
  trace[Elab.do.match] "refined: {refined}, discrs after generalization: {discrs.map (·.expr)}"
  let isDep := isDep || refined
  -- throwError "discrs: {discrs.map (·.expr)}, matchType: {matchType}, isDep: {isDep}"
  /-
   We should not use `synthesizeSyntheticMVarsNoPostponing` here. Otherwise, we will not be
   able to elaborate examples such as:
   ```
   def f (x : Nat) : Option Nat := none

   def g (xs : List (Nat × Nat)) : IO Unit :=
   xs.forM fun x =>
     match f x.fst with
     | _ => pure ()
   ```
   If `synthesizeSyntheticMVarsNoPostponing`, the example above fails at `x.fst` because
   the type of `x` is only available after we process the last argument of `List.forM`.

   We apply pending default types to make sure we can process examples such as
   ```
   let (a, b) := (0, 0)
   ```
  -/
  Term.synthesizeSyntheticMVarsUsingDefault
  let rhss := alts.map Prod.snd
  trace[Elab.do.match] "matchType: {matchType}"
  let altLHSS ← alts.toList.mapM fun alt => do
    let altLHS ← Match.instantiateAltLHSMVars alt.1
    /- Remark: we try to postpone before throwing an error.
       The combinator `commitIfDidNotPostpone` ensures we backtrack any updates that have been performed.
       The quick-check `waitExpectedTypeAndDiscrs` minimizes the number of scenarios where we have to postpone here.
       Here is an example that passes the `waitExpectedTypeAndDiscrs` test, but postpones here.
       ```
        def bad (ps : Array (Nat × Nat)) : Array (Nat × Nat) :=
          (ps.filter fun (p : Prod _ _) =>
            match p with
            | (x, y) => x == 0)
          ++
          ps
       ```
       When we try to elaborate `fun (p : Prod _ _) => ...` for the first time, we haven't propagated the type of `ps` yet
       because `Array.filter` has type `{α : Type u_1} → (α → Bool) → (as : Array α) → optParam Nat 0 → optParam Nat (Array.size as) → Array α`
       However, the partial type annotation `(p : Prod _ _)` makes sure we succeed at the quick-check `waitExpectedTypeAndDiscrs`.
    -/
    withRef altLHS.ref do
      for d in altLHS.fvarDecls do
        if d.hasExprMVar then
          Term.tryPostpone
          withExistingLocalDecls altLHS.fvarDecls do
            Term.runPendingTacticsAt d.type
            if (← instantiateMVars d.type).hasExprMVar then
              Term.throwMVarError m!"Invalid match expression: The type of pattern variable '{d.toExpr}' contains metavariables:{indentExpr d.type}"
      for p in altLHS.patterns do
        if (← Match.instantiatePatternMVars p).hasExprMVar then
          Term.tryPostpone
          withExistingLocalDecls altLHS.fvarDecls do
            Term.throwMVarError m!"Invalid match expression: This pattern contains metavariables:{indentExpr (← p.toExpr)}"
      pure altLHS
--    return (discrs, matchType, altLHSS, isDep, rhss)
  if let some r ← if isDep then pure none else Term.isMatchUnit? altLHSS rhss then
    return r
  else
    let numDiscrs := discrs.size
    let matcherName ← Term.mkAuxName `match
    let matcherResult ← Meta.Match.mkMatcher { matcherName, matchType, discrInfos := discrs.map fun discr => { hName? := discr.h?.map (·.getId) }, lhss := altLHSS }
    Term.reportMatcherResultErrors altLHSS matcherResult
    matcherResult.addMatcher
    let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r (discrs.map (·.expr))
    let r := mkAppN r rhss
    trace[Elab.match] "result: {r}"
    return r

  -- let mγ ← mkMonadicType (← read).doBlockResultType
  -- trace[Elab.do] "doMatch. mγ: {mγ}, dec.resultType: {dec.resultType}, dec.duplicable: {dec.kind matches .duplicable ..}"
  --dec.withDuplicableCont fun mkDec => do
  --  let rec elabMatch i (alts : Array (TSyntax ``matchAlt)) := do
  --    if h : i < alts.size then
  --      match alts[i] with
  --      | `(matchAltExpr| | $patterns,* => $seq) =>
  --        let vars ← getPatternsVarsEx patterns
  --        checkMutVarsForShadowing vars
  --        doElabToSyntax m!"match alternative {patterns.getElems}" (ref := seq) (elabDoSeqRefined ⟨seq⟩ mkDec) fun rhs => do
  --          elabMatch (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
  --      | _ => throwUnsupportedSyntax
  --    else
  --      elabNestedActionsArray discrs.getElems fun discrs => do
  --      withMayElabToJump true do
  --      Term.elabTerm (← `(match $[$gen]? $[$motive]? $[$discrs],* with $alts:matchAlt*)) mγ
  --  elabMatch 0 alts

@[builtin_doElem_elab Lean.Parser.Term.doMatch] partial def elabDoMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[(generalizing := $gen?)]? $(motive?)? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  if let some stxNew ← liftMacroM <| Term.expandMatchAlts? stx then
    return ← Term.withMacroExpansion stx stxNew <| elabDoElem ⟨stxNew⟩ dec
  let gen? := gen?.map (· matches `(trueVal| true))
  let doGeneralize ← Term.checkMotiveCompatible discrs gen? motive?
  elabDoMatchCore doGeneralize motive? discrs (alts.filterMap (Term.getMatchAlt ``doSeq)) dec

@[builtin_doElem_elab Lean.Parser.Term.doMatchExpr] def elabDoMatchExpr : DoElab := fun stx dec => do
  let `(doMatchExpr| match_expr $[(meta := false)%$metaFalseTk?]? $discr with $alts) := stx | throwUnsupportedSyntax
  if metaFalseTk?.isNone then -- i.e., implicitly (meta := true)
    let x ← Term.mkFreshIdent discr
    elabDoIdDecl x none (← `(doElem| instantiateMVars $discr)) (contRef := dec.ref) (declKind := .implDetail) do
      elabDoMatchExprNoMeta x alts dec
  else
    elabNestedActions discr fun discr => do
    elabDoMatchExprNoMeta discr alts dec
where elabDoMatchExprNoMeta (discr : Term) (alts : TSyntax ``matchExprAlts) (dec : DoElemCont) : DoElabM Expr := do
  dec.withDuplicableCont fun mkDec => do
    let rec elabMatch i (altsArr : Array (TSyntax ``matchExprAlt)) := do
      if h : i < altsArr.size then
        match altsArr[i] with
        | `(matchExprAltExpr| | $pattern => $seq) =>
          let vars ← getExprPatternVarsEx pattern
          checkMutVarsForShadowing vars
          doElabToSyntax m!"match_expr alternative {pattern}" (ref := seq) (elabDoSeqRefined ⟨seq⟩ mkDec) fun rhs => do
            elabMatch (i + 1) (altsArr.set i (← `(matchExprAltExpr| | $pattern => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        let elseSeq := alts.raw[1][3]
        doElabToSyntax m!"match_expr else alternative" (ref := elseSeq) (elabDoSeqRefined ⟨elseSeq⟩ mkDec) fun rhs => do
          let alts : TSyntax ``matchExprAlts := ⟨alts.raw.modifyArg 0 fun node => node.setArgs altsArr⟩
          let alts : TSyntax ``matchExprAlts := ⟨alts.raw.modifyArg 1 (·.setArg 3 rhs)⟩
          let mγ ← mkMonadicType (← read).doBlockResultType
          elabNestedActions discr fun discrs => do
          withMayElabToJump true do
          Term.elabTerm (← `(match_expr $discr with $alts)) mγ
    elabMatch 0 (alts.raw[0].getArgs.map (⟨·⟩))

@[builtin_doElem_elab Lean.Parser.Term.doLetExpr] def elabDoLetExpr : DoElab := fun stx dec => do
  let `(doLetExpr| let_expr $pattern:matchExprPat := $rhs:term | $otherwise $[$body?:doSeq]?) := stx | throwUnsupportedSyntax
  let γ := (← read).doBlockResultType
  let mγ ← mkMonadicType γ
  let otherwise ← elabDoSeq otherwise (← DoElemCont.mkPure γ)
  let otherwise ← Term.exprToSyntax otherwise
  let vars ← getExprPatternVarsEx pattern
  let elabBody :=
    match body? with
    | some body => elabDoSeq body dec
    | none => dec.continueWithUnit
  checkMutVarsForShadowing vars
  doElabToSyntax m!"let_expr body of {pattern}" elabBody (ref := dec.ref) fun body => do
    elabNestedActions rhs fun rhs => do
    Term.elabTerm (← `(match_expr $rhs with | $pattern => $body | _ => $otherwise)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doLetMetaExpr] def elabDoLetMetaExpr : DoElab := fun stx dec => do
  let `(doLetMetaExpr| let_expr $pattern:matchExprPat ← $rhs:term | $otherwise $(body?)?) := stx | throwUnsupportedSyntax
  let x ← Term.mkFreshIdent pattern
  elabDoIdDecl x none (← `(doElem| instantiateMVars $rhs)) (contRef := dec.ref) (declKind := .implDetail) do
    elabDoLetExpr (← `(doElem| let_expr $pattern:matchExprPat := $x | $otherwise $(body?)?)) dec
