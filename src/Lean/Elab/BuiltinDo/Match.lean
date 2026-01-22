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

/--
Expand a `doMatch` into a term `match` term. We do this for `match_syntax` only.
Reason: In case of a dependent match, we cannot guarantee that generalization of join points and
`mut` vars will succeed.
The rest of the code in this file is concerned with copying just enough code from the term `match`
elaborator to guarantee that said generalization will always succeed.
-/
private def expandToTermMatch : DoElab := fun stx dec => do
  let `(doMatch| match $discrs:matchDiscr,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  -- trace[Elab.do] "expandToTermMatch. mγ: {mγ}, dec.resultType: {dec.resultType}, dec.duplicable: {dec.kind matches .duplicable ..}"
  dec.withDuplicableCont fun dec => do
  let rec loop i (alts : Array (TSyntax ``matchAlt)) := do
    if h : i < alts.size then
      match alts[i] with
      | `(matchAltExpr| | $patterns,* => $seq) =>
        let vars ← getPatternsVarsEx patterns
        checkMutVarsForShadowing vars
        doElabToSyntax m!"match_syntax alternative {patterns.getElems}" (ref := seq) (elabDoSeq ⟨seq⟩ dec) fun rhs => do
          loop (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
      | _ => throwUnsupportedSyntax
    else
      elabNestedActionsArray discrs.getElems fun discrs => do
      Term.elabTerm (← `(match $[$discrs],* with $alts:matchAlt*)) mγ
  loop 0 alts

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
    -- trace[Elab.do.match] "abstractDiscrs: {d} {type}"
    type := mkForall (← mkFreshUserName n) .default (← inferType d) type
  return type

/--
Like `mkForallFVars (discr.map (·.toExpr)) ty`, but handles non-FVar discriminants by trying to
`kabstract`.

This function also calls `elimMVarDeps` to eliminate MVar dependencies on discriminants before
calling `abstractDiscrs`, so that metavariables are handled correctly.
-/
private def abstractDiscrsM (discrs : Array Expr) (type : Expr) : MetaM Expr := do
  -- let type ← elimMVarDeps discrs type
  abstractDiscrs discrs type

private def abstractDiscrsGeneralizingIf (generalize? : LocalDecl → Bool) (discrs : Array Expr)
    (type : Expr) : MetaM (Array FVarId × Expr) := do
  -- `elimMVarDeps` ensures that `Expr.abstract` in `kabstract` is sufficient and exposes otherwise
  -- hidden forward dependencies to `Expr.containsFVar`.
  -- let type ← elimMVarDeps discrs type
--  if pred.keepMinimal then
--    let type ← abstractDiscrs discrs type
--    if ← isTypeCorrect type then
--      return (#[], type)
  -- Otherwise, we have to generalize even if `pred.keepMinimal`.
  -- Compute the set of forward dependencies of the discriminants. This is the largest potential
  -- set to generalize over. When `(generalizing := false)`, we will only generalize over a
  -- necessary subset to make the result type and the do block result type type correct (via `pred`).
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
    if generalize? decl then
      kept := kept.push decl
    else if ← kept.anyM fun k => localDeclDependsOn k y then
      kept := kept.push decl
  let contDiscrDecls := kept.reverse
  let contDiscrs := contDiscrDecls.map (·.toExpr)
  trace[Elab.do.match] "kept: {contDiscrs}"
  let discrs := discrs ++ contDiscrs
  let type ← abstractDiscrs discrs type
  try check type catch ex =>
    trace[Elab.do.match] "Inferred motive is type incorrect due to: {ex.toMessageData}"
    throwError "Invalid match expression. Inferred motive is not type correct: {indentExpr type}"
  return (contDiscrDecls.map (·.fvarId), type)

/--
A generalizer that generalizes muts in addition to the regular, optional FVar generalization procedure.

Generalization of muts is not optional, just like discriminant refinement.
If we wouldn't refine mut types, we would get errors when assigning the mut tuple types of join
points and `break`.
Example: If we do not generalize `mut s : Fin x` in a match on `x`, we still abstract
`?σ := ?σ' x` (from `jp : resTy → ?σ → m γ`) and later on solve `?σ' x := Fin x` by
`?σ' := fun x => Fin x`; so we'd generalize join point types but not the actual muts, leading to
a failure when synthesizing jump sites.
-/
private def generalizeMutsContsFVars (initialGenFVars : Array FVarId) (mutVars : Array Ident)
    (contFVars : Std.HashSet Name) (doGeneralize : Bool) : Term.Generalizer k := fun discrs matchType altViews => do
  let generalize? decl :=
    doGeneralize || matchType.containsFVar decl.fvarId || mutVars.any (·.getId == decl.userName) || contFVars.contains decl.userName
  let discrExprs := discrs.map (·.expr)
  -- `matchType` is of the form `∀ds, type`; we want `type[ds := discrs]` and re-do the abstraction
  -- on our terms.
  let resultType := matchType.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs
  let (newGenFVars, matchType) ← abstractDiscrsGeneralizingIf generalize? discrExprs resultType
  if newGenFVars.isEmpty then
    return { discrs, toClear := initialGenFVars, matchType, altViews, refined := !initialGenFVars.isEmpty }
  let (discrs, altViews) ← Term.addGeneralizedDiscrsAndAlts newGenFVars discrs altViews
  return { discrs, toClear := initialGenFVars ++ newGenFVars, matchType, altViews, refined := true }

private def elabDoMatchCore (doGeneralize : Bool) (motive? : Option (TSyntax ``motive))
    (discrs : TSyntaxArray ``matchDiscr) (alts : Array DoMatchAltView) (nondupDec : DoElemCont) :
    DoElabM Expr := do
  nondupDec.withDuplicableCont fun dec => do
  let doBlockResultType := (← read).doBlockResultType
  let mγ ← mkMonadicType doBlockResultType
  elabNestedActionsArray discrs fun discrs => do
  elabNonAtomicDiscrs motive? discrs fun discrs => do
  trace[Elab.do.match] "discrs: {discrs}, nondupDec.resultType: {nondupDec.resultType}"
  Term.tryPostponeIfDiscrTypeIsMVar motive? discrs
  let (discrs, matchType, alts, isDep) ← mapTermElabM Term.commitIfDidNotPostpone do
    let ⟨discrs, resultMotive, isDep⟩ ← Term.withSynthesize <|
       Term.elabMatchTypeAndDiscrs discrs motive? nondupDec.resultType

    let mi := (← read).monadInfo
    let discrExprs := discrs |>.map (·.expr)
    if (mi.m.abstract discrExprs).hasLooseBVars then
      throwError "Invalid match expression: monad {mi.m} depends on one of the discriminants. \
        This is not supported by the `do` elaborator."

    Term.synthesizeSyntheticMVars -- using default would be too strong here; omitting it would be too weak to provoke the bad discrminant refinement error
    -- We do not support custom motives or `generalizing := false`. We always produce our own motive
    -- by abstracting the expected type (`dec.resultType`) over the discriminants.
    -- We *do* take the instantiated motive produced by `elabMatchTypeAndDiscrs` though because it
    -- has instantiated metavariables in the result type.
    let resultType := resultMotive.getForallBodyMaxDepth discrExprs.size |>.instantiateRev discrExprs
    -- The initial generalization pass is minimal, just to make the motive type correct.
    -- We test for both the motive and the do block result type; otherwise we
    -- let doBlockResultType ← elimMVarDeps discrExprs doBlockResultType
    let generalize? decl := resultType.containsFVar decl.fvarId || doBlockResultType.containsFVar decl.fvarId
    let (genFVars, resultMotive) ← abstractDiscrsGeneralizingIf generalize? discrExprs resultType
    let (discrs, alts) ← Term.addGeneralizedDiscrsAndAlts genFVars discrs alts
    let discrExprs := discrs.map (·.expr)

    let doBlockResultType := (← read).doBlockResultType
    trace[Elab.do.match] "doBlockResultType: {doBlockResultType}"
    let matchType ← mkMonadicType doBlockResultType
    let matchMotive ← abstractDiscrsM discrExprs matchType
    trace[Elab.do.match] "discrExprs: {discrExprs}, matchMotive: {matchMotive}"
    check matchMotive
    trace[Elab.do.match] "discrExprs: {discrExprs}, resultMotive: {resultMotive}, matchMotive: {matchMotive}"
    let returnType := (← getReturnCont).resultType
    trace[Elab.do.match] "returnType: {returnType}"
    let outerLCtx ← getLCtx

    let outerRef ← getRef
    let haveCheckedBadDiscriminantRefinement ← IO.mkRef false
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
      unless (← haveCheckedBadDiscriminantRefinement.get) do
        -- We have not checked for bad refined discriminants yet; do it now, but only once.
        haveCheckedBadDiscriminantRefinement.set true
        let motiveDependent := [doBlockResultMotive, resultMotive, returnMotive]
          |>.any (·.getForallBodyMaxDepth discrExprs.size |>.hasLooseBVars)
        let hasGeneralizedContVars ← (← read).contFVars.toArray.anyM fun contFVar => do
          let some decl := outerLCtx.findFromUserName? contFVar | return false
          return discrs.any (·.expr == decl.toExpr)
        if nondupDec.kind matches .nonDuplicable && motiveDependent && !hasGeneralizedContVars then
          -- The example here is
          -- example (x : Nat) (h : x = 3) := Id.run (α := Fin (x + 3)) do
          --   let y : Fin (x + 3) <- match h with | rfl => pure ⟨0, by grind⟩
          --   return ⟨y - 1, by grind⟩
          -- Need to add `x` as discriminant to fix.
          throwErrorAt outerRef "The inferred match motive {indentExpr returnType}\nor the monadic \
            result type {indentExpr matchMotive}\nhad occurrences of free variables that depend on \
            the discriminants, but no continuation variables were generalized.\n\
            This is not supported by the `do` elaborator. Supply missing indices as disciminants to fix this."
      withReader (fun _ => ctx) do elabDoSeq rhs { dec with resultType }

    let mutVars := (← read).mutVars
    let contFVars := (← read).contFVars
    let (discrs, matchType, alts, refined) ←
      controlAtTermElabM fun runInBase => do
      Term.elabMatchAlts discrs matchMotive alts
      -- Term.elabMatchAlts discrs matchType alts
        (generalizer := generalizeMutsContsFVars genFVars mutVars contFVars doGeneralize)
        (elabRhs := (runInBase <| elabDoMatchRhs · · · ·))
    trace[Elab.do.match] "refined: {refined}, discrs after generalization: {discrs.map (·.expr)}"
    let isDep := isDep || refined
    return (discrs, matchType, alts, isDep)

  let finishMatchExpr : Term.FixedTermElab := fun _ => do
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
  Term.elabToSyntax finishMatchExpr (Term.elabTerm · mγ)

def isSyntaxMatch (alts : Array (TSyntax ``matchAlt)) : Bool :=
  alts.any (fun alt =>
    match alt with
    | `(matchAltExpr| | $pats,* => $_) =>
      pats.getElems.any (fun
      | `($_@$pat) => pat.raw.isQuot
      | pat        => pat.raw.isQuot)
    | _ => false)

def getAltsPatternVars (alts : TSyntaxArray ``matchAlt) : TermElabM (Array Ident) := do
  let mut vars := #[]
  for alt in alts do
    let `(matchAltExpr| | $patterns,* => $_) := alt | throwUnsupportedSyntax
    let patternVars ← getPatternsVarsEx patterns
    vars := vars ++ patternVars
  return vars

@[builtin_doElem_elab Lean.Parser.Term.doMatch] partial def elabDoMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[(generalizing := $gen?)]? $(motive?)? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  if let some stxNew ← liftMacroM <| Term.expandMatchAlts? stx then
    return ← Term.withMacroExpansion stx stxNew <| elabDoElem ⟨stxNew⟩ dec
  if isSyntaxMatch alts then
    return ← expandToTermMatch stx dec
  if let `(matchAltExpr| | $y:ident => $seq) := alts.getD 0 ⟨.missing⟩ then
    if let `(matchDiscr| $[$_ :]? $discr) := discrs.getElems.getD 0 ⟨.missing⟩ then
      if alts.size == 1 && (← Term.isPatternVar y) then
        let newStx ← `(doSeq| let $y:ident := $discr; do $(⟨seq⟩))
        return ← Term.withMacroExpansion stx newStx <| elabDoSeq ⟨newStx⟩ dec

  if let some motive? := motive? then
    throwErrorAt motive? "The `do` elaborator does not support custom motives. Try type ascription to provide expected types."
  let gen? := gen?.map (· matches `(trueVal| true))
  let doGeneralize := gen?.getD true
  checkMutVarsForShadowing (← getAltsPatternVars alts)
  elabDoMatchCore doGeneralize motive? discrs (alts.filterMap (Term.getMatchAlt ``doSeq)) dec

@[builtin_doElem_elab Lean.Parser.Term.doMatchExpr] def elabDoMatchExpr : DoElab := fun stx dec => do
  let `(doMatchExpr| match_expr $[(meta := false)%$metaFalseTk?]? $discr with $alts) := stx | throwUnsupportedSyntax
  if metaFalseTk?.isNone then -- i.e., implicitly (meta := true)
    let x ← Term.mkFreshIdent discr
    elabDoIdDecl x none (← `(doElem| instantiateMVars $discr)) (contRef := dec.ref) (declKind := .implDetail) fun _ref => do
      elabDoMatchExprNoMeta x alts dec
  else
    elabNestedActions discr fun discr => do
    elabDoMatchExprNoMeta discr alts dec
where elabDoMatchExprNoMeta (discr : Term) (alts : TSyntax ``matchExprAlts) (dec : DoElemCont) : DoElabM Expr := do
  dec.withDuplicableCont fun dec => do
    let rec elabMatch i (altsArr : Array (TSyntax ``matchExprAlt)) := do
      if h : i < altsArr.size then
        match altsArr[i] with
        | `(matchExprAltExpr| | $pattern => $seq) =>
          let vars ← getExprPatternVarsEx pattern
          checkMutVarsForShadowing vars
          doElabToSyntax m!"match_expr alternative {pattern}" (ref := seq) (elabDoSeq ⟨seq⟩ dec) fun rhs => do
            elabMatch (i + 1) (altsArr.set i (← `(matchExprAltExpr| | $pattern => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        let elseSeq := alts.raw[1][3]
        doElabToSyntax m!"match_expr else alternative" (ref := elseSeq) (elabDoSeq ⟨elseSeq⟩ dec) fun rhs => do
          let alts : TSyntax ``matchExprAlts := ⟨alts.raw.modifyArg 0 fun node => node.setArgs altsArr⟩
          let alts : TSyntax ``matchExprAlts := ⟨alts.raw.modifyArg 1 (·.setArg 3 rhs)⟩
          let mγ ← mkMonadicType (← read).doBlockResultType
          elabNestedActions discr fun discrs => do
          Term.elabTerm (← `(match_expr $discr with $alts)) mγ
    elabMatch 0 (alts.raw[0].getArgs.map (⟨·⟩))
