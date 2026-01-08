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

private abbrev DoMatchAltView := Term.MatchAltView ``doSeq

private def elabDoMatchCore (doGeneralize : Bool) (motive? : Option (TSyntax ``motive))
    (discrs : TSyntaxArray ``matchDiscr) (alts : Array DoMatchAltView) (dec : DoElemCont) :
    DoElabM Expr := do
  elabNestedActionsArray discrs fun discrs => do
--  let (discrs, matchType, altLHSS, isDep, rhss) ← Term.commitIfDidNotPostpone do
  let ⟨discrs, resultMotive, isDep⟩ ← Term.elabMatchTypeAndDiscrs discrs motive? dec.resultType
  trace[Elab.do.match] "resultMotive: {resultMotive}"

  let mi := (← read).monadInfo
  let discrExprs := discrs |>.map (·.expr)
  let indices := discrExprs |>.map (·.isFVar)
  let discrExprs' := indices.mask discrExprs
  if (mi.m.abstract discrExprs').hasLooseBVars then
    throwError "Invalid match expression: monad {mi.m} depends on one of the discriminants. \
      This is not supported by the `do` elaborator."

  let doBlockResultType := (← read).doBlockResultType
  let matchType ← mkForallFVars discrExprs (← mkMonadicType doBlockResultType)
  trace[Elab.do.match] "matchType: {matchType}"

  let elabDoMatchRhs (patterns : List Match.Pattern) (rhs : TSyntax ``doSeq) (matchType : Expr) :
      DoElabM Expr := do
    let discrExprs' := (← patterns.mapM (·.toExpr)).toArray
    let resultType ← forallBoundedTelescope resultMotive discrs.size fun xs resultType => do
      resultType.replaceFVarsM xs discrExprs'
    let doBlockResultType ← doBlockResultType.replaceFVarsM discrExprs discrExprs'
    trace[Elab.do.match] "rhs: {rhs}, resultType: {resultType}, doBlockResultType: {doBlockResultType}"
    withDoBlockResultType doBlockResultType do
      elabDoSeq rhs { dec with resultType := resultType }
  let (discrs, matchType, alts, refined) ← controlAtTermElabM fun runInBase =>
    Term.elabMatchAlts (runInBase <| elabDoMatchRhs · · ·) doGeneralize discrs matchType alts
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
  let doGeneralize ← Term.checkMotiveCompatible discrs.getElems gen? motive?
  elabDoMatchCore doGeneralize motive? discrs.getElems (alts.filterMap (Term.getMatchAlt ``doSeq)) dec

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
