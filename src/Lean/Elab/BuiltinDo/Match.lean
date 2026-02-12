/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.Do.PatternVar
import Lean.Elab.BuiltinDo.Basic
import Lean.Elab.Match
import Lean.Elab.MatchAltView
import Lean.Data.Array
import Init.Omega

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta
open Lean.Meta.Match

private def elabDoSeqWithRefinedType (type : Expr) (doSeq : TSyntax ``doSeq) (dec : DoElemCont) : DoElabM Expr := do
  let newDoBlockResultType ← withNewMCtxDepth do
    let γ ← mkFreshExprMVar (mkSort (← read).monadInfo.u.succ)
    unless ← isDefEqGuarded type (← mkMonadicType γ) do
      throwError "Could not determine dependently-refined result type of `do` block.\n
        Expected type {type} was not def eq to {← mkMonadicType γ}"
    instantiateMVars γ
  trace[Elab.do.match] "newDoBlockResultType: {newDoBlockResultType}"
  -- The `doBlockResultType` *is* the continuation's return type, since it is duplicable.
  let dec := { dec with resultType := newDoBlockResultType }
  withDoBlockResultType newDoBlockResultType (elabDoSeq doSeq dec)

/--
Expand a `doMatch` into a term `match` term. We do this for `match_syntax` and
`match (dependent := true)`. For the latter, the functionality is very restricted to effectively
ban join points.
Reason: In case of a dependent match, it is hard to guarantee that generalization of join points and
`mut` vars will succeed.
The rest of the code in this file is concerned with providing the default, non-dependent `match` in
`do` notation.
-/
private def expandToTermMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[(dependent := $dep?)]? $[(generalizing := $gen?)]? $[(motive := $motive?)]? $discrs:matchDiscr,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  let doBlockResultType := (← read).doBlockResultType
  let mγ ← mkMonadicType doBlockResultType
  -- trace[Elab.do] "expandToTermMatch. mγ: {mγ}, dec.resultType: {dec.resultType}, dec.duplicable: {dec.kind matches .duplicable ..}"
  let info ← inferControlInfoElem stx
  let dependent := dep?.getD ⟨.missing⟩ matches `(trueVal| true)
  trace[Elab.do.match] "expandToTermMatch. dependent: {dependent}, doBlockResultType: {doBlockResultType}, dec.resultType: {dec.resultType}"
  let complexDec := withNewMCtxDepth <| not <$> isDefEqGuarded dec.resultType doBlockResultType
  if ← pure dependent <&&> complexDec then
    throwError "Dependent match is not supported when the result type of the `do` block \
      {indentExpr doBlockResultType}\n is different to the result type of the `match` \
      {indentExpr dec.resultType}"
  dec.withDuplicableCont info fun dec => do
  let rec loop i (alts : Array (TSyntax ``matchAlt)) := do
    if h : i < alts.size then
      match alts[i] with
      | `(matchAltExpr| | $patterns,* => $seq) =>
        let vars ← getPatternsVarsEx patterns
        checkMutVarsForShadowing vars
        let elabRhs (type? : Option Expr) : DoElabM Expr := do
          let (true, some type) := (dependent, type?) | elabDoSeq ⟨seq⟩ dec
          elabDoSeqWithRefinedType type ⟨seq⟩ dec
        doElabToSyntaxWithExpectedType m!"match_syntax alternative {patterns.getElems}"
          (ref := seq) elabRhs fun rhs => do
            loop (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
      | _ => throwUnsupportedSyntax
    else
      Term.elabTerm (← `(match $[(generalizing := $gen?)]? $[(motive := $motive?)]? $[$discrs],* with $alts:matchAlt*)) mγ
  loop 0 alts

-- cf. Term.expandNonAtomicDiscrs?
private def expandNonAtomicDiscrs? (discrs : TSyntaxArray ``matchDiscr) : DoElabM (Option (TSyntaxArray ``matchDiscr)) := do
  -- Recall that
  -- matchDiscr := leading_parser optional (ident >> ":") >> termParser
  if ← discrs.allM fun discr => Term.isAtomicDiscr discr.raw[1] then
    return none
  let mut newDiscrs := #[]
  for discr in discrs do
    let `(matchDiscr| $[$h? :]? $term) := discr | throwUnsupportedSyntax
    if (← Term.isAtomicDiscr term) then
      newDiscrs := newDiscrs.push discr
    else
      trace[Elab.do.match] "elabNonAtomicDiscrs: {term}"
      let e ← Term.elabTerm term none
      let discrNew ← `(matchDiscr| $[$h? :]? $(← Term.exprToSyntax e))
      newDiscrs := newDiscrs.push discrNew
  return some newDiscrs

private def tryPostponeIfDiscrTypeIsMVar (discrs : TSyntaxArray ``matchDiscr) : TermElabM Unit := do
  for discr in discrs do
    let `(matchDiscr| $[$h? :]? $term) := discr | throwUnsupportedSyntax
    let d ← Term.elabTerm term none
    let dType ← inferType d
    trace[Elab.do.match] "discr {d} : {← instantiateMVars dType}"
    Term.tryPostponeIfMVar dType

private def mkUserNameFor (e : Expr) : TermElabM Name := do
  match e with
  | .fvar fvarId => mkFreshUserName (← fvarId.getUserName)
  | _            => Term.mkFreshBinderName

private def elabDiscrs (discrStxs : TSyntaxArray ``matchDiscr) : TermElabM (Array Term.Discr) := do
  let mut discrs := #[]
  for discrStx in discrStxs do
    let `(matchDiscr| $[$h? :]? $term) := discrStx | throwUnsupportedSyntax
    let discr     ← Term.elabTerm term none
    let discr     ← instantiateMVars discr
    let h? ← h?.mapM fun
      | stx@`(_) => return mkIdentFrom stx (← mkFreshUserName `h)
      | stx => return ⟨stx⟩
    discrs := discrs.push { expr := discr, h? }
  return discrs

open Meta.Match (throwIncorrectNumberOfPatternsAt logIncorrectNumberOfPatternsAt) in
private def elabPatterns (patternStxs : Array Syntax) (discrTypes : Array Expr) : TermElabM (Array Expr) :=
  withReader (fun ctx => { ctx with implicitLambda := false }) do
    let mut patterns  := #[]
    let patternStxs ← Term.checkNumPatterns discrTypes.size patternStxs
    for h : idx in *...patternStxs.size do
      let patternStx := patternStxs[idx]
      let discrType := discrTypes[idx]!
      let pattern ← Term.withSynthesize <| Term.withPatternElabConfig <| Term.elabTermEnsuringType patternStx discrType
      patterns  := patterns.push pattern
    return patterns

def withElaboratedLHS {α} (patternVarDecls : Array Term.PatternVarDecl) (patternStxs : Array Syntax)
    (lhsStx : Syntax) (discrTypes : Array Expr) (k : AltLHS → TermElabM α) : TermElabM α := do
  let patterns ← Term.withSynthesize <| withRef lhsStx <| elabPatterns patternStxs discrTypes
  trace[Elab.do.match] "patterns: {patterns}"
  let matchType := discrTypes.foldr (init := mkConst ``Unit) (fun discrType matchType => mkForall `x .default discrType matchType)
  Term.withDepElimPatterns patternVarDecls patterns matchType fun localDecls patterns _matchType => do
    k { ref := lhsStx, fvarDecls := localDecls.toList, patterns := patterns.toList }

private abbrev DoMatchAltView := Term.MatchAltView ``doSeq

private def elabMatchAlt (discrs : Array Term.Discr) (discrTypes : Array Expr)
    (alt : DoMatchAltView) (dec : DoElemCont) : DoElabM (AltLHS × Expr) := withRef alt.ref do
  let (patternVars, alt) ← Term.collectPatternVars alt
  trace[Elab.do.match] "patternVars: {patternVars}"
  controlAtTermElabM fun runInBase => do
  Term.withPatternVars patternVars fun patternVarDecls => do
    withElaboratedLHS patternVarDecls alt.patterns alt.lhs discrTypes fun altLHS =>
      Term.withEqs discrs altLHS.patterns fun eqs =>
        withLocalInstances altLHS.fvarDecls <| runInBase do
          trace[Elab.do.match] "elabMatchAlt: {alt.lhs}"
          let rhs ← elabDoSeq alt.rhs dec
          let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr ++ eqs
          let rhs ← if xs.isEmpty then pure <| mkSimpleThunk rhs else mkLambdaFVars xs rhs
          trace[Elab.do.match] "rhs: {rhs}"
          return (altLHS, rhs)

private def elabMatchAlts (discrs : Array Term.Discr) (alts : Array DoMatchAltView) (dec : DoElemCont) : DoElabM (Expr × Array AltLHS × Array Expr) := do
  let alts ← liftMacroM <| Term.expandMacrosInPatterns alts
  let discrTypes ← discrs.mapM fun discr => do
    let discrType ← inferType discr.expr
    transform (usedLetOnly := true) (← instantiateMVars discrType)
  let (lhss, rhss) ← Array.unzip <$> alts.mapM (elabMatchAlt discrs discrTypes · dec)
  let mut matchType ← mkMonadicType (← read).doBlockResultType
  for discrType in discrTypes.reverse do
    matchType := mkForall `x .default (← instantiateMVars discrType) matchType
  return (matchType, lhss, rhss)

private def compileMatch (discrs : Array Term.Discr) (matchType : Expr) (lhss : List AltLHS)
    (rhss : Array Expr) : DoElabM Expr := do
  let numDiscrs := discrs.size
  let matcherName ← Term.mkAuxName `match
  let matcherResult ← Meta.Match.mkMatcher { matcherName, matchType, lhss, discrInfos := discrs.map fun discr => { hName? := discr.h?.map (·.getId) } }
  Term.reportMatcherResultErrors lhss matcherResult
  matcherResult.addMatcher
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r (discrs.map (·.expr))
  let r := mkAppN r rhss
  trace[Elab.do.match] "result: {r}"
  return r

private def elabDoMatchCore (discrs : TSyntaxArray ``matchDiscr) (alts : Array DoMatchAltView)
    (nondupDec : DoElemCont) : DoElabM Expr := do
  let info ← alts.foldlM (fun info alt => info.alternative <$> inferControlInfoSeq alt.rhs) ControlInfo.pure
  nondupDec.withDuplicableCont info fun dec => do
  trace[Elab.do.match] "discrs: {discrs}, nondupDec.resultType: {nondupDec.resultType}, may postpone: {(← readThe Term.Context).mayPostpone}"
  tryPostponeIfDiscrTypeIsMVar discrs
  let (discrs, matchType, lhss, rhss) ← mapTermElabM Term.commitIfDidNotPostpone do
    let discrs ← Term.withSynthesize <| elabDiscrs discrs
    let (matchType, lhss, rhss) ← elabMatchAlts discrs alts dec
    Term.synthesizeSyntheticMVarsUsingDefault -- Rationale similar to term match elaborator
    let lhss ← Term.instantiateAltLHSs lhss
    return (discrs, matchType, lhss, rhss)
  compileMatch discrs matchType lhss rhss

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
  let `(doMatch| match $[(dependent := $dep)]? $[(generalizing := $gen?)]? $(motive?)? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax

  -- Expand alts
  if let some stxNew ← liftMacroM <| Term.expandMatchAlts? stx then
    return ← Term.withMacroExpansion stx stxNew <| elabDoElem ⟨stxNew⟩ dec

  -- Expand non-atomic discriminants for independent elaboration problems
  if let some discrs ← expandNonAtomicDiscrs? discrs then
    let newStx ← `(doElem| match $[(generalizing := $gen?)]? $(motive?)? $discrs,* with $alts:matchAlt*)
    return ← Term.withMacroExpansion stx newStx <| elabDoElem ⟨newStx⟩ dec

  -- Expand simple matches to `let`
  if let `(matchAltExpr| | $y:ident => $seq) := alts.getD 0 ⟨.missing⟩ then
    if let `(matchDiscr| $discr:term) := discrs.getElems.getD 0 ⟨.missing⟩ then
      if alts.size == 1 && (← Term.isPatternVar y) then
        let newStx ← `(doSeq| let $y:ident := $discr; do $(⟨seq⟩))
        return ← Term.withMacroExpansion stx newStx <| elabDoSeq ⟨newStx⟩ dec

  -- Expand syntax_match to a term match. This is OK because it is never dependent.
  if isSyntaxMatch alts then
    return ← expandToTermMatch stx dec

  -- If the user has explicitly requested a dependent match, we expand to a term match as well.
  if dep.getD ⟨.missing⟩ matches `(trueVal| true) then
    return ← expandToTermMatch stx dec

  if let some stx := motive? then
    throwErrorAt stx "The `do` elaborator does not support custom motives.\nIf you want a dependent match, try `(dependent := true)`.\nIf you want to provide an expected type, do so via type ascription on the bind."
  if let some stx := gen? then
    throwErrorAt stx "The `do` elaborator does not support dependent matches and generalization by default. Try `(dependent := true)`."

  checkMutVarsForShadowing (← getAltsPatternVars alts)
  elabDoMatchCore discrs (alts.filterMap (Term.getMatchAlt ``doSeq)) dec
