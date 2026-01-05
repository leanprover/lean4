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

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_doElem_elab Lean.Parser.Term.doMatch] def elabDoMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  -- We push the `DoElemCont` into each `match` alternative, altering its result type.
  -- We *could* try and propagate the `motive` to `dec.resultType`, but that seems complicated and
  -- is not really what the user thinks will happen. So we do not accept custom motives.
  if let some motive := motive then
    throwErrorAt motive "Specifying a `match` motive is not supported in `do` blocks.\n\
      You can specify `(generalizing := false)` to force a non-dependent match."
  -- We interpret `(generalizing := false)` as a request to perform a non-dependent match.
  -- A dependent match does not make sense without also generalizing the join point type.
  -- See test definition `depMatchNeedsGeneralization`.
  let nonDep :=
    match gen.getD ⟨.missing⟩ with
    | `(generalizingParam| (generalizing := false)) => true
    | _ => false
  -- cf. `expandMatchAlts?`
  let alts : Array (TSyntax ``matchAlt) :=
    if alts.any Term.shouldExpandMatchAlt then
      alts.foldl (init := #[]) fun alts alt =>
        alts ++ (Term.expandMatchAlt alt)
    else
      alts
  let mγ ← mkMonadicType (← read).doBlockResultType
  -- trace[Elab.do] "doMatch. mγ: {mγ}, dec.resultType: {dec.resultType}, dec.duplicable: {dec.kind matches .duplicable ..}"
  dec.withDuplicableCont fun mkDec => do
    let rec elabMatch i (alts : Array (TSyntax ``matchAlt)) := do
      if h : i < alts.size then
        match alts[i] with
        | `(matchAltExpr| | $patterns,* => $seq) =>
          let vars ← getPatternsVarsEx patterns
          checkMutVarsForShadowing vars
          doElabToSyntax m!"match alternative {patterns.getElems}" (ref := seq) (elabDoSeqRefined ⟨seq⟩ mkDec) fun rhs => do
            elabMatch (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
        | _ => throwUnsupportedSyntax
      else
        let motive ← do
          if !nonDep then
            pure none
          else
            let mut motive : Term ← Term.exprToSyntax mγ
            for discr in discrs.getElems do
              motive ← `(∀ _, $motive)
            some <$> `(motive| (motive := $motive))
        elabNestedActionsArray discrs.getElems fun discrs => do
        withMayElabToJump true do
        Term.elabTerm (← `(match $[$gen]? $[$motive]? $[$discrs],* with $alts:matchAlt*)) mγ
    elabMatch 0 alts

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
