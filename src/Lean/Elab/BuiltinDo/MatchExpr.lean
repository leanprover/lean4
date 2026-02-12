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
import Init.Omega

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_macro Lean.Parser.Term.doLetExpr] def expandDoLetExpr : Macro := fun stx => match stx with
  | `(doElem| let_expr $pat:matchExprPat := $discr:term
                | $elseBranch
              $thenBranch) =>
    `(doElem| match_expr (meta := false) $discr:term with
              | $pat:matchExprPat => $thenBranch:doSeqIndent
              | _ => $elseBranch:doSeqIndent)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doLetMetaExpr] def expandDoLetMetaExpr : Macro := fun stx => match stx with
  | `(doElem| let_expr $pat:matchExprPat ← $discr:term
                | $elseBranch
              $thenBranch) =>
    `(doElem| match_expr $discr:term with
              | $pat:matchExprPat => $thenBranch:doSeqIndent
              | _ => $elseBranch:doSeqIndent)
  | _ => Macro.throwUnsupported

@[builtin_doElem_elab Lean.Parser.Term.doMatchExpr] def elabDoMatchExpr : DoElab := fun stx dec => do
  let `(doMatchExpr| match_expr $[(meta := false)%$metaFalseTk?]? $discr with $alts) := stx | throwUnsupportedSyntax
  let info ← inferControlInfoElem stx
  if metaFalseTk?.isNone then -- i.e., implicitly (meta := true)
    let x := mkIdentFrom discr (← mkFreshUserName `__x)
    elabDoIdDecl x none (← `(doElem| instantiateMVarsIfMVarApp $discr)) (contRef := dec.ref) do
      elabDoMatchExprNoMeta info x alts dec
  else
    elabDoMatchExprNoMeta info discr alts dec
where elabDoMatchExprNoMeta (info : ControlInfo) (discr : Term) (alts : TSyntax ``matchExprAlts) (dec : DoElemCont) : DoElabM Expr := do
  dec.withDuplicableCont info fun dec => do
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
          Term.elabTerm (← `(match_expr $discr with $alts)) mγ
    elabMatch 0 (alts.raw[0].getArgs.map (⟨·⟩))
