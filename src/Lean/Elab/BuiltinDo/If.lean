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

@[builtin_doElem_elab Lean.Parser.Term.doIf] def elabDoIf : DoElab := fun stx dec => do
  let `(doIf|if $cond:doIfCond then $thenSeq $[else if $conds:doIfCond then $thenSeqs]* $[else $elseSeq?]?) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  dec.withDuplicableCont fun mkDec => do
  withMayElabToJump true do
  let doElemToTerm doElem := doElabToSyntax m!"if branch {doElem}" (ref := doElem) (elabDoSeqRefined doElem mkDec)
  let condsThens := #[(cond, thenSeq)] ++ Array.zip conds thenSeqs
  let rec loop (i : Nat) : DoElabM Expr := do
    if h : i < condsThens.size then
      let (cond, thenSeq) := condsThens[i]
      doElemToTerm thenSeq fun then_ => do
      doElabToSyntax m!"else branch of {cond}" (loop (i + 1)) fun else_ => do
      match cond with
      | `(doIfCond|$cond) =>
        elabNestedActions cond fun cond => do
        Term.elabTerm (← `(if $cond then $then_ else $else_)) mγ
      | `(doIfCond|_ : $cond) =>
        elabNestedActions cond fun cond => do
        Term.elabTerm (← `(if _ : $cond then $then_ else $else_)) mγ
      | `(doIfCond|$h:ident : $cond) =>
        elabNestedActions cond fun cond => do
        Term.elabTerm (← `(if $h:ident : $cond then $then_ else $else_)) mγ
      | `(doIfCond|let $pat := $d) =>
        checkMutVarsForShadowing (← getPatternVarsEx pat)
        elabNestedActions d fun d => do
        Term.elabTerm (← `(match $d:term with | $pat => $then_ | _ => $else_)) mγ
      | `(doIfCond|let $pat ← $rhs) =>
        checkMutVarsForShadowing (← getPatternVarsEx pat)
        let x ← Term.mkFreshIdent pat
        elabDoIdDecl x none (← `(doElem| $rhs:term)) (contRef := pat) (declKind := .implDetail) do
          Term.elabTerm (← `(match $x:term with | $pat => $then_ | _ => $else_)) mγ
      | _ => throwUnsupportedSyntax
    else
      match elseSeq? with
      | some elseSeq => elabDoSeqRefined elseSeq mkDec
      | none         => elabWithRefinement mkDec DoElemCont.continueWithUnit
  loop 0
