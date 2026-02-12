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
import Lean.Elab.Do.PatternVar

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

inductive LetOrReassign
  | let (mutTk? : Option Syntax)
  | have
  | reassign

def LetOrReassign.getLetMutTk? (letOrReassign : LetOrReassign) : Option Syntax :=
  match letOrReassign with
  | .let mutTk? => mutTk?
  | _           => none

def LetOrReassign.checkMutVars (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit :=
  match letOrReassign with
  | .reassign => do
    throwUnlessMutVarsDeclared vars
  | _         => checkMutVarsForShadowing vars

def LetOrReassign.registerReassignAliasInfo (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit := do
  if letOrReassign matches .reassign then
    let mutVarDefs := (← read).mutVarDefs
    for var in vars do
      if let some baseId := mutVarDefs[var.getId]? then
        let id := (← getFVarFromUserName var.getId).fvarId!
        if id != baseId then
          pushInfoLeaf <| .ofFVarAliasInfo { userName := var.getId, id, baseId }

def elabDoLetOrReassignWith (hint : MessageData) (letOrReassign : LetOrReassign) (vars : Array Ident)
    (k : DoElabM Expr) (elabBody : (body : Term) → TermElabM Expr) : DoElabM Expr := do
  -- letOrReassign.checkMutVars vars -- Should be done by the caller!
  let elabCont : DoElabM Expr := do
    declareMutVars? letOrReassign.getLetMutTk? vars do
      letOrReassign.registerReassignAliasInfo vars
      k
  doElabToSyntax hint elabCont fun body => elabBody body

def elabWithReassignments (letOrReassign : LetOrReassign) (vars : Array Ident) (k : DoElabM Expr) : DoElabM Expr := do
  declareMutVars? letOrReassign.getLetMutTk? vars do
    letOrReassign.registerReassignAliasInfo vars
    k

partial def elabDoLetOrReassign (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getLetDeclVars decl
  letOrReassign.checkMutVars vars
  -- Some decl preprocessing on the patterns and expected types:
  let decl ←
    if letOrReassign matches .reassign then
      match decl with
      | `(letDecl| $x:ident $[: $xType?]? := $rhs) =>
        -- We use `Term.elabTermEnsuringType` instead of `Term.ensureHasType` to turn type
        -- mismatches into sorrys.
        discard <| Term.elabTermEnsuringType (← `($x:ident)) (← xType?.mapM (Term.elabType ·))
        let xType ← Term.exprToSyntax (← getLocalDeclFromUserName x.getId).type
        `(letDecl| $x:ident : $xType := $rhs)
      | `(letDecl| $pattern:term $[: $xType?]? := $rhs) =>
        let pattern ← match xType? with
          | some xType => `(($pattern : $xType))
          | none       => pure pattern
        -- `Term.withoutErrToSorry` prevents a confusing secondary error message when elaborating
        -- the `match` pattern, where the mut vars potentially get a different type.
        -- Example: `let mut n : Nat := 0; ((n : Char), _) := (false, false)`. We don't want to see
        --          "`n` has type `Char` but was expected to have type `Bool`".
        let e ← Term.withoutErrToSorry <| Term.elabTerm pattern none
        let patType ← Term.exprToSyntax (← inferType e)
        `(letDecl| $pattern:term := ($rhs : $patType))
      | _ => throwError m!"Impossible case in elabDoLetOrReassign. This is an elaborator bug.\n{decl}"
    else
      pure decl

  let mγ ← mkMonadicType (← read).doBlockResultType
  match decl with
  | `(letDecl| $decl:letEqnsDecl) =>
    let declNew ← `(letDecl| $(⟨← liftMacroM <| Term.expandLetEqnsDecl decl⟩):letIdDecl)
    return ← Term.withMacroExpansion decl declNew <| elabDoLetOrReassign letOrReassign declNew dec
  | `(letDecl| $pattern:term $[: $xType?]? := $rhs) =>
    let rhs ← match xType? with | some xType => `(($rhs : $xType)) | none => pure rhs
    let contElab : DoElabM Expr := elabWithReassignments letOrReassign vars dec.continueWithUnit
    doElabToSyntax m!"let body of {pattern}" contElab fun body => do
    -- The infamous MVar postponement trick below popularized by `if` is necessary in Lake.CLI.Main.
    -- We need it because we specify a constant motive, otherwise the `match` elaborator would have postponed.
    let mvar ← Lean.withRef rhs `(?m)
    let term ← `(let_mvar% ?m := $rhs;
                 wait_if_type_mvar% ?m;
                 match (motive := ∀_, $(← Term.exprToSyntax mγ)) $mvar:term with
                 | $pattern:term => $body)
    Term.withMacroExpansion (← getRef) term do Term.elabTermEnsuringType term (some mγ)
  | `(letDecl| $decl:letIdDecl) =>
    let { id, binders, type, value } := Term.mkLetIdDeclView decl
    let id ← if id.isIdent then pure id else Term.mkFreshIdent id (canonical := true)
    -- Only non-`mut` lets will be elaborated as `let`s; `let mut` and reassigns behave as `have`s.
    -- TODO: Perhaps make let muts actually behave as let muts again once the attribute-based inference stuff is in place
    let nondep := !(letOrReassign matches .let none)
    let config := { nondep }
    controlAtTermElabM fun runInBase => do
    Term.withElabLetDeclAux config id binders type value fun x val => runInBase do
      elabWithReassignments letOrReassign vars do
      let body ← dec.continueWithUnit >>= instantiateMVars
      if config.zeta then
        body.replaceFVarsM #[x] #[val]
      else
        mkLetFVars #[x] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
  | _ => throwUnsupportedSyntax

def elabDoArrow (letOrReassign : LetOrReassign) (stx : TSyntax [``doIdDecl, ``doPatDecl]) (dec : DoElemCont) : DoElabM Expr := do
  match stx with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    letOrReassign.checkMutVars #[x]
    -- For plain variable reassignment, we know the expected type of the reassigned variable and
    -- propagate it eagerly via type ascription if the user hasn't provided one themselves:
    let xType? ← match letOrReassign, xType? with
      | .reassign, none =>
        let decl ← getLocalDeclFromUserName x.getId
        some <$> Term.exprToSyntax decl.type
      | _, _ => pure xType?
    elabDoIdDecl x xType? rhs (declareMutVar? letOrReassign.getLetMutTk? x <| dec.continueWithUnit)
      (kind := dec.kind) (contRef := dec.ref)
  | `(doPatDecl| _%$pattern ← $rhs) =>
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    trace[Elab.do] "wildcard arrow: {rhs}, dec.ref: {dec.ref}"
    elabDoIdDecl x none rhs dec.continueWithUnit (kind := dec.kind) (contRef := dec.ref)
  | `(doPatDecl| $pattern:term ← $rhs $[| $otherwise? $(rest?)?]?) =>
    let rest? := rest?.join
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    trace[Elab.do] "pattern let arrow: {pattern} <- {rhs}, dec.ref: {dec.ref}"
    elabDoIdDecl x none rhs (contRef := pattern) (declKind := .implDetail) do
      match letOrReassign, otherwise? with
      | .let mutTk?, some otherwise =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise $(rest?)?)) dec
      | .let mutTk?, _ =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x)) dec
      | .have, some _otherwise =>
        throwUnsupportedSyntax
      | .have, _ =>
        elabDoElem (← `(doElem| have $pattern:term := $x)) dec
      | .reassign, _ =>
        -- otherwise? is always `none`, because there is no `doReassignElse`
        unless rest?.isNone do
          throwError "reassignment with `|` (i.e., \"else clause\") is not supported"
        elabDoElem (← `(doElem| $pattern:term := $x)) dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let $[mut%$mutTk?]? $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign (.let mutTk?) decl dec

@[builtin_doElem_elab Lean.Parser.Term.doHave] def elabDoHave : DoElab := fun stx dec => do
  let `(doHave| have $decl:letDecl) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign .have decl dec

@[builtin_doElem_elab Lean.Parser.Term.doLetRec] def elabDoLetRec : DoElab := fun stx dec => do
  let `(doLetRec| let rec $decls:letRecDecls) := stx | throwUnsupportedSyntax
  let vars ← getLetRecDeclsVars decls
  let mγ ← mkMonadicType (← read).doBlockResultType
  doElabToSyntax m!"let rec body of group {vars}" dec.continueWithUnit fun body => do
    -- Let recs may never have nested actions. We expand just for the sake of error messages.
    -- This suppresses error messages for the let body. Not sure if this is a good call, but it was
    -- the status quo of the legacy `do` elaborator.
    Term.elabTerm (← `(let rec $decls:letRecDecls; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  match stx with
  | `(doReassign| $x:ident $[: $xType?]? := $rhs) =>
    let decl : TSyntax ``letIdDecl ← `(letIdDecl| $x:ident $[: $xType?]? := $rhs)
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    elabDoLetOrReassign .reassign decl dec
  | `(doReassign| $decl:letPatDecl) =>
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    elabDoLetOrReassign .reassign decl dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $pattern := $rhs | $otherwise $(body?)?) := stx | throwUnsupportedSyntax
  let letOrReassign := LetOrReassign.let mutTk?
  let vars ← getPatternVarsEx pattern
  letOrReassign.checkMutVars vars
  let mut body ← body?.getDM `(doSeqIndent|pure PUnit.unit)
  -- In case of `let mut`, we need to re-declare the pattern variables as `let mut`s inside `body`.
  if mutTk?.isSome then
    for var in vars do
      body ← `(doSeqIndent| let mut $var := $var; do $body:doSeqIndent)
  elabDoElem (← `(doElem| match $rhs:term with | $pattern => $body:doSeqIndent | _ => $otherwise:doSeqIndent)) dec

@[builtin_doElem_elab Lean.Parser.Term.doLetArrow] def elabDoLetArrow : DoElab := fun stx dec => do
  let `(doLetArrow| let $[mut%$mutTk?]? $decl) := stx | throwUnsupportedSyntax
  elabDoArrow (.let mutTk?) decl dec

@[builtin_doElem_elab Lean.Parser.Term.doReassignArrow] def elabDoReassignArrow : DoElab := fun stx dec => do
  match stx with
  | `(doReassignArrow| $decl:doIdDecl) =>
    elabDoArrow .reassign decl dec
  | `(doReassignArrow| $decl:doPatDecl) =>
    elabDoArrow .reassign decl dec
  | _ => throwUnsupportedSyntax
