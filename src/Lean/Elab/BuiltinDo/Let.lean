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

def getLetIdVars (letId : TSyntax ``letId) : TermElabM (Array Ident) := do
  match letId with
  | `(letId| _) => return #[]
  | `(letId| $id:ident) => return #[id]
  | `(letId| $s:hygieneInfo) => return #[HygieneInfo.mkIdent s `this (canonical := true)]
  | _ => throwError "Not a letId: {letId}"

def getLetIdDeclVars (letIdDecl : TSyntax ``letIdDecl) : TermElabM (Array Ident) := do
  -- def letIdDecl := leading_parser letIdLhs >> " := " >> termParser
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letIdDecl.raw[0]⟩

def getLetPatDeclVars (letPatDecl : TSyntax ``letPatDecl) : TermElabM (Array Ident) := do
  -- def letPatDecl := leading_parser termParser >> pushNone >> optType >> " := " >> termParser
  getPatternVarsEx ⟨letPatDecl.raw[0]⟩

def getLetEqnsDeclVars (letEqnsDecl : TSyntax ``letEqnsDecl) : TermElabM (Array Ident) :=
  -- def letEqnsDecl := leading_parser letIdLhs >> matchAlts
  -- def letIdLhs : Parser := letId >> many (ppSpace >> letIdBinder) >> optType
  -- NB: `letIdLhs` does not introduce a new node
  getLetIdVars ⟨letEqnsDecl.raw[0]⟩

def getLetDeclVars (letDecl : TSyntax ``letDecl) : TermElabM (Array Ident) := do
  match letDecl with
  | `(letDecl| $letIdDecl:letIdDecl) => getLetIdDeclVars letIdDecl
  | `(letDecl| $letPatDecl:letPatDecl) => getLetPatDeclVars ⟨letPatDecl⟩
  | `(letDecl| $letEqnsDecl:letEqnsDecl) => getLetEqnsDeclVars letEqnsDecl
  | _ => throwError "Not a let declaration: {toString letDecl}"

def getLetRecDeclVars (letRecDecl : TSyntax ``letRecDecl) : TermElabM (Array Ident) := do
  -- def letRecDecl := optional docComment >> optional «attributes» >> letDecl >> Termination.suffix
  getLetDeclVars ⟨letRecDecl.raw[2]⟩

def getLetRecDeclsVars (letRecDecls : TSyntax ``letRecDecls) : TermElabM (Array Ident) := do
  -- def letRecDecls := sepBy1 letRecDecl ", "
  let `(letRecDecls| $[$letRecDecls:letRecDecl],*) := letRecDecls | throwUnsupportedSyntax
  let mut allVars := #[]
  for letRecDecl in letRecDecls do
    let vars ← getLetRecDeclVars letRecDecl
    allVars := allVars ++ vars
  return allVars

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

def elabDoLetOrReassign (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (dec : DoElemCont) : DoElabM Expr := do
  let vars ← getLetDeclVars decl
  letOrReassign.checkMutVars vars
  let mγ ← mkMonadicType (← read).doBlockResultType
  -- For plain variable reassignment, we infer the LHS as a term and use that as the expected type
  -- of the RHS:
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
  let contElab : DoElabM Expr := elabWithReassignments letOrReassign vars (dec.continueWithUnit decl)
  doElabToSyntax m!"let body of {vars}" contElab fun body => do
    elabNestedActions decl fun decl => do
    match letOrReassign with
    -- Only non-`mut` lets will be elaborated as `let`s; `let mut` and reassigns behave as `have`s.
    -- TODO: Undo this change once we have the attribute-based inference stuff
    | .let none => Term.elabLetDecl (← `(let $decl:letDecl; $body)) mγ
    | _         => Term.elabHaveDecl (← `(have $decl:letDecl; $body)) mγ

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
    elabDoIdDecl x xType? rhs (declareMutVar? letOrReassign.getLetMutTk? x ∘ dec.continueWithUnit)
      (kind := dec.kind) (contRef := dec.ref)
  | `(doPatDecl| $pattern:term ← $rhs $[| $otherwise?:doSeq $(rest?)?]?) =>
    let rest? := rest?.join
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    elabDoIdDecl x none rhs (contRef := pattern) (declKind := .implDetail) fun _ref => do
      match letOrReassign, otherwise? with
      | .let mutTk?, some otherwise =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise:doSeq $(rest?)?)) dec
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
  doElabToSyntax m!"let rec body of group {vars}" (dec.continueWithUnit decls) fun body => do
    -- Let recs may never have nested actions. We expand just for the sake of error messages.
    -- This suppresses error messages for the let body. Not sure if this is a good call, but it was
    -- the status quo of the legacy `do` elaborator.
    elabNestedActions decls fun decls => do
    Term.elabTerm (← `(let rec $decls:letRecDecls; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  -- And `letIdDeclNoBinders` is a `letIdDecl`. We wrap a `letDecl` node manually.
  let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[stx.raw[0]]⟩
  elabDoLetOrReassign .reassign decl dec

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $pattern := $rhs | $otherwise $(body?)?) := stx | throwUnsupportedSyntax
  let letOrReassign := LetOrReassign.let mutTk?
  let vars ← getPatternVarsEx pattern
  letOrReassign.checkMutVars vars
  let mut body ← body?.getDM `(doSeq|pure PUnit.unit)
  -- In case of `let mut`, we need to re-declare the pattern variables as `let mut`s inside `body`.
  if mutTk?.isSome then
    for var in vars do
      body ← `(doSeq| let mut $var := $var; do $body)
  elabDoElem (← `(doElem| match $rhs:term with | $pattern => $body | _ => $otherwise)) dec

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

@[builtin_macro Lean.Parser.Term.doLetExpr] def expandDoLetExpr : Macro := fun stx => match stx with
  | `(doElem| let_expr $pat:matchExprPat := $discr:term
                | $elseBranch:doSeq
              $thenBranch) =>
    `(doElem| match_expr (meta := false) $discr:term with
              | $pat:matchExprPat => $thenBranch
              | _ => $elseBranch)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doLetMetaExpr] def expandDoLetMetaExpr : Macro := fun stx => match stx with
  | `(doElem| let_expr $pat:matchExprPat ← $discr:term
                | $elseBranch:doSeq
              $thenBranch) =>
    `(doElem| match_expr $discr:term with
              | $pat:matchExprPat => $thenBranch
              | _ => $elseBranch)
  | _ => Macro.throwUnsupported
