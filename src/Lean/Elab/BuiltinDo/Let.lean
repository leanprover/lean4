/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
meta import Init.Data.Erased
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.Basic
import Lean.Elab.Do.PatternVar

public section

-- The `ghost` doElem quotations below need the current stage's parser until stage0 catches up.
set_option internal.parseQuotWithCurrentStage true

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

inductive LetOrReassign
  | let (mutTk? : Option Syntax) (ghost : Bool)
  | have
  | reassign

def LetOrReassign.getLetMutTk? (letOrReassign : LetOrReassign) : Option Syntax :=
  match letOrReassign with
  | .let mutTk? _ => mutTk?
  | _             => none

def LetOrReassign.isGhostDecl (letOrReassign : LetOrReassign) : Bool :=
  match letOrReassign with
  | .let _ ghost => ghost
  | _            => false

def isGhost (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Bool := do
  match letOrReassign with
  | .let _ ghost => return ghost
  | .reassign    =>
    let some v := vars[0]? | return false
    let some mv ← findMutVar? v.getId | return false
    return mv.ghost
  | _            => return false

def LetOrReassign.checkMutVars (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit :=
  match letOrReassign with
  | .reassign => do
    throwUnlessMutVarsDeclared vars
    -- Reassigning a ghost variable wraps its value, which only the single-variable form can do.
    unless vars.size == 1 do
      for v in vars do
        if ((← findMutVar? v.getId).map (·.ghost)).getD false then
          throwErrorAt v "a ghost variable takes a plain reassignment, as in `{v.getId} := e`"
  | _         => checkMutVarsForShadowing vars

def LetOrReassign.registerReassignAliasInfo (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit := do
  if letOrReassign matches .reassign then
    for var in vars do
      registerMutVarAlias var.getId

def elabWithReassignments (letOrReassign : LetOrReassign) (vars : Array Ident) (k : DoElabM Expr) : DoElabM Expr := do
  declareMutVars? letOrReassign.getLetMutTk? vars letOrReassign.isGhostDecl do
    letOrReassign.registerReassignAliasInfo vars
    if ← isGhost letOrReassign vars then
      vars.foldr (init := k) withErasedProj
    else
      k

private def pushTypeIntoReassignment (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl) : TermElabM (TSyntax ``letDecl) := do
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

private def checkLetConfigInDo (config : Term.LetConfig) : DoElabM Unit := do
  if config.postponeValue then
    throwError "`+postponeValue` is not supported in `do` blocks"
  if config.generalize then
    throwError "`+generalize` is not supported in `do` blocks"

/--
Wrap a ghost decl `ghost x : t := e` as `let x : Erased t := Erased.mk e`, similarly for
reassigments.
-/
private def wrapGhostDecl (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl) :
    DoElabM (TSyntax ``letDecl) := do
  let `(letDecl| $x:ident $[: $t?]? := $e) := decl
    | throwErrorAt decl "`ghost` takes a variable"
  match letOrReassign with
  | .reassign =>
    let t ← Term.exprToSyntax (← getLocalDeclFromUserName x.getId).type
    let e ← match t? with
      | some tAsc => `(Erased.mk ($e : $tAsc))
      | none      => `(Erased.mk ($e : $t))
    `(letDecl| $x:ident : Erased $t := $e)
  | _ =>
    match t? with
    | some t => `(letDecl| $x:ident : Erased $t := Erased.mk $e)
    | none   => `(letDecl| $x:ident := Erased.mk $e)

partial def elabDoLetOrReassign (config : Term.LetConfig) (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (tk : Syntax) (dec : DoElemCont) : DoElabM Expr := do
  checkLetConfigInDo config
  let vars ← getLetDeclVars decl
  letOrReassign.checkMutVars vars
  let dec ← dec.ensureUnitAt tk
  let isGhost ← isGhost letOrReassign vars
  -- Some decl preprocessing on the patterns and expected types:
  let decl ← if isGhost then wrapGhostDecl letOrReassign decl
             else pushTypeIntoReassignment letOrReassign decl
  let mγ ← mkMonadApp (← read).doBlockResultType
  match decl with
  | `(letDecl| $decl:letEqnsDecl) =>
    let declNew ← `(letDecl| $(⟨← liftMacroM <| Term.expandLetEqnsDecl decl⟩):letIdDecl)
    return ← Term.withMacroExpansion decl declNew <| elabDoLetOrReassign config letOrReassign declNew tk dec
  | `(letDecl| $pattern:term $[: $xType?]? := $rhs) =>
    let rhs ← match xType? with | some xType => `(($rhs : $xType)) | none => pure rhs
    let contElab : DoElabM Expr := elabWithReassignments letOrReassign vars dec.continueWithUnit
    doElabToSyntax m!"let body of {pattern}" contElab fun body => do
    -- The infamous MVar postponement trick below popularized by `if` is necessary in Lake.CLI.Main.
    -- We need it because we specify a constant motive, otherwise the `match` elaborator would have postponed.
    let mvar ← Lean.withRef rhs `(?m)
    let term ← if let some h := config.eq? then
      `(let_mvar% ?m := $rhs;
        wait_if_type_mvar% ?m;
        match $h:ident : $mvar:term with
        | $pattern:term => $body)
    else
      `(let_mvar% ?m := $rhs;
        wait_if_type_mvar% ?m;
        match (motive := ∀_, $(← Term.exprToSyntax mγ)) $mvar:term with
        | $pattern:term => $body)
    Term.withMacroExpansion (← getRef) term do Term.elabTermEnsuringType term (some mγ)
  | `(letDecl| $decl:letIdDecl) =>
    let { id, binders, type, value } := Term.mkLetIdDeclView decl
    let id ← if id.isIdent then pure id else Term.mkFreshIdent id (canonical := true)
    let nondep := config.nondep || letOrReassign matches .have
    -- Only non-`mut` lets will be elaborated as `let`s; `let mut` and reassigns behave as `have`s.
    -- See `elabLetDeclAux` for rationale.
    let (type, val) ← Term.elabBindersEx binders fun xs => do
      let fvars := xs.map (·.2) -- discard binders
      let ty ← Term.withSynthesize (postpone := .partial) <| Term.elabType type
      let letMsg := if nondep then "have" else "let"
      Term.registerCustomErrorIfMVar ty type m!"failed to infer `{letMsg}` declaration type"
      Term.registerLevelMVarErrorExprInfo ty type m!"failed to infer universe levels in `{letMsg}` declaration type"
      let lctx' := fvars.foldl (init := ← getLCtx) fun lctx fvar =>
        lctx.modifyLocalDecl fvar.fvarId! (fun decl => decl.setType decl.type.cleanupAnnotations)
      let val ← withLCtx' lctx' do
        let val ← Term.elabTermEnsuringType value ty
        mkLambdaFVars fvars val (usedLetOnly := false)
      let ty ← mkForallFVars fvars ty
      pure (ty, val)
    let kind := .ofBinderName id.getId
    trace[Elab.let.decl] "{id.getId} : {type} := {val}"
    withLetDecl id.getId (kind := kind) type val (nondep := nondep) fun x => do
      Term.addLocalVarInfo id x
      match config.eq? with
      | none =>
        let body ← elabWithReassignments letOrReassign vars dec.continueWithUnit
        if config.zeta then
          pure <| (← body.abstractM #[x]).instantiate1 val
        else
          mkLetFVars #[x] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
      | some h =>
        let hTy ← mkEq x val
        withLetDecl h.getId hTy (← mkEqRefl x) (nondep := true) fun h' => do
          Term.addLocalVarInfo h h'
          let body ← elabWithReassignments letOrReassign vars dec.continueWithUnit
          if config.zeta then
            pure <| (← body.abstractM #[x, h']).instantiateRev #[val, ← mkEqRefl val]
          else if nondep then
            let f ← mkLambdaFVars #[x, h'] body
            return mkApp2 f val (← mkEqRefl val)
          else
            mkLetFVars #[x, h'] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
  | _ => throwUnsupportedSyntax

def elabDoArrow (mutTk? : Option Syntax) (ghost : Bool) (stx : TSyntax [``doIdDecl, ``doPatDecl])
    (tk : Syntax) (dec : DoElemCont) : DoElabM Expr := do
  match stx with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    checkMutVarsForShadowing #[x]
    let dec ← dec.ensureUnitAt tk
    elabDoIdDecl x xType? rhs (declareMutVar? mutTk? x ghost <| dec.continueWithUnit)
      (kind := dec.kind)
  | `(doPatDecl| _%$pattern $[: $patType?]? ← $rhs) =>
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    let dec ← dec.ensureUnitAt tk
    elabDoIdDecl x patType? rhs dec.continueWithUnit (kind := dec.kind)
  | `(doPatDecl| $pattern:term $[: $patType?]? ← $rhs $[| $otherwise? $(rest?)?]?) =>
    let rest? := rest?.join
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    elabDoIdDecl x patType? rhs do
      match otherwise? with
      | some otherwise =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise $(rest?)?)) dec
      | none =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x)) dec
  | _ => throwUnsupportedSyntax

private def getLetConfigAndCheckMut (letConfigStx : TSyntax ``Parser.Term.letConfig)
    (mutTk? : Option Syntax) (initConfig : Term.LetConfig := {}) : DoElabM Term.LetConfig := do
  if mutTk?.isSome && !letConfigStx.raw[0].getArgs.isEmpty then
    throwErrorAt letConfigStx "configuration options are not allowed with `let mut`"
  Term.mkLetConfig letConfigStx initConfig

@[builtin_doElem_elab Lean.Parser.Term.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let%$tk $[mut%$mutTk?]? $config:letConfig $decl:letDecl) := stx | throwUnsupportedSyntax
  let config ← getLetConfigAndCheckMut config mutTk?
  elabDoLetOrReassign config (.let mutTk? false) decl tk dec

@[builtin_doElem_elab Lean.Parser.Term.doGhost] def elabDoGhost : DoElab := fun stx dec => do
  let `(doGhost| ghost%$tk $[mut%$mutTk?]? $x:ident $[: $t?]? := $e) := stx | throwUnsupportedSyntax
  elabDoLetOrReassign {} (.let mutTk? true) (← `(letDecl| $x:ident $[: $t?]? := $e)) tk dec

@[builtin_macro Lean.Parser.Term.doGhostArrow] def expandDoGhostArrow : Macro := fun stx => do
  match stx with
  | `(doGhostArrow| ghost%$tk $[mut%$mutTk?]? $x:ident $[: $t?]? ← $rhs) =>
    let y := mkIdentFrom x (← MonadQuotation.addMacroScope `__x)
    let letElem ← `(doElem| let $y:ident $[: $t?]? ← $rhs)
    let ghostElem : TSyntax `doElem := ⟨(← `(doGhost| ghost%$tk $[mut%$mutTk?]? $x:ident := $y)).raw⟩
    `(doElem| do $letElem:doElem; $ghostElem:doElem)
  | _ => Macro.throwUnsupported

@[builtin_doElem_elab Lean.Parser.Term.doHave] def elabDoHave : DoElab := fun stx dec => do
  let `(doHave| have%$tk $config:letConfig $decl:letDecl) := stx | throwUnsupportedSyntax
  let config ← Term.mkLetConfig config { nondep := true }
  elabDoLetOrReassign config .have decl tk dec

@[builtin_doElem_elab Lean.Parser.Term.doLetRec] def elabDoLetRec : DoElab := fun stx dec => do
  let `(doLetRec| let%$tk rec $decls:letRecDecls) := stx | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt tk
  let vars ← getLetRecDeclsVars decls
  let mγ ← mkMonadApp (← read).doBlockResultType
  doElabToSyntax m!"let rec body of group {vars}" dec.continueWithUnit fun body => do
    -- Let recs may never have nested actions. We expand just for the sake of error messages.
    -- This suppresses error messages for the let body. Not sure if this is a good call, but it was
    -- the status quo of the legacy `do` elaborator.
    Term.elabTerm (← `(let rec $decls:letRecDecls; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  -- def doReassign := letIdDeclNoBinders <|> letPatDecl
  match stx with
  | `(doReassign| $x:ident $[: $xType?]? :=%$tk $rhs) =>
    let decl : TSyntax ``letIdDecl ← `(letIdDecl| $x:ident $[: $xType?]? := $rhs)
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    elabDoLetOrReassign {} .reassign decl tk dec
  | `(doReassign| $decl:letPatDecl) =>
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    elabDoLetOrReassign {} .reassign decl decl dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $cfg:letConfig $pattern := $rhs | $otherwise $(body?)?) := stx
    | throwUnsupportedSyntax
  let config ← getLetConfigAndCheckMut cfg mutTk?
  checkLetConfigInDo config
  let letOrReassign := LetOrReassign.let mutTk? false
  let vars ← getPatternVarsEx pattern
  letOrReassign.checkMutVars vars
  let mut body ← body?.getDM `(doSeqIndent|pure PUnit.unit)
  -- In case of `let mut`, we need to re-declare the pattern variables as `let mut`s inside `body`.
  if mutTk?.isSome then
    for var in vars do
      body ← `(doSeqIndent| let mut $var := $var; do $body:doSeqIndent)
  if let some h := config.eq? then
    elabDoElem (← `(doElem| match $h:ident : $rhs:term with | $pattern => $body:doSeqIndent | _ => $otherwise:doSeqIndent)) dec
  else
    elabDoElem (← `(doElem| match $rhs:term with | $pattern => $body:doSeqIndent | _ => $otherwise:doSeqIndent)) dec

@[builtin_doElem_elab Lean.Parser.Term.doLetArrow] def elabDoLetArrow : DoElab := fun stx dec => do
  let `(doLetArrow| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl) := stx | throwUnsupportedSyntax
  let config ← getLetConfigAndCheckMut cfg mutTk?
  checkLetConfigInDo config
  if config.nondep || config.usedOnly || config.zeta || config.eq?.isSome then
    throwErrorAt cfg "configuration options are not supported with `←`"
  elabDoArrow mutTk? false decl tk dec

@[builtin_macro Lean.Parser.Term.doReassignArrow] def expandDoReassignArrow : Macro := fun stx => do
  match stx with
  | `(doReassignArrow| $x:ident $[: $t?]? ← $rhs) =>
    let y := mkIdentFrom x (← MonadQuotation.addMacroScope `__x)
    `(doElem| do let $y:ident $[: $t?]? ← $rhs; $x:ident := $y)
  | `(doReassignArrow| $pat:term $[: $t?]? ← $rhs $[| $otherwise? $(_rest?)?]?) =>
    if otherwise?.isSome then
      Macro.throwErrorAt stx "reassignment with `|` (i.e., \"else clause\") is not supported"
    else
      let y := mkIdentFrom pat (← MonadQuotation.addMacroScope `__x)
      `(doElem| do let $y:ident $[: $t?]? ← $rhs; $pat:term := $y)
  | _ => Macro.throwUnsupported
