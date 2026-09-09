/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
import Init.Data.Erased  -- referenced by the `ghost` quotations
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
  | let (mutTk? : Option Syntax) (ghostUser? : Option Ident)
  | have
  | reassign

def LetOrReassign.getLetMutTk? (letOrReassign : LetOrReassign) : Option Syntax :=
  match letOrReassign with
  | .let mutTk? _ => mutTk?
  | _             => none

/-- The source identifier of a `ghost` declaration. -/
def LetOrReassign.ghostUserIdent? (letOrReassign : LetOrReassign) : Option Ident :=
  match letOrReassign with
  | .let _ ghostUser? => ghostUser?
  | _                 => none

def LetOrReassign.checkMutVars (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit :=
  match letOrReassign with
  | .reassign => do
    throwUnlessMutVarsDeclared vars
  | _         => checkMutVarsForShadowing vars

def LetOrReassign.registerReassignAliasInfo (letOrReassign : LetOrReassign) (vars : Array Ident) : DoElabM Unit := do
  if letOrReassign matches .reassign then
    for var in vars do
      registerMutVarAlias var.getId

def elabDoLetOrReassignWith (hint : MessageData) (letOrReassign : LetOrReassign) (vars : Array Ident)
    (k : DoElabM Expr) (elabBody : (body : Term) → TermElabM Expr) : DoElabM Expr := do
  -- letOrReassign.checkMutVars vars -- Should be done by the caller!
  let elabCont : DoElabM Expr := do
    declareMutVars? letOrReassign.getLetMutTk? vars letOrReassign.ghostUserIdent? do
      letOrReassign.registerReassignAliasInfo vars
      k
  doElabToSyntax hint elabCont fun body => elabBody body

def elabWithReassignments (letOrReassign : LetOrReassign) (vars : Array Ident) (k : DoElabM Expr) : DoElabM Expr := do
  declareMutVars? letOrReassign.getLetMutTk? vars letOrReassign.ghostUserIdent? do
    letOrReassign.registerReassignAliasInfo vars
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

partial def elabDoLetOrReassign (config : Term.LetConfig) (letOrReassign : LetOrReassign) (decl : TSyntax ``letDecl)
    (tk : Syntax) (dec : DoElemCont) : DoElabM Expr := do
  checkLetConfigInDo config
  let vars ← getLetDeclVars decl
  letOrReassign.checkMutVars vars
  let dec ← dec.ensureUnitAt tk
  -- Some decl preprocessing on the patterns and expected types:
  let decl ← pushTypeIntoReassignment letOrReassign decl
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
      elabWithReassignments letOrReassign vars do
      match config.eq? with
      | none =>
        let body ← dec.continueWithUnit
        if config.zeta then
          pure <| (← body.abstractM #[x]).instantiate1 val
        else
          mkLetFVars #[x] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
      | some h =>
        let hTy ← mkEq x val
        withLetDecl h.getId hTy (← mkEqRefl x) (nondep := true) fun h' => do
          Term.addLocalVarInfo h h'
          let body ← dec.continueWithUnit
          if config.zeta then
            pure <| (← body.abstractM #[x, h']).instantiateRev #[val, ← mkEqRefl val]
          else if nondep then
            let f ← mkLambdaFVars #[x, h'] body
            return mkApp2 f val (← mkEqRefl val)
          else
            mkLetFVars #[x, h'] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
  | _ => throwUnsupportedSyntax

def elabDoArrow (letOrReassign : LetOrReassign) (stx : TSyntax [``doIdDecl, ``doPatDecl]) (tk : Syntax) (dec : DoElemCont) : DoElabM Expr := do
  match stx with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    letOrReassign.checkMutVars #[x]
    let dec ← dec.ensureUnitAt tk
    if letOrReassign matches .reassign then
      if ((← findMutVar? x.getId).map (·.ghost)).getD false then
        let y := mkIdentFrom x (← mkFreshUserName `__y)
        return ← elabDoIdDecl y xType? rhs
          (elabDoElem (← `(doElem| $x:ident := $y)) dec) (kind := dec.kind)
    -- For plain variable reassignment, we know the expected type of the reassigned variable and
    -- propagate it eagerly via type ascription if the user hasn't provided one themselves:
    let xType? ← match letOrReassign, xType? with
      | .reassign, none =>
        let decl ← getLocalDeclFromUserName x.getId
        some <$> Term.exprToSyntax decl.type
      | _, _ => pure xType?
    elabDoIdDecl x xType? rhs (declareMutVar? letOrReassign.getLetMutTk? x letOrReassign.ghostUserIdent? <| dec.continueWithUnit)
      (kind := dec.kind)
  | `(doPatDecl| _%$pattern $[: $patType?]? ← $rhs) =>
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    let dec ← dec.ensureUnitAt tk
    elabDoIdDecl x patType? rhs dec.continueWithUnit (kind := dec.kind)
  | `(doPatDecl| $pattern:term $[: $patType?]? ← $rhs $[| $otherwise? $(rest?)?]?) =>
    let rest? := rest?.join
    let x := mkIdentFrom pattern (← mkFreshUserName `__x)
    elabDoIdDecl x patType? rhs do
      match letOrReassign, otherwise? with
      | .let mutTk? _, some otherwise =>
        elabDoElem (← `(doElem| let $[mut%$mutTk?]? $pattern:term := $x | $otherwise $(rest?)?)) dec
      | .let mutTk? _, _ =>
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

private def getLetConfigAndCheckMut (letConfigStx : TSyntax ``Parser.Term.letConfig)
    (mutTk? : Option Syntax) (initConfig : Term.LetConfig := {}) : DoElabM Term.LetConfig := do
  if mutTk?.isSome && !letConfigStx.raw[0].getArgs.isEmpty then
    throwErrorAt letConfigStx "configuration options are not allowed with `let mut`"
  Term.mkLetConfig letConfigStx initConfig

@[builtin_doElem_elab Lean.Parser.Term.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let%$tk $[mut%$mutTk?]? $config:letConfig $decl:letDecl) := stx | throwUnsupportedSyntax
  let config ← getLetConfigAndCheckMut config mutTk?
  elabDoLetOrReassign config (.let mutTk? none) decl tk dec

/-- Elaborate `ghost $[mut]? $decl`. A single variable `x : t := e` binds a carried
`Erased t := Erased.mk e` under an inaccessible name, and the source name binds the `.out`
shadow that proofs read. A pattern binds its variables plainly and then shadows each one with
its ghost redeclaration. -/
@[builtin_doElem_elab Lean.Parser.Term.doGhost] def elabDoGhost : DoElab := fun stx dec => do
  match stx with
  | `(doGhost| ghost%$tk $[mut%$mutTk?]? $x:ident $[: $t?]? := $e) =>
    let xc := mkIdentFrom x (← mkFreshUserName x.getId) (canonical := true)
    let declNew ← match t? with
      | some t => `(letDecl| $xc:ident : Erased $t := Erased.mk $e)
      | none   => `(letDecl| $xc:ident := Erased.mk $e)
    let dec := { dec with k := withGhostShadow x xc.getId dec.k }
    elabDoLetOrReassign { nondep := true } (.let mutTk? (some x)) declNew tk dec
  | `(doGhost| ghost%$tk $[mut%$mutTk?]? $decl:letPatDecl) =>
    let declNew : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    let vars ← getLetDeclVars declNew
    let redecls ← vars.mapM fun v =>
      return ⟨(← `(doGhost| ghost%$tk $[mut%$mutTk?]? $v:ident := $v:ident)).raw⟩
    let dec ← dec.ensureUnitAt tk
    let dec ← if redecls.isEmpty then pure dec else
      pure <| DoElemCont.mk (← mkFreshUserName `__r) (← mkPUnit) (elabDoElems1 redecls dec) dec.kind
    elabDoLetOrReassign {} (.let none none) declNew tk dec
  | _ => throwUnsupportedSyntax

/-- Elaborate `ghost $[mut]? x ← act`: bind the action's result plainly to a fresh variable and
funnel it through `ghost x := y`, which wraps. At runtime the result is unused, so the element
behaves like `_ ← act`. -/
@[builtin_doElem_elab Lean.Parser.Term.doGhostArrow] def elabDoGhostArrow : DoElab := fun stx dec => do
  match stx with
  | `(doGhostArrow| ghost%$tk $[mut%$mutTk?]? $x:ident $[: $t?]? ← $rhs) =>
    checkMutVarsForShadowing #[x]
    let dec ← dec.ensureUnitAt tk
    let y := mkIdentFrom x (← mkFreshUserName `__y)
    elabDoIdDecl y t? rhs
      (elabDoElem ⟨(← `(doGhost| ghost%$tk $[mut%$mutTk?]? $x:ident := $y)).raw⟩ dec)
      (kind := dec.kind)
  | `(doGhostArrow| ghost%$tk $[mut%$mutTk?]? $pat:term $[: $t?]? ← $rhs $[| $otherwise? $(rest?)?]?) =>
    if otherwise?.isSome then
      throwErrorAt tk "`ghost` takes no `|` alternative"
    let dec ← dec.ensureUnitAt tk
    let y := mkIdentFrom pat (← mkFreshUserName `__y)
    elabDoIdDecl y t? rhs
      (elabDoElem ⟨(← `(doGhost| ghost%$tk $[mut%$mutTk?]? $pat:term := $y)).raw⟩ dec)
      (kind := dec.kind)
  | _ => throwUnsupportedSyntax

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
    -- A ghost variable's reassignment rebinds the carried variable with the wrapped value, so
    -- `x := e` stores `Erased.mk e` and an ascription moves inside: `x : t := e` stores
    -- `Erased.mk (e : t)`. The source name then rebinds the fresh `.out` shadow.
    if let some mv := (← findMutVar? x.getId).filter (·.ghost) then
      let xc := mkIdentFrom x mv.getId
      let rhs ← match xType? with
        | some t => `(Erased.mk ($rhs : $t))
        | none   => `(Erased.mk $rhs)
      let decl : TSyntax ``letIdDecl ← `(letIdDecl| $xc:ident := $rhs)
      let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
      let dec := { dec with k := withGhostShadow mv.userIdent mv.getId dec.k }
      return ← elabDoLetOrReassign {} .reassign decl tk dec
    let decl : TSyntax ``letIdDecl ← `(letIdDecl| $x:ident $[: $xType?]? := $rhs)
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    elabDoLetOrReassign {} .reassign decl tk dec
  | `(doReassign| $decl:letPatDecl) =>
    let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl]⟩
    for var in (← getLetDeclVars decl) do
      if ((← findMutVar? var.getId).map (·.ghost)).getD false then
        throwErrorAt var "a ghost variable takes a plain reassignment, as in `{var.getId} := e`"
    elabDoLetOrReassign {} .reassign decl decl dec
  | _ => throwUnsupportedSyntax

@[builtin_doElem_elab Lean.Parser.Term.doLetElse] def elabDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let $[mut%$mutTk?]? $cfg:letConfig $pattern := $rhs | $otherwise $(body?)?) := stx
    | throwUnsupportedSyntax
  let config ← getLetConfigAndCheckMut cfg mutTk?
  checkLetConfigInDo config
  let letOrReassign := LetOrReassign.let mutTk? none
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
  elabDoArrow (.let mutTk? none) decl tk dec

@[builtin_doElem_elab Lean.Parser.Term.doReassignArrow] def elabDoReassignArrow : DoElab := fun stx dec => do
  match stx with
  | `(doReassignArrow| $decl:doIdDecl) =>
    elabDoArrow .reassign decl decl dec
  | `(doReassignArrow| $decl:doPatDecl) =>
    elabDoArrow .reassign decl decl dec
  | _ => throwUnsupportedSyntax
