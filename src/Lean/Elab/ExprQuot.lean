/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
module

prelude
public import Lean.Meta.ExprPattern
public import Lean.Meta.Match.Match
public import Lean.Elab.MatchAltView
public import Lean.Elab.SyntheticMVars
meta import Lean.Parser.Term
meta import Lean.Parser.Do
import Init.Syntax
import Init.Data.Array.Mem
import Init.Omega
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Compiler.NoncomputableAttr

public section

/-!
# Quasi-Quoted `Expr` Pattern Elaboration, Term Building, and Native `match` Compilation

Implements:
- `` `(expr[rel]| p) `` pattern parsing/preprocessing (`?x` binders, `?P x y` higher-order binders,
  `$e` pins, `_` wildcards), elaboration via `elabExprQuotHoleApp` and `elabExprQuotPatSlot`, and
  per-module deduplicated `ExprPattern` auxiliary constants (`exprPatExt`).
- `` `(expr[rel]| t) `` term-position template building (`elabExprQuotTerm`, `exprTmplExt`),
  preserving sharing and zero beta-reduction, checking splice types under `rel`, synthesizing
  splice-dependent type-class instances at runtime, and opening `?h`/`?_` `refine` holes.
- `match (modulo := rel)` macro expansion for both term-mode and `do`-mode matches.
- Native `match`/`if let`/`let ... |` join-point dispatch (`compileExprMatch`), mixing ordinary
  constructors and `Expr` quotations cleanly with exact exhaustiveness/redundancy diagnostics and
  `sorry`-free catch-all fall-through.
-/

namespace Lean.Elab.Term.ExprQuot

open Lean Meta
open Lean.Parser.Term

private abbrev mkConst (n : Name) (us : List Level := []) : Expr :=
  Lean.mkConst n us

/-- Return `true` iff `stx` is an `` `(expr[rel]| ...) `` quotation node. -/
def isExprQuot (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Term.exprQuot

/--
Collect all `?x` pattern variable identifiers occurring in an `` `(expr[rel]| p) `` quotation,
stopping at `$`-pins and nested quotations, and rejecting repeated `?x`.
-/
def collectExprQuotPatternVars (exprQuotStx : Syntax) : TermElabM (Array Ident) := do
  let (_, (res, _)) ← (go exprQuotStx[4]).run (#[], {})
  return res
where
  go (stx : Syntax) : StateRefT (Array Ident × NameSet) TermElabM Unit := do
    if stx.isOfKind ``Parser.Term.syntheticHole then
      if stx[1].isIdent then
        let id : Ident := ⟨stx[1]⟩
        let name := id.getId
        unless name.eraseMacroScopes.isAtomic do
          throwErrorAt id
            "Invalid pattern variable: Variable name must be atomic, \
             but `{name}` has multiple components"
        if (← get).2.contains name then
          throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
        modify fun (vs, s) => (vs.push id, s.insert name)
      return
    if stx.isAntiquot || stx.isTokenAntiquot || stx.isAntiquotSplice ||
        stx.isAntiquotSuffixSplice || stx.isQuot || isExprQuot stx then
      return
    match stx with
    | .node _ _ args => for a in args do go a
    | _              => return

/-! ## `match (modulo := rel)` macro expansion -/

private def unwrapModuloRel (modRelStx : Syntax) :
    Option Syntax × Option Syntax × Array Syntax :=
  let inner := modRelStx[0]
  if inner.isOfKind ``exprQuotModuloWithEngine then
    let engWrapped := inner[0]
    let engStx :=
      if engWrapped.isOfKind ``exprQuotModuloEngineSlash then
        engWrapped[0]
      else
        mkNode ``exprQuotEngine #[mkAtomFrom engWrapped "/", engWrapped[0]]
    let items? := if inner[1].isNone then none else some inner[1][0]
    let flags := inner[2].getArgs
    (some engStx, items?, flags)
  else if inner.isOfKind ``exprQuotModuloItems then
    (none, some inner[0], inner[1].getArgs)
  else
    (none, none, inner[0].getArgs)

private def mergeExprQuotRel (modRelStx patRelStx : Syntax) : Syntax :=
  let patEng? := if patRelStx[0].isNone then none else some patRelStx[0][0]
  if patEng?.isSome then
    -- Pattern's own `/engine...` replaces the shared `(modulo := rel)` completely.
    patRelStx
  else
    let (modEng?, modItems?, modFlags) := unwrapModuloRel modRelStx
    let patItems? := if patRelStx[1].isNone then none else some patRelStx[1][0]
    let patFlags := patRelStx[2].getArgs
    let engNode := match modEng? with
      | some e => mkNullNode #[e]
      | none   => mkNullNode
    let itemsNode := match modItems?, patItems? with
      | none, none => mkNullNode
      | some i, none | none, some i => mkNullNode #[i]
      | some mi, some pi =>
        let merged := mi[1].getSepArgs ++ pi[1].getSepArgs
        let sepList := Syntax.mkSep merged (mkAtomFrom mi ", ")
        mkNullNode #[mkNode ``exprQuotItems #[mi[0], sepList, mi[2]]]
    let flagsNode := mkNullNode (modFlags ++ patFlags)
    mkNode ``exprQuotRel #[engNode, itemsNode, flagsNode]

private def rewriteExprQuotsInPat (modRelStx : Syntax) (stx : Syntax) : Syntax :=
  if isExprQuot stx then
    stx.setArg 2 (mergeExprQuotRel modRelStx stx[2])
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    stx
  else
    match stx with
    | .node i k args =>
      if k == ``Parser.Term.typeAscription then
        if h : 1 < args.size then
          .node i k (args.set 1 (rewriteExprQuotsInPat modRelStx args[1]))
        else
          .node i k args
      else
        .node i k (args.map fun a => rewriteExprQuotsInPat modRelStx a)
    | _ => stx
termination_by sizeOf stx
decreasing_by
  · simp_wf
    have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
    omega
  · decreasing_tactic

private def rewriteMatchAltsModulo (modRelStx : Syntax) (matchAltsStx : Syntax) : Syntax :=
  matchAltsStx.modifyArg 0 fun altsNode =>
    altsNode.setArgs <| altsNode.getArgs.map fun alt =>
      alt.modifyArg 1 (rewriteExprQuotsInPat modRelStx)

private def validateAndLiftModuloPins (modRelStx : Syntax) :
    MacroM (Syntax × Array (Ident × Term)) := do
  let inner := modRelStx[0]
  let mut lifted : Array (Ident × Term) := #[]
  let liftItems (itemsStx : Syntax) (lifted : Array (Ident × Term)) :
      MacroM (Syntax × Array (Ident × Term)) := do
    let sepArgs := itemsStx[1].getArgs
    let mut newSepArgs := sepArgs
    let mut acc := lifted
    for h : i in *...sepArgs.size do
      if i % 2 == 0 then
        let itemStx := sepArgs[i]
        if itemStx[1].isOfKind ``exprQuotItemPin then
          let pinNode := itemStx[1]
          let pinTerm : Term :=
            ⟨if pinNode.getNumArgs == 2 then pinNode[1] else pinNode[2]⟩
          let pinId : Ident ← withFreshMacroScope `(modPin)
          let pinId := ⟨mkIdentFrom pinTerm pinId.getId⟩
          acc := acc.push (pinId, pinTerm)
          let newPin := mkNode ``exprQuotItemPin #[pinNode[0], pinId]
          newSepArgs := newSepArgs.set! i (itemStx.setArg 1 newPin)
    return (itemsStx.setArg 1 (mkNullNode newSepArgs), acc)
  let validateFlags (flags : Array Syntax) : MacroM Unit := do
    for flagStx in flags do
      let flagName := flagStx[1].getId.eraseMacroScopes
      unless flagName == `inst || flagName == `beta || flagName == `zeta ||
          flagName == `proj || flagName == `eta do
        Macro.throwErrorAt flagStx[1]
          s!"unknown expr quotation flag `{flagName}`; \
             expected `inst`, `beta`, `zeta`, `proj`, or `eta`"
  if inner.isOfKind ``exprQuotModuloWithEngine then
    let engWrapped := inner[0]
    let engId :=
      if engWrapped.isOfKind ``exprQuotModuloEngineSlash then
        engWrapped[0][1]
      else
        engWrapped[0]
    let engName := engId.getId.eraseMacroScopes
    unless engName == `structural || engName == `reducible || engName == `instances ||
        engName == `defeq || engName == `sym do
      Macro.throwErrorAt engId
        s!"unknown expr quotation engine `{engName}`; \
           expected `structural`, `reducible`, `instances`, `defeq`, or `sym`"
    validateFlags inner[2].getArgs
    if inner[1].isNone then
      return (modRelStx, lifted)
    else
      let (newItems, lifted') ← liftItems inner[1][0] lifted
      let newInner := inner.setArg 1 (mkNullNode #[newItems])
      return (modRelStx.setArg 0 newInner, lifted')
  else if inner.isOfKind ``exprQuotModuloItems then
    validateFlags inner[1].getArgs
    let (newItems, lifted') ← liftItems inner[0] lifted
    let newInner := inner.setArg 0 newItems
    return (modRelStx.setArg 0 newInner, lifted')
  else
    validateFlags inner[0].getArgs
    return (modRelStx, lifted)

/-- Expand term-level `match (modulo := rel) ...` into `match ...` with merged relations. -/
@[builtin_macro Lean.Parser.Term.matchModulo] def expandMatchModulo : Macro := fun stx => do
  let gen1 := stx[1]
  let mot1 := stx[2]
  let modParam := stx[3]
  let gen2 := stx[4]
  let mot2 := stx[5]
  if !gen1.isNone && !gen2.isNone then
    Macro.throwErrorAt gen2 "duplicate `(generalizing := ...)` parameter in `match`"
  if !mot1.isNone && !mot2.isNone then
    Macro.throwErrorAt mot2 "duplicate `(motive := ...)` parameter in `match`"
  let gen := if !gen1.isNone then gen1 else gen2
  let mot := if !mot1.isNone then mot1 else mot2
  let (modRel, liftedPins) ← validateAndLiftModuloPins modParam[3]
  let alts := rewriteMatchAltsModulo modRel stx[8]
  let mut res : Term :=
    ⟨mkNode ``Parser.Term.«match» #[stx[0], gen, mot, stx[6], stx[7], alts]⟩
  for (pinId, pinTerm) in liftedPins.reverse do
    res ← `(have $pinId : _root_.Lean.Expr := $pinTerm; $res)
  return res.raw

/-- Expand `do`-level `match (modulo := rel) ...` into `doMatch` with merged relations. -/
@[builtin_macro Lean.Parser.Term.doMatchModulo] def expandDoMatchModulo : Macro := fun stx => do
  let dep1 := stx[1]
  let gen1 := stx[2]
  let mot1 := stx[3]
  let modParam := stx[4]
  let dep2 := stx[5]
  let gen2 := stx[6]
  let mot2 := stx[7]
  if !dep1.isNone && !dep2.isNone then
    Macro.throwErrorAt dep2 "duplicate `(dependent := ...)` parameter in `match`"
  if !gen1.isNone && !gen2.isNone then
    Macro.throwErrorAt gen2 "duplicate `(generalizing := ...)` parameter in `match`"
  if !mot1.isNone && !mot2.isNone then
    Macro.throwErrorAt mot2 "duplicate `(motive := ...)` parameter in `match`"
  let dep := if !dep1.isNone then dep1 else dep2
  let gen := if !gen1.isNone then gen1 else gen2
  let mot := if !mot1.isNone then mot1 else mot2
  let (modRel, liftedPins) ← validateAndLiftModuloPins modParam[3]
  let alts := rewriteMatchAltsModulo modRel stx[10]
  let mut res : TSyntax `doElem :=
    ⟨mkNode ``Parser.Term.doMatch #[stx[0], dep, gen, mot, stx[8], stx[9], alts]⟩
  for (pinId, pinTerm) in liftedPins.reverse do
    res ← `(doElem| do have $pinId : _root_.Lean.Expr := $pinTerm; $res:doElem)
  return res.raw

/-! ## Relation elaboration and pattern compilation -/

private def elabExprMatchEngine (stx : Syntax) : TermElabM ExprMatchEngine := do
  let name := stx[1].getId.eraseMacroScopes
  match name with
  | `structural => return .structural
  | `reducible  => return .reducible
  | `instances  => return .instances
  | `defeq      => return .defeq
  | `sym        => return .sym
  | _ =>
    throwErrorAt stx[1]
      "unknown expr quotation engine `{name}`; \
       expected `structural`, `reducible`, `instances`, `defeq`, or `sym`"

private def elabPinExpr (termStx : Syntax) (isIdentPin : Bool) : TermElabM Expr := do
  try
    withoutErrToSorry <| Term.elabTermEnsuringType termStx (mkConst ``Expr)
  catch ex =>
    if isIdentPin && termStx.isIdent then
      let id := termStx.getId
      if (← resolveLocalName id).isNone && (← resolveGlobalName id).isEmpty then
        throwErrorAt termStx "unknown identifier `{id}` in `$`-pin (did you mean `?{id}`?)"
    throw ex

/--
Elaborate `exprQuotRel` syntax into a static `ExprMatchRel` plus any dynamic `$x` item pins
evaluated in the current local context. Pattern quotations default to `.structural`, while
term-building quotations pass `defaultEngine := .defeq`.
-/
def elabExprMatchRel (relStx : Syntax) (defaultEngine : ExprMatchEngine := .structural) :
    TermElabM (ExprMatchRel × Array (Bool × Expr)) := do
  let mut engine : ExprMatchEngine := defaultEngine
  unless relStx[0].isNone do
    engine ← elabExprMatchEngine relStx[0][0]
  let mut items : Array ExprMatchItem := #[]
  let mut localItems : Array (Bool × Expr) := #[]
  unless relStx[1].isNone do
    let itemsStx := relStx[1][0]
    for itemStx in itemsStx[1].getSepArgs do
      let positive := itemStx[0].isNone || itemStx[0][0].isOfKind ``exprQuotItemPos
      let target := itemStx[1]
      if target.isOfKind ``exprQuotItemPin then
        let (pinTerm, isId) :=
          if target.getNumArgs == 2 then (target[1], true) else (target[2], false)
        let e ← elabPinExpr pinTerm isId
        localItems := localItems.push (positive, e)
      else
        let id : Ident := ⟨target⟩
        let name := id.getId.eraseMacroScopes
        if (← getSimpExtension? name).isSome then
          items := items.push { positive, declName := name, isSimpSet := true }
        else
          let declName ← realizeGlobalConstNoOverloadWithInfo id
          items := items.push { positive, declName, isSimpSet := false }
  let mut flags : ExprMatchFlags := {}
  for flagStx in relStx[2].getArgs do
    let val := flagStx.isOfKind ``exprQuotFlagPos
    let flagName := flagStx[1].getId.eraseMacroScopes
    match flagName with
    | `inst => flags := { flags with inst := some val }
    | `beta => flags := { flags with beta := some val }
    | `zeta => flags := { flags with zeta := some val }
    | `proj => flags := { flags with proj := some val }
    | `eta  => flags := { flags with eta := some val }
    | _ =>
      throwErrorAt flagStx[1]
        "unknown expr quotation flag `{flagName}`; \
         expected `inst`, `beta`, `zeta`, `proj`, or `eta`"
  let rel : ExprMatchRel := { engine, items, flags }
  let _ ← rel.resolveStatic
  return (rel, localItems)

/-! ## Compile-time pattern quoting and deduplicated auxiliary constant emission -/

private def quoteBinderInfo (bi : BinderInfo) : Expr :=
  mkConst <| match bi with
    | .default        => ``BinderInfo.default
    | .implicit       => ``BinderInfo.implicit
    | .strictImplicit => ``BinderInfo.strictImplicit
    | .instImplicit   => ``BinderInfo.instImplicit

private def quoteLevel : Level → TermElabM Expr
  | .zero      => return mkConst ``Level.zero
  | .succ u    => return mkApp (mkConst ``Level.succ) (← quoteLevel u)
  | .max u v   => return mkApp2 (mkConst ``Level.max) (← quoteLevel u) (← quoteLevel v)
  | .imax u v  => return mkApp2 (mkConst ``Level.imax) (← quoteLevel u) (← quoteLevel v)
  | .param n   => return mkApp (mkConst ``Level.param) (toExpr n)
  | .mvar _    => throwError "internal error in expr quotation: unexpected universe metavariable"

private def quoteExpr : Expr → TermElabM Expr
  | .bvar i => return mkApp (mkConst ``Expr.bvar) (toExpr i)
  | .sort u => return mkApp (mkConst ``Expr.sort) (← quoteLevel u)
  | .const n us => do
    let usExpr ← us.mapM quoteLevel
    let levelType := mkConst ``Level
    let nil := mkApp (mkConst ``List.nil [0]) levelType
    let cons := mkApp (mkConst ``List.cons [0]) levelType
    let listExpr := usExpr.foldr (init := nil) fun u acc => mkApp2 cons u acc
    return mkApp2 (mkConst ``Expr.const) (toExpr n) listExpr
  | .app f a => return mkApp2 (mkConst ``Expr.app) (← quoteExpr f) (← quoteExpr a)
  | .lam n t b bi =>
    return mkApp4 (mkConst ``Expr.lam) (toExpr n) (← quoteExpr t) (← quoteExpr b)
      (quoteBinderInfo bi)
  | .forallE n t b bi =>
    return mkApp4 (mkConst ``Expr.forallE) (toExpr n) (← quoteExpr t) (← quoteExpr b)
      (quoteBinderInfo bi)
  | .letE n t v b nd =>
    return mkApp5 (mkConst ``Expr.letE) (toExpr n) (← quoteExpr t) (← quoteExpr v)
      (← quoteExpr b) (toExpr nd)
  | .lit l => return mkApp (mkConst ``Expr.lit) (toExpr l)
  | .mdata _ e => quoteExpr e
  | .proj s i e => return mkApp3 (mkConst ``Expr.proj) (toExpr s) (toExpr i) (← quoteExpr e)
  | .fvar _ | .mvar _ =>
    throwError "internal error in expr quotation: compiled pattern is not closed"

private def quoteExprMatchEngine : ExprMatchEngine → Expr
  | .structural => mkConst ``ExprMatchEngine.structural
  | .reducible  => mkConst ``ExprMatchEngine.reducible
  | .instances  => mkConst ``ExprMatchEngine.instances
  | .defeq      => mkConst ``ExprMatchEngine.defeq
  | .sym        => mkConst ``ExprMatchEngine.sym

private def quoteExprMatchItem (item : ExprMatchItem) : Expr :=
  mkApp3 (mkConst ``ExprMatchItem.mk)
    (toExpr item.positive) (toExpr item.declName) (toExpr item.isSimpSet)

private def quoteOptionBool : Option Bool → Expr
  | none   => mkApp (mkConst ``Option.none [0]) (mkConst ``Bool)
  | some b => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Bool) (toExpr b)

private def quoteExprMatchFlags (f : ExprMatchFlags) : Expr :=
  mkApp5 (mkConst ``ExprMatchFlags.mk)
    (quoteOptionBool f.inst) (quoteOptionBool f.beta) (quoteOptionBool f.zeta)
    (quoteOptionBool f.proj) (quoteOptionBool f.eta)

private def quoteResolvedExprMatchFlags (f : ResolvedExprMatchFlags) : Expr :=
  mkApp5 (mkConst ``ResolvedExprMatchFlags.mk)
    (toExpr f.inst) (toExpr f.beta) (toExpr f.zeta) (toExpr f.proj) (toExpr f.eta)

private def quoteResolvedExprMatchRel (rel : ExprMatchRel) : Expr :=
  let flags := rel.resolveFlags
  let hasUnfolding := flags.beta || flags.zeta || flags.proj || flags.eta
  let ruleTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Sum [0, 0]) (mkConst ``Name) (mkConst ``SimpTheorems))
  let emptyRules := Expr.app (mkConst ``Array.empty [0]) ruleTy
  let emptyFVars := Expr.app (mkConst ``Array.empty [0]) (mkConst ``FVarId)
  mkApp6 (mkConst ``ResolvedExprMatchRel.mk)
    (quoteExprMatchEngine rel.engine) (quoteResolvedExprMatchFlags flags)
    emptyRules emptyFVars emptyFVars (toExpr hasUnfolding)

/-- Serialize an `ExprMatchRel` into a closed Lean term expression. -/
def quoteExprMatchRel (rel : ExprMatchRel) : TermElabM Expr := do
  let itemsArr ← mkArrayLit (mkConst ``ExprMatchItem) (rel.items.map quoteExprMatchItem).toList
  return mkApp3 (mkConst ``ExprMatchRel.mk)
    (quoteExprMatchEngine rel.engine) itemsArr (quoteExprMatchFlags rel.flags)

private def mkListLitExpr (elemTy : Expr) (elems : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [0]) elemTy
  let cons := mkApp (mkConst ``List.cons [0]) elemTy
  elems.foldr (init := nil) fun e acc => mkApp2 cons e acc

private structure PatCacheKey where
  levelParams : List Name
  lam         : Expr
  numVars     : Nat
  namedIdx    : Array Nat
  firstOrder  : Array Bool
  isPrivate   : Bool
  isMeta      : Bool
  deriving BEq, Hashable

private builtin_initialize exprPatExt : EnvExtension (Std.HashMap PatCacheKey Name) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private structure TmplCacheKey where
  levelParams : List Name
  lam         : Expr
  varKinds    : Array ExprTemplateVarKind
  isPrivate   : Bool
  isMeta      : Bool
  deriving BEq, Hashable

private builtin_initialize exprTmplExt : EnvExtension (Std.HashMap TmplCacheKey Name) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def auxDeclContextFlags : TermElabM (Bool × Bool) := do
  let env ← getEnv
  let isMeta := (← read).isMetaSection || (← read).declName?.any (isMarkedMeta env) ||
    (← read).declName?.isNone
  let isPrivate := env.header.isModule && !env.isExporting
  return (isPrivate, isMeta)

private def addAuxClosedDecl (auxBase : Name) (isPrivate isMeta : Bool)
    (type value : Expr) : TermElabM Name := do
  let env ← getEnv
  let baseName ← Term.mkAuxName auxBase
  let auxName := if isPrivate then mkPrivateName env baseName else baseName
  let decl := Declaration.defnDecl {
    name        := auxName
    levelParams := []
    type
    value
    hints       := .opaque
    safety      := .safe
  }
  let logCompileErrors := !(← read).isNoncomputableSection &&
    !(← read).declName?.any (Lean.isNoncomputable env)
  addAndCompile decl (logCompileErrors := logCompileErrors) (markMeta := isMeta)
  return auxName

private def mkAuxPatConst (pat : ExprPattern) : TermElabM Expr := do
  let env ← getEnv
  let (isPrivate, isMeta) ← auxDeclContextFlags
  let key : PatCacheKey := {
    levelParams := pat.levelParams
    lam         := pat.lam
    numVars     := pat.numVars
    namedIdx    := pat.namedIdx
    firstOrder  := pat.firstOrder
    isPrivate
    isMeta
  }
  let state := exprPatExt.getState env
  let cached? := state[key]? <|> if isPrivate then state[{ key with isPrivate := false }]? else none
  if let some cachedName := cached? then
    return mkConst cachedName
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)
  let proofPairs ← pat.closedProofs.toList.mapM fun (k, v) => do
    return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Expr) (mkConst ``Expr)
      (← quoteExpr k) (← quoteExpr v)
  let patVal := mkAppN (mkConst ``ExprPattern.mkCompiled) #[
    mkListLitExpr (mkConst ``Name) (pat.levelParams.map toExpr),
    ← quoteExpr pat.lam,
    toExpr pat.numVars,
    ← mkArrayLit (mkConst ``Nat) (pat.namedIdx.toList.map toExpr),
    ← mkArrayLit (mkConst ``Bool) (pat.firstOrder.toList.map toExpr),
    ← mkArrayLit (mkConst ``Bool) (pat.captureVars.toList.map toExpr),
    mkListLitExpr pairTy proofPairs,
    toExpr pat.precomputed
  ]
  let patAuxName ← addAuxClosedDecl `exprPat isPrivate isMeta (mkConst ``ExprPattern) patVal
  modifyEnv fun env => exprPatExt.modifyState env (·.insert key patAuxName)
  return mkConst patAuxName

private def quoteExprTemplateVarKind : ExprTemplateVarKind → Expr
  | .splice pos     => mkApp (mkConst ``ExprTemplateVarKind.splice) (toExpr pos)
  | .hole userName? =>
    let optTy := mkConst ``Name
    let optExpr := match userName? with
      | none   => mkApp (mkConst ``Option.none [0]) optTy
      | some n => mkApp2 (mkConst ``Option.some [0]) optTy (toExpr n)
    mkApp (mkConst ``ExprTemplateVarKind.hole) optExpr
  | .tc             => mkConst ``ExprTemplateVarKind.tc
  | .infer          => mkConst ``ExprTemplateVarKind.infer

private def mkAuxTmplConst (tmpl : ExprTemplate) : TermElabM Expr := do
  let env ← getEnv
  let (isPrivate, isMeta) ← auxDeclContextFlags
  let key : TmplCacheKey := {
    levelParams := tmpl.levelParams
    lam         := tmpl.lam
    varKinds    := tmpl.varKinds
    isPrivate
    isMeta
  }
  let state := exprTmplExt.getState env
  let cached? := state[key]? <|> if isPrivate then state[{ key with isPrivate := false }]? else none
  if let some cachedName := cached? then
    return mkConst cachedName
  let tmplVal := mkApp3 (mkConst ``ExprTemplate.mk)
    (mkListLitExpr (mkConst ``Name) (tmpl.levelParams.map toExpr))
    (← quoteExpr tmpl.lam)
    (← mkArrayLit (mkConst ``ExprTemplateVarKind)
      (tmpl.varKinds.toList.map quoteExprTemplateVarKind))
  let tmplAuxName ← addAuxClosedDecl `exprTmpl isPrivate isMeta (mkConst ``ExprTemplate) tmplVal
  modifyEnv fun env => exprTmplExt.modifyState env (·.insert key tmplAuxName)
  return mkConst tmplAuxName

/-! ## Pattern preprocessing & elaboration -/

private inductive PatHoleKind where
  | binder (id : Ident) (arity : Nat)
  | pin    (term : Syntax) (arity : Nat) (isIdent : Bool)
  deriving Inhabited

private structure PatPreprocessState where
  binders       : Array Ident := #[]
  binderArity   : NameMap Nat := {}
  holes         : Array PatHoleKind := #[]
  holeNames     : Array Name := #[]
  -- Map binder name -> index in `holes` (for `$x` referencing an earlier `?x` in the same pattern).
  binderHoleIdx : NameMap Nat := {}
  selfPins      : Array (Ident × Name) := #[]

private def mkPlaceholderSyntax (ref : Syntax) (idx : Nat) : Syntax :=
  mkNode ``Parser.Term.elabToSyntax #[mkAtomFrom ref "elabToSyntax% ", Syntax.mkNatLit idx]

private def mkHoleAppOrApp (ref : Syntax) (idx : Nat) (holeName : Name)
    (newArgs : Array Syntax) : Syntax :=
  let ph := mkPlaceholderSyntax ref idx
  let hasNamedOrEllipsis := newArgs.any fun a =>
    a.isOfKind ``Parser.Term.namedArgument || a.isOfKind ``Parser.Term.ellipsis
  if hasNamedOrEllipsis then
    mkNode ``Parser.Term.app #[ph, mkNullNode newArgs]
  else
    mkNode ``Parser.Term.exprQuotHoleApp #[mkIdentFrom ref holeName, ph, mkNullNode newArgs]

private def recordPatHole (hk : PatHoleKind) :
    StateT PatPreprocessState TermElabM (Nat × Name) := do
  let idx := (← get).holes.size
  let baseName := match hk with
    | .binder id _ => id.getId
    | .pin _ _ _   => `_pin
  let holeName ← mkFreshUserName baseName
  modify fun s => { s with
    holes := s.holes.push hk
    holeNames := s.holeNames.push holeName
  }
  return (idx, holeName)

private def preprocessAppHead (fnStx : Syntax) (numArgs : Nat)
    (elabArgs : StateT PatPreprocessState TermElabM (Array Syntax)) :
    StateT PatPreprocessState TermElabM (Option Syntax) := do
  if fnStx.isOfKind ``Parser.Term.syntheticHole && fnStx[1].isIdent then
    let id : Ident := ⟨fnStx[1]⟩
    let name := id.getId
    unless name.eraseMacroScopes.isAtomic do
      throwErrorAt id
        "Invalid pattern variable: Variable name must be atomic, \
         but `{name}` has multiple components"
    if (← get).binderHoleIdx.contains name then
      throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
    let (idx, holeName) ← recordPatHole (.binder id numArgs)
    modify fun s => { s with
      binders := s.binders.push id
      binderArity := s.binderArity.insert name numArgs
      binderHoleIdx := s.binderHoleIdx.insert name idx
    }
    let newArgs ← elabArgs
    return some <| mkHoleAppOrApp fnStx idx holeName newArgs
  else if fnStx.isAntiquot && !fnStx.isEscapedAntiquot then
    let aqTerm := fnStx.getAntiquotTerm
    if aqTerm.isOfKind ``Parser.Term.hole then
      throwErrorAt fnStx "expected `$e` pin; use `_` for a wildcard"
    let newArgs ← elabArgs
    if aqTerm.isIdent then
      let name := aqTerm.getId
      if let some idx := (← get).binderHoleIdx.find? name then
        let holeName := (← get).holeNames.getD idx `_pin
        modify fun s => { s with selfPins := s.selfPins.push (⟨aqTerm⟩, name) }
        return some <| mkHoleAppOrApp fnStx idx holeName newArgs
    let (idx, holeName) ← recordPatHole (.pin aqTerm numArgs aqTerm.isIdent)
    return some <| mkHoleAppOrApp fnStx idx holeName newArgs
  else
    return none

private def preprocessExprPatStx (stx : Syntax) : StateT PatPreprocessState TermElabM Syntax := do
  if stx.isOfKind ``Parser.Term.syntheticHole then
    if stx[1].isIdent then
      let id : Ident := ⟨stx[1]⟩
      let name := id.getId
      unless name.eraseMacroScopes.isAtomic do
        throwErrorAt id
          "Invalid pattern variable: Variable name must be atomic, \
           but `{name}` has multiple components"
      if (← get).binderHoleIdx.contains name then
        throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
      let (idx, _) ← recordPatHole (.binder id 0)
      modify fun s => { s with
        binders := s.binders.push id
        binderArity := s.binderArity.insert name 0
        binderHoleIdx := s.binderHoleIdx.insert name idx
      }
      return mkPlaceholderSyntax stx idx
    else
      -- `?_` -> treat as wildcard hole `_`
      return mkHole stx
  if stx.isAntiquot then
    if stx.isEscapedAntiquot then
      return Syntax.unescapeAntiquot stx
    let aqTerm := stx.getAntiquotTerm
    if aqTerm.isOfKind ``Parser.Term.hole then
      throwErrorAt stx "expected `$e` pin; use `_` for a wildcard"
    if aqTerm.isIdent then
      let name := aqTerm.getId
      if let some idx := (← get).binderHoleIdx.find? name then
        modify fun s => { s with selfPins := s.selfPins.push (⟨aqTerm⟩, name) }
        return mkPlaceholderSyntax stx idx
    let (idx, _) ← recordPatHole (.pin aqTerm 0 aqTerm.isIdent)
    return mkPlaceholderSyntax stx idx
  if stx.isQuot || isExprQuot stx then
    return stx
  match stx with
  | .node i k args =>
    if k == ``Parser.Term.app then
      if _h0 : 0 < args.size then
        if h1 : 1 < args.size then
          let fnStx := args[0]
          let argsNode := args[1]
          let elabArgs : StateT PatPreprocessState TermElabM (Array Syntax) :=
            match hNode : argsNode with
            | .node _ _ innerArgs => do
              let mut out := Array.emptyWithCapacity innerArgs.size
              for hMem : a in innerArgs do
                have hSub1 : sizeOf a < sizeOf innerArgs := Array.sizeOf_lt_of_mem hMem
                have hSub2 : sizeOf argsNode < sizeOf args :=
                  Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
                have hNodeSize : sizeOf innerArgs < sizeOf argsNode := by
                  rw [hNode]; simp_wf; omega
                have hSize : sizeOf a < 1 + sizeOf i + sizeOf k + sizeOf args := by omega
                out := out.push (← preprocessExprPatStx a)
              return out
            | _ => return #[]
          if let some res ← preprocessAppHead fnStx argsNode.getArgs.size elabArgs then
            return res
    let mut newArgs := Array.emptyWithCapacity args.size
    for a in args do
      newArgs := newArgs.push (← preprocessExprPatStx a)
    return .node i k newArgs
  | _ => return stx
termination_by sizeOf stx

/--
Elaborate a pattern hole/pin application `exprQuotHoleApp` (`?P x y` or `$fn a b`), creating a
synthetic-opaque hole metavariable whose type abstracts only distinct bound-variable arguments.
-/
@[builtin_term_elab Lean.Parser.Term.exprQuotHoleApp]
def elabExprQuotHoleApp : TermElab := fun stx expectedType? => do
  let holeName := stx[0].getId
  let placeholder := stx[1]
  let idx := placeholder[1].isNatLit?.getD 0
  unless placeholder.isOfKind ``Parser.Term.elabToSyntax &&
      idx < (← read).fixedTermElabs.size do
    throwUnsupportedSyntax
  let argStxs := stx[2].getArgs
  if ((← getMCtx).findUserName? holeName).isSome then
    return ← Term.elabTerm (mkNode ``Parser.Term.app #[placeholder, stx[2]]) expectedType?
  let argExprs ← argStxs.mapM fun a => do instantiateMVars (← Term.elabTerm a none)
  let mut fvarBinders : Array Expr := #[]
  let mut seenFVars : FVarIdSet := {}
  let mut isDistinctBinder : Array Bool := #[]
  for a in argExprs do
    if a.isFVar then
      let fv := a.fvarId!
      let decl ← fv.getDecl
      if !decl.isLet (allowNondep := true) && !seenFVars.contains fv then
        seenFVars := seenFVars.insert fv
        fvarBinders := fvarBinders.push a
        isDistinctBinder := isDistinctBinder.push true
      else
        isDistinctBinder := isDistinctBinder.push false
    else
      isDistinctBinder := isDistinctBinder.push false
  let mut pTy ←
    if fvarBinders.isEmpty then
      let u ← withLCtx {} {} mkFreshLevelMVar
      withLCtx {} {} <| mkFreshExprMVar (some (mkSort u))
    else
      let u ← withLCtx {} {} mkFreshLevelMVar
      let retTyFunTy ← mkForallFVars fvarBinders (mkSort u)
      if retTyFunTy.hasFVar then
        throwError "pattern hole cannot depend on bound variables not passed as arguments"
      let retTyMVar ← withLCtx {} {} <| mkFreshExprMVar (some retTyFunTy)
      pure (mkAppN retTyMVar fvarBinders)
  for i in (Array.range argExprs.size).reverse do
    if h : i < argExprs.size then
      let a := argExprs[i]
      if isDistinctBinder.getD i false then
        pTy ← mkForallFVars #[a] pTy
      else
        let aTy ← instantiateMVars (← inferType a)
        pTy ← mkArrow aTy pTy
  if pTy.hasFVar then
    throwError "pattern hole cannot depend on bound variables not passed as arguments"
  let mv ← withLCtx {} {} <| mkFreshExprMVar (some pTy) .syntheticOpaque holeName
  let app := mkAppN mv argExprs
  if let some expTy := expectedType? then
    let appTy ← inferType app
    unless ← isDefEq appTy expTy do
      Term.throwTypeMismatchError none expTy appTy app
  return app

/--
Elaborate an extracted `expr` quotation pattern placeholder (`exprQuotPatSlot`), attributing type
mismatches directly to the user's quotation syntax instead of internal placeholder identifiers.
-/
@[builtin_term_elab Lean.Parser.Term.exprQuotPatSlot]
def elabExprQuotPatSlot : TermElab := fun stx expectedType? => do
  let phId := stx[0]
  let origQuot := stx[1]
  let some (phExpr, []) ← resolveLocalName phId.getId
    | throwErrorAt origQuot
        "invalid `expr` quotation pattern: quotation occurs in an inaccessible or parameter \
         position"
  let exprTy := mkConst ``Expr
  let phTy ← inferType phExpr
  discard <| withRef origQuot <| isDefEq phTy exprTy
  if let some expTy := expectedType? then
    unless ← isDefEq exprTy expTy do
      let expTy ← instantiateMVars expTy
      throwErrorAt origQuot
        "type mismatch{indentD origQuot}\nhas type{indentExpr exprTy}\n\
         but is expected to have type{indentExpr expTy}"
  return phExpr

private def getMVarAppArgs? : Expr → Option (MVarId × Array Expr)
  | .mvar mvarId => some (mvarId, #[])
  | .mdata _ b   => getMVarAppArgs? b
  | .app f a     => (getMVarAppArgs? f).map fun (m, args) => (m, args.push a)
  | _            => none

/--
Detect which pattern metavariables `m` in `e` are used ONLY in higher-order Miller position
(i.e. applied to distinct bound variables of `e`), returning `true` for first-order and `false`
for higher-order.
-/
private def computeFirstOrderMask (e : Expr) (mvars : Array Expr) : Array Bool := Id.run do
  let mvarIds := mvars.map fun m => if m.isMVar then some m.mvarId! else none
  let isHigherOrder : Array Bool := .replicate mvars.size false
  let (_, ho) := (visit mvarIds e 0).run isHigherOrder
  return ho.map (!·)
where
  visitAppArgs (mvarIds : Array (Option MVarId)) (f : Expr) (depth : Nat) :
      StateM (Array Bool) Unit :=
    match f with
    | .app f' a    => do visitAppArgs mvarIds f' depth; visit mvarIds a depth
    | .mdata _ b   => visitAppArgs mvarIds b depth
    | _            => return
  visit (mvarIds : Array (Option MVarId)) (e : Expr) (depth : Nat) :
      StateM (Array Bool) Unit := do
    match e with
    | .app f a =>
      if let some (mvarId, args) := getMVarAppArgs? e then
        if let some idx := mvarIds.findIdx? (· == some mvarId) then
          if !args.isEmpty then
            let mut allDistinctBVars := true
            let mut seenBVars : Array Nat := #[]
            for arg in args do
              if let .bvar bIdx := arg.consumeMData then
                if bIdx < depth && !seenBVars.contains bIdx then
                  seenBVars := seenBVars.push bIdx
                else
                  allDistinctBVars := false
              else
                allDistinctBVars := false
            if allDistinctBVars then
              modify fun s : Array Bool => s.setIfInBounds idx true
        visitAppArgs mvarIds f depth
        visit mvarIds a depth
      else
        visit mvarIds f depth
        visit mvarIds a depth
    | .lam _ d b _      => visit mvarIds d depth; visit mvarIds b (depth + 1)
    | .forallE _ d b _  => visit mvarIds d depth; visit mvarIds b (depth + 1)
    | .letE _ t v b _   =>
      visit mvarIds t depth; visit mvarIds v depth; visit mvarIds b (depth + 1)
    | .mdata _ b        => visit mvarIds b depth
    | .proj _ _ b       => visit mvarIds b depth
    | _                 => return

private def shiftElabPlaceholders (baseOffset : Nat) (stx : Syntax) : Syntax :=
  match stx with
  | .node i k args =>
    if k == ``Parser.Term.elabToSyntax then
      let idx := stx[1].isNatLit?.getD 0
      Syntax.node i k #[stx[0], Syntax.mkNatLit (baseOffset + idx)]
    else
      .node i k (args.map fun a => shiftElabPlaceholders baseOffset a)
  | stx => stx

/-- Compiled `expr` quotation slot ready for match dispatch. -/
structure CompiledExprSlot where
  /-- Source syntax of the `` `(expr[rel]| ...) `` quotation. -/
  ref           : Syntax
  /-- Index of the placeholder free variable inside `altLHS.fvarDecls`. -/
  ordVarIdx     : Nat
  /-- Static matching relation for this quotation slot. -/
  rel           : ExprMatchRel
  /-- Compiled closed `ExprPattern` (deferred from aux const emission until dispatch). -/
  pat           : ExprPattern
  /-- Parameter binder indices in `pat` bound by runtime `$pin`s. -/
  pinIdxs       : Array Nat
  /-- Lambda over ordinary pattern variables & earlier binders yielding runtime `$pin` values. -/
  pinsLam       : Expr
  /-- Lambda yielding runtime local `$x` definition relation overrides. -/
  localItemsLam : Expr
  /-- Whether this slot carries any runtime local `$x` definition overrides. -/
  hasLocalItems : Bool := false
  /-- User-visible `?x` pattern variable identifiers bound by this quotation slot. -/
  binders       : Array Ident
  /-- Self-references `$x` inside the same quotation referring to an earlier `?x`. -/
  selfPins      : Array (Ident × Name) := #[]
  deriving Inhabited

/--
Compile an `` `(expr[rel]| p) `` pattern in the current local context (which includes ordinary
pattern vars and earlier quotation binders from the same alternative), without emitting an
auxiliary declaration yet (deferred until `compileExprMatch`).
-/
def elabExprQuotPattern (exprQuotStx : Syntax) (ordVarIdx : Nat) (ctxFVars : Array Expr) :
    TermElabM CompiledExprSlot := withRef exprQuotStx do
  let (rel, localItemExprs) ← elabExprMatchRel exprQuotStx[2]
  let (rewrittenStx, prepState) ← (preprocessExprPatStx exprQuotStx[4]).run {}
  -- Elaborate runtime `$pin` terms in the enclosing local context.
  let mut pinExprs : Array (Nat × Expr) := #[]
  for h : idx in *...prepState.holes.size do
    if let .pin term _ isId := prepState.holes[idx] then
      let pinVal ← elabPinExpr term isId
      pinExprs := pinExprs.push (idx, pinVal)
  -- Compile pattern in empty LCtx; keep `ignoreTCFailures := false` so invalid concrete
  -- instances (e.g. `1 + "hello"`) fail while genuinely stuck implicits stay postponed cleanly.
  let (pat, pinIdxs) ← withoutModifyingElabMetaStateWithInfo <|
    withLCtx {} {} <| withoutErrToSorry <|
    withNewMCtxDepth do
      modify fun s => { s with
        syntheticMVars := {}
        pendingMVars := []
        mvarErrorInfos := []
        levelMVarErrorInfos := []
      }
      -- Register `fixedTermElabs` for each hole placeholder (0-arg occurrences).
      let mut fixedElabs : Array FixedTermElab := #[]
      for holeName in prepState.holeNames do
        fixedElabs := fixedElabs.push fun expectedType? => do
          if let some mvarId := (← getMCtx).findUserName? holeName then
            Term.ensureHasType expectedType? (← instantiateMVars (mkMVar mvarId))
          else
            let ty ← withLCtx {} {} mkFreshTypeMVar
            let mv ← withLCtx {} {} <| mkFreshExprMVar (some ty) .syntheticOpaque holeName
            if let some expTy := expectedType? then
              let mvTy ← inferType mv
              unless ← isDefEq mvTy expTy do
                Term.throwTypeMismatchError none expTy mvTy mv
            return mv
      -- Replace placeholder indices in `elabBodyStx` with fresh `fixedTermElab` offsets.
      let baseOffset := (← read).fixedTermElabs.size
      let elabBodyStx := shiftElabPlaceholders baseOffset rewrittenStx
      let savedMsgs := (← getThe Core.State).messages
      modifyThe Core.State fun s => { s with messages := {} }
      let (e, hasNewErrors) ←
        try
          let e ← withReader (fun ctx => { ctx with
              fixedTermElabs := ctx.fixedTermElabs ++ fixedElabs.map (·.toFixedTermElabRef)
            }) do
              let e ← Term.elabTerm elabBodyStx none
              Term.synthesizeSyntheticMVars (postpone := .partial)
              instantiateMVars e
          let newMsgs := (← getThe Core.State).messages
          modifyThe Core.State fun s => { s with messages := savedMsgs ++ newMsgs }
          pure (e, newMsgs.hasErrors)
        catch ex =>
          let newMsgs := (← getThe Core.State).messages
          modifyThe Core.State fun s => { s with messages := savedMsgs ++ newMsgs }
          throw ex
      if hasNewErrors then
        throwAbortTerm
      let mctx ← getMCtx
      let holeMVars ← (prepState.holeNames.zipIdx).mapM fun (holeName, hIdx) => do
        if let some mvarId := mctx.findUserName? holeName then
          return mkMVar mvarId
        else
          match prepState.holes.getD hIdx (.pin .missing 0 false) with
          | .binder id _ =>
            throwError
              "pattern variable `?{id.getId}` was eliminated during pattern elaboration:\
               {indentD exprQuotStx[4]}"
          | .pin _ _ _ =>
            throwError
              "pin `$...` was eliminated during pattern elaboration:{indentD exprQuotStx[4]}"
      let r ← abstractMVars e
      let firstOrder := computeFirstOrderMask e r.mvars
      let mut binderMVars : Array Expr := #[]
      for bId in prepState.binders do
        let some hIdx := prepState.binderHoleIdx.find? bId.getId
          | throwError "internal error in expr quotation: missing binder index for `?{bId.getId}`"
        binderMVars := binderMVars.push (holeMVars.getD hIdx default)
      let indexOf (mv : Expr) (what : MessageData) : TermElabM Nat := do
        let some j := r.mvars.idxOf? mv
          | throwError "{what} was eliminated during pattern elaboration:\
              {indentD exprQuotStx[4]}"
        return j
      let namedIdx ← prepState.binders.zip binderMVars |>.mapM fun (bId, mv) =>
        indexOf mv m!"pattern variable `?{bId.getId}`"
      let mut pinIndices : Array Nat := #[]
      for (hIdx, _) in pinExprs do
        let mv := holeMVars.getD hIdx default
        if let some j := r.mvars.idxOf? mv then
          pinIndices := pinIndices.push j
        else
          throwError "pin `$...` was eliminated during pattern elaboration:{indentD exprQuotStx[4]}"
      let pat : ExprPattern := {
        levelParams := r.paramNames.toList
        lam         := r.expr
        numVars     := r.numMVars
        namedIdx
        firstOrder
      }
      let pat ← (pat.compile : MetaM ExprPattern)
      return (pat, pinIndices)
  let pinExprList := pinExprs.map (·.2) |>.toList
  let pinsArrayExpr ← mkArrayLit (mkConst ``Expr) pinExprList
  let pinsLam ← mkLambdaFVars ctxFVars pinsArrayExpr
  let boolExprProd := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Bool) (mkConst ``Expr)
  let localItemExprList ← localItemExprs.toList.mapM fun (pos, e) =>
    mkAppM ``Prod.mk #[toExpr pos, e]
  let localItemsArrayExpr ← mkArrayLit boolExprProd localItemExprList
  let localItemsLam ← mkLambdaFVars ctxFVars localItemsArrayExpr
  return {
    ref := exprQuotStx
    ordVarIdx
    rel
    pat
    pinIdxs
    pinsLam
    localItemsLam
    hasLocalItems := !localItemExprs.isEmpty
    binders := prepState.binders
    selfPins := prepState.selfPins
  }

/-! ## Extracting expr quotations from match alternatives -/

/-- Specification of one extracted `expr` quotation slot within a match alternative. -/
structure AltExprSlotSpec where
  /-- Synthetic placeholder identifier inserted into the ordinary match pattern. -/
  placeholderId : Ident
  /-- Original `` `(expr[rel]| ...) `` syntax replaced by `placeholderId`. -/
  exprQuotStx   : Syntax
  /-- Discriminant column index where this slot appeared. -/
  colIdx        : Nat
  deriving Inhabited

/-- Return `true` iff pattern syntax `stx` contains an `` `(expr[rel]| ...) `` quotation. -/
def hasExprQuotInPat (stx : Syntax) : Bool :=
  if isExprQuot stx then true
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then false
  else
    match stx with
    | .node _ k args =>
      if k == ``Parser.Term.typeAscription then
        if h : 1 < args.size then hasExprQuotInPat args[1] else false
      else
        args.any hasExprQuotInPat
    | _ => false
termination_by sizeOf stx
decreasing_by
  · simp_wf
    have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
    omega
  · decreasing_tactic

/-- Return `true` iff any pattern in any alternative contains an `` `(expr| ...) `` quotation. -/
def hasExprQuotInAltViews (altViews : Array (MatchAltView k)) : Bool :=
  altViews.any (·.patterns.any hasExprQuotInPat)

private def collectExprQuotBinderNames (stx : Syntax) : StateRefT (Array Name) TermElabM Unit := do
  if isExprQuot stx then
    let vs ← collectExprQuotPatternVars stx
    modify (· ++ vs.map (·.getId))
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    return
  else
    match stx with
    | .node _ k args =>
      if k == ``Parser.Term.typeAscription then
        if h : 1 < args.size then collectExprQuotBinderNames args[1]
      else
        for a in args do collectExprQuotBinderNames a
    | _ => return
termination_by sizeOf stx
decreasing_by
  · simp_wf
    have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
    omega
  · decreasing_tactic

/--
Return the binder names declared by any `exprQuot` inside `pats`, for generalization shadowing
checks.
-/
def getExprQuotBinderNamesInPats (pats : Array Syntax) : TermElabM (Array Name) := do
  let (_, res) ← (pats.forM collectExprQuotBinderNames).run #[]
  return res

/-- Reject `match h : e` on any discriminant column whose patterns contain an `expr` quotation. -/
def checkNoEqProofOnQuotDiscrs (discrH?s : Array (Option Syntax))
    (altViews : Array (MatchAltView k)) : TermElabM Unit := do
  for h : colIdx in *...discrH?s.size do
    if let some hStx := discrH?s[colIdx] then
      if altViews.any fun alt => alt.patterns[colIdx]?.any hasExprQuotInPat then
        throwErrorAt hStx
          "`{hStx}:` equality proof is not supported on a discriminant matched with `expr` \
           quotations (the `Expr` values may only be related, not equal)"

private def extractPatExprQuots (altIdx colIdx : Nat) (stx : Syntax) :
    StateRefT (Array AltExprSlotSpec) TermElabM Syntax := do
  if isExprQuot stx then
    let slotIdx := (← get).size
    let phId := mkIdentFrom stx (← mkFreshUserName <| Name.mkSimple s!"__eq_{altIdx}_{slotIdx}")
    modify (·.push { placeholderId := phId, exprQuotStx := stx, colIdx })
    return mkNode ``Parser.Term.exprQuotPatSlot #[phId, stx]
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    return stx
  else
    match stx with
    | .node i k args =>
      if k == ``Parser.Term.typeAscription then
        if h : 1 < args.size then
          let inner ← extractPatExprQuots altIdx colIdx args[1]
          return .node i k (args.set 1 inner)
        else
          return .node i k args
      else
        let mut newArgs := Array.emptyWithCapacity args.size
        for a in args do
          newArgs := newArgs.push (← extractPatExprQuots altIdx colIdx a)
        return .node i k newArgs
    | _ => return stx
termination_by sizeOf stx
decreasing_by
  · simp_wf
    have := Array.sizeOf_lt_of_mem (Array.getElem_mem h)
    omega
  · decreasing_tactic

/--
Extract all `` `(expr| ...) `` quotations from each alternative in `altViews`, replacing each
occurrence with an `exprQuotPatSlot` node so Lean's ordinary pattern elaborator checks surrounding
types and constructs ordinary `AltLHS` patterns.
-/
def extractAltExprQuots (altViews : Array (MatchAltView k)) :
    TermElabM (Array (MatchAltView k) × Array (Array AltExprSlotSpec)) := do
  let mut newAltViews := #[]
  let mut allSpecs := #[]
  for h : altIdx in *...altViews.size do
    let alt := altViews[altIdx]
    let mut newPats := #[]
    let mut specs : Array AltExprSlotSpec := #[]
    for hCol : colIdx in *...alt.patterns.size do
      let pat := alt.patterns[colIdx]
      let (newPat, specs') ← (extractPatExprQuots altIdx colIdx pat).run specs
      newPats := newPats.push newPat
      specs := specs'
    newAltViews := newAltViews.push { alt with patterns := newPats }
    allSpecs := allSpecs.push specs
  return (newAltViews, allSpecs)

private def patternHasVar (fv : FVarId) : Meta.Match.Pattern → Bool
  | .var x          => x == fv
  | .as x p _       => x == fv || patternHasVar fv p
  | .ctor _ _ _ fs  => fs.any (patternHasVar fv)
  | .arrayLit _ ps  => ps.any (patternHasVar fv)
  | _               => false

private def withSlotBinders {α} (binders : Array Ident) (j : Nat)
    (quotDecls : Array LocalDecl) (ctxFVars : Array Expr) (bvMap : NameMap Expr)
    (k : Array LocalDecl → Array Expr → NameMap Expr → TermElabM α) : TermElabM α := do
  if h : j < binders.size then
    let bId := binders[j]
    withLocalDeclD bId.getId (mkConst ``Expr) fun bv => do
      Term.addTermInfo' (isBinder := true) bId bv
      let decl ← bv.fvarId!.getDecl
      withSlotBinders binders (j + 1) (quotDecls.push decl) (ctxFVars.push bv)
        (bvMap.insert bId.getId bv) k
  else
    k quotDecls ctxFVars bvMap
termination_by binders.size - j

/--
Check that no `?`-binder in `slots` collides with ordinary pattern variables or earlier `?`-binders
in the same alternative, verify quotations do not occur in inaccessible/parameter positions, and
elaborate each `AltExprSlotSpec` sequentially in `TermElabM`.
-/
def withElaboratedExprSlots {α} (specs : Array AltExprSlotSpec)
    (altPatterns : List Meta.Match.Pattern) (ordFVarDecls : Array LocalDecl) (eqs : Array Expr)
    (k : Array CompiledExprSlot → Array LocalDecl → TermElabM α) : TermElabM α := do
  let ordUserNames : NameSet := ordFVarDecls.foldl (init := {}) fun s d => s.insert d.userName
  let ctxFVars := ordFVarDecls.map LocalDecl.toExpr ++ eqs
  loop 0 #[] #[] ordUserNames ctxFVars
where
  loop (i : Nat) (slots : Array CompiledExprSlot) (quotDecls : Array LocalDecl)
      (usedNames : NameSet) (ctxFVars : Array Expr) : TermElabM α := do
    if h : i < specs.size then
      let spec := specs[i]
      let some ordVarIdx := ordFVarDecls.findIdx? (·.userName == spec.placeholderId.getId)
        | throwErrorAt spec.exprQuotStx
            "invalid `expr` quotation pattern: quotation occurs in an inaccessible or parameter \
             position"
      if hOrd : ordVarIdx < ordFVarDecls.size then
        let phFv := ordFVarDecls[ordVarIdx].fvarId
        unless altPatterns.any (patternHasVar phFv) do
          throwErrorAt spec.exprQuotStx
            "invalid `expr` quotation pattern: quotation occurs in an inaccessible or parameter \
             position"
      let slot ← elabExprQuotPattern spec.exprQuotStx ordVarIdx ctxFVars
      for bId in slot.binders do
        if usedNames.contains bId.getId then
          throwErrorAt bId
            "Invalid pattern variable: Variable name `{bId.getId}` was already used"
      let usedNames' := slot.binders.foldl (init := usedNames) fun s id => s.insert id.getId
      withSlotBinders slot.binders 0 quotDecls ctxFVars {} fun quotDecls' ctxFVars' bvMap => do
        for (pinId, name) in slot.selfPins do
          if let some bv := bvMap.find? name then
            Term.addTermInfo' (isBinder := false) pinId bv
        loop (i + 1) (slots.push slot) quotDecls' usedNames' ctxFVars'
    else
      k slots quotDecls
  termination_by specs.size - i

/-! ## Join-point match dispatch compiler -/

/-- One elaborated alternative ready for join-point `Expr` match compilation. -/
structure ExprMatchAlt where
  /-- Underlying ordinary `AltLHS` pattern and local declarations. -/
  altLHS        : Meta.Match.AltLHS
  /-- Number of discriminant equality proof arguments bound for `h : discr`. -/
  eqsCount      : Nat
  /-- Compiled `expr` quotation slots in left-to-right order. -/
  slots         : Array CompiledExprSlot
  /-- Local declarations introduced by all `?x` binders in `slots`. -/
  quotFVarDecls : Array LocalDecl
  /-- Elaborated right-hand side abstracted over ordinary vars, eq proofs, and `?x` binders. -/
  rhs           : Expr
  /-- Original pattern syntax per `altLHS` column (`none` for synthesized/generalized columns). -/
  origPats      : Array (Option Syntax) := #[]
  deriving Inhabited

/-- Instantiate metavariables in `alt`'s slots, quotation binder declarations, and RHS. -/
def instantiateExprMatchAltMVars (alt : ExprMatchAlt) (newLHS : Meta.Match.AltLHS) :
    TermElabM ExprMatchAlt := do
  let slots ← alt.slots.mapM fun s => do
    return { s with
      pinsLam := ← instantiateMVars s.pinsLam
      localItemsLam := ← instantiateMVars s.localItemsLam
    }
  let quotFVarDecls ← alt.quotFVarDecls.mapM fun d =>
    return d.setType (← instantiateMVars d.type)
  let rhs ← instantiateMVars alt.rhs
  return { alt with altLHS := newLHS, slots, quotFVarDecls, rhs }

private def sameOrdPatternSkeletonList : List Meta.Match.Pattern → List Meta.Match.Pattern → Bool
  | [], [] => true
  | a :: as, b :: bs => sameOrdPatternSkeleton a b && sameOrdPatternSkeletonList as bs
  | _, _ => false
where
  sameOrdPatternSkeleton : Meta.Match.Pattern → Meta.Match.Pattern → Bool
    | .var _, .var _ => true
    | .ctor n₁ us₁ ps₁ fs₁, .ctor n₂ us₂ ps₂ fs₂ =>
      n₁ == n₂ && us₁ == us₂ && ps₁ == ps₂ && sameOrdPatternSkeletonList fs₁ fs₂
    | .arrayLit t₁ ps₁, .arrayLit t₂ ps₂ =>
      t₁ == t₂ && sameOrdPatternSkeletonList ps₁ ps₂
    | .val v₁, .val v₂ => v₁ == v₂
    | .inaccessible e₁, .inaccessible e₂ => e₁ == e₂
    | _, _ => false

private def sameOrdPatternSkeleton (a b : Meta.Match.Pattern) : Bool :=
  sameOrdPatternSkeletonList [a] [b]

private def isSimpleAllVarAlt (alt : ExprMatchAlt) : Bool :=
  alt.eqsCount == 0 &&
  alt.altLHS.fvarDecls.length == alt.altLHS.patterns.length &&
  alt.altLHS.patterns.all fun
    | .var _ => true
    | _      => false

private def collectVarMappingList (psB psT : List Meta.Match.Pattern)
    (baseDecls tgtDecls : List LocalDecl) (ordFVars : Array Expr) :
    StateM (Array (Option Expr)) Unit := do
  match psB, psT with
  | pB :: as, pT :: bs =>
    collectVarMapping pB pT baseDecls tgtDecls ordFVars
    collectVarMappingList as bs baseDecls tgtDecls ordFVars
  | _, _ => return
where
  collectVarMapping (pBase pTgt : Meta.Match.Pattern) (baseDecls tgtDecls : List LocalDecl)
      (ordFVars : Array Expr) : StateM (Array (Option Expr)) Unit := do
    match pBase, pTgt with
    | .var fvB, .var fvT =>
      if let some bIdx := baseDecls.findIdx? (·.fvarId == fvB) then
        if let some tIdx := tgtDecls.findIdx? (·.fvarId == fvT) then
          if let some fv := ordFVars[bIdx]? then
            modify (·.set! tIdx (some fv))
    | .ctor _ _ _ fsB, .ctor _ _ _ fsT =>
      collectVarMappingList fsB fsT baseDecls tgtDecls ordFVars
    | .arrayLit _ psB, .arrayLit _ psT =>
      collectVarMappingList psB psT baseDecls tgtDecls ordFVars
    | _, _ => return

private def mapOrdFVars (baseAlt tgtAlt : ExprMatchAlt) (ordFVars : Array Expr) :
    Option (Array Expr) :=
  let init : Array (Option Expr) := .replicate tgtAlt.altLHS.fvarDecls.length none
  let (_, mapped) :=
    (collectVarMappingList baseAlt.altLHS.patterns tgtAlt.altLHS.patterns
      baseAlt.altLHS.fvarDecls tgtAlt.altLHS.fvarDecls ordFVars).run init
  mapped.mapM id

private def canGroupSameSkeleton (a b : ExprMatchAlt) : Bool :=
  a.eqsCount == 0 && b.eqsCount == 0 &&
  a.altLHS.fvarDecls.length == b.altLHS.fvarDecls.length &&
  a.altLHS.patterns.length == b.altLHS.patterns.length &&
  a.altLHS.fvarDecls.all (fun d => !d.type.hasFVar) &&
  b.altLHS.fvarDecls.all (fun d => !d.type.hasFVar) &&
  sameOrdPatternSkeletonList a.altLHS.patterns b.altLHS.patterns &&
  (mapOrdFVars a b (a.altLHS.fvarDecls.toArray.map LocalDecl.toExpr)).isSome

private def withSlotLetBindings (binders : Array Ident) (xsVar : Expr) (j : Nat)
    (quotFVars ctxArgs : Array Expr)
    (k : Array Expr → Array Expr → TermElabM Expr) : TermElabM Expr := do
  if h : j < binders.size then
    let bId := binders[j]
    let val := mkApp2 (mkConst ``ExprPattern.arg) xsVar (toExpr j)
    withLetDecl bId.getId (mkConst ``Expr) val (nondep := true) fun bv => do
      let body ← withSlotLetBindings binders xsVar (j + 1)
        (quotFVars.push bv) (ctxArgs.push bv) k
      mkLetFVars (generalizeNondepLet := false) #[bv] body
  else
    k quotFVars ctxArgs
termination_by binders.size - j

private def buildMatchSiteError (failCall : Expr) (ex : Exception) : TermElabM Expr := do
  let retTy ← inferType failCall
  let retTyWhnf ← whnf retTy
  if !retTyWhnf.isApp then
    throwError "expr quotation matching requires a monad lifting `MetaM`, \
                got result type{indentExpr retTy}"
  let m := retTyWhnf.appFn!
  let monadInst? ← trySynthInstance (← mkAppM ``Monad #[m])
  let liftInst? ← trySynthInstance (← mkAppOptM ``MonadLiftT #[mkConst ``MetaM, m])
  if !(monadInst? matches .some _) || !(liftInst? matches .some _) then
    throwError "expr quotation matching requires a monad lifting `MetaM`, \
                got result type{indentExpr retTy}\n{ex.toMessageData}"
  throw ex

private def buildSlotChainGo (jpAlt : Expr) (alt : ExprMatchAlt) (ordFVars eqs : Array Expr)
    (failCall : Expr) (slotIdx : Nat) (quotFVars ctxArgs : Array Expr) : TermElabM Expr := do
  if h : slotIdx < alt.slots.size then
    let slot := alt.slots[slotIdx]
    let patConst ← mkAuxPatConst slot.pat
    let scrutinee := ordFVars.getD slot.ordVarIdx default
    let pinIdxsExpr ← mkArrayLit (mkConst ``Nat) (slot.pinIdxs.toList.map toExpr)
    let pinsExpr :=
      if slot.pinIdxs.isEmpty then
        Expr.app (mkConst ``Array.empty [0]) (mkConst ``Expr)
      else
        (slot.pinsLam.beta ctxArgs)
    let onMatchLam ← withLocalDeclD (← mkFreshUserName `__xs)
        (mkApp (mkConst ``Array [0]) (mkConst ``Expr)) fun xsVar => do
      let body ← withSlotLetBindings slot.binders xsVar 0 quotFVars ctxArgs
        fun quotFVars' ctxArgs' =>
          buildSlotChainGo jpAlt alt ordFVars eqs failCall (slotIdx + 1) quotFVars' ctxArgs'
      mkLambdaFVars #[xsVar] body
    let onFailLam ← withLocalDeclD `_ (mkConst ``Unit) fun _u =>
      mkLambdaFVars #[_u] failCall
    try
      if slot.rel.items.isEmpty && !slot.hasLocalItems then
        -- Emit a closed `ResolvedExprMatchRel` so the compiler hoists it with zero allocation.
        let resolvedRelExpr := quoteResolvedExprMatchRel slot.rel
        mkAppM ``ExprPattern.matchResolvedOrElse
          #[patConst, resolvedRelExpr, pinIdxsExpr, pinsExpr, scrutinee, onMatchLam, onFailLam]
      else
        let relExpr ← quoteExprMatchRel slot.rel
        let localItemsExpr := (slot.localItemsLam.beta ctxArgs)
        let siteIdExpr := toExpr (patConst.constName?.getD .anonymous)
        mkAppM ``ExprPattern.matchSiteOrElse
          #[siteIdExpr, patConst, relExpr, pinIdxsExpr, pinsExpr, localItemsExpr, scrutinee,
            onMatchLam, onFailLam]
    catch ex =>
      buildMatchSiteError failCall ex
  else
    let allArgs := ordFVars ++ eqs ++ quotFVars
    if allArgs.isEmpty then
      return mkApp jpAlt (mkConst ``Unit.unit)
    else
      return mkAppN jpAlt allArgs
termination_by alt.slots.size - slotIdx

private def buildSlotChain (jpAlt : Expr) (alt : ExprMatchAlt) (ordFVars eqs : Array Expr)
    (failCall : Expr) : TermElabM Expr :=
  buildSlotChainGo jpAlt alt ordFVars eqs failCall 0 #[] (ordFVars ++ eqs)

private def withEqsFor (discrHNames : Array (Option Name)) (lhs rhs : Array Expr)
    (eqs : Array Expr) (i : Nat) (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if h : i < lhs.size then
    if let some (some hName) := discrHNames[i]? then
      withLocalDeclD hName (← mkEqHEq lhs[i] (rhs.getD i default)) fun eq =>
        withEqsFor discrHNames lhs rhs (eqs.push eq) (i + 1) k
    else
      withEqsFor discrHNames lhs rhs eqs (i + 1) k
  else
    k eqs
termination_by lhs.size - i

private def toHEqProof (p : Expr) : MetaM Expr := do
  let ty ← whnfD (← inferType p)
  if ty.isAppOfArity ``Eq 3 then
    mkAppM ``heq_of_eq #[p]
  else
    pure p

private def combineEqHEq (lhs rhs p1 p2 : Expr) : MetaM Expr := do
  let targetTy ← mkEqHEq lhs rhs
  let p1Ty ← whnfD (← inferType p1)
  let p2Ty ← whnfD (← inferType p2)
  if targetTy.isAppOfArity ``Eq 3 && p1Ty.isAppOfArity ``Eq 3 && p2Ty.isAppOfArity ``Eq 3 then
    mkAppM ``Eq.trans #[p1, p2]
  else
    let h1 ← toHEqProof p1
    let h2 ← toHEqProof p2
    let h ← mkAppM ``HEq.trans #[h1, h2]
    if targetTy.isAppOfArity ``Eq 3 then
      mkAppM ``eq_of_heq #[h]
    else
      pure h

private def combineOrigEqs (discrHNames : Array (Option Name)) (origDiscrs : Array Expr)
    (origEqs? : Option (Array Expr)) (stepArgs stepEqs : Array Expr) : MetaM (Array Expr) := do
  match origEqs? with
  | none => return stepEqs
  | some origEqs =>
    let mut res : Array Expr := #[]
    let mut eqIdx := 0
    for h : i in *...discrHNames.size do
      if discrHNames[i].isSome then
        let origEq := origEqs.getD eqIdx default
        let stepEq := stepEqs.getD eqIdx default
        let combined ←
          combineEqHEq (origDiscrs.getD i default) (stepArgs.getD i default) origEq stepEq
        res := res.push combined
        eqIdx := eqIdx + 1
    return res

private def mkOrdMinor (discrHNames : Array (Option Name)) (origDiscrs : Array Expr)
    (origEqs? : Option (Array Expr)) (jpAlt : Expr) (alt : ExprMatchAlt)
    (discrExprs : Array Expr) : TermElabM Expr := do
  withExistingLocalDecls alt.altLHS.fvarDecls do
    let ordFVars := alt.altLHS.fvarDecls.toArray.map LocalDecl.toExpr
    let args ← alt.altLHS.patterns.toArray.mapM (Meta.Match.Pattern.toExpr · (annotate := false))
    withEqsFor discrHNames discrExprs args #[] 0 fun eqs => do
      let combinedEqs ← combineOrigEqs discrHNames origDiscrs origEqs? args eqs
      let allArgs := ordFVars ++ combinedEqs
      let call :=
        if allArgs.isEmpty then mkApp jpAlt (mkConst ``Unit.unit)
        else mkAppN jpAlt allArgs
      if (ordFVars ++ eqs).isEmpty then
        return mkSimpleThunk call
      else
        mkLambdaFVars (ordFVars ++ eqs) call

private def mkCatchAllAltLHS (curMatchType : Expr) (numDiscrs : Nat) :
    TermElabM Meta.Match.AltLHS := do
  forallBoundedTelescope curMatchType numDiscrs fun xs _ => do
    let decls ← xs.toList.mapM (·.fvarId!.getDecl)
    let pats := xs.toList.map fun x => Meta.Match.Pattern.var x.fvarId!
    return { ref := ← getRef, fvarDecls := decls, patterns := pats }

private def mkCatchAllMinor (discrHNames : Array (Option Name)) (origDiscrs discrExprs : Array Expr)
    (origEqs? : Option (Array Expr)) (catchAllLHS : Meta.Match.AltLHS)
    (mkFailCall : Array Expr → Array Expr → TermElabM Expr) :
    TermElabM Expr := do
  withExistingLocalDecls catchAllLHS.fvarDecls do
    let vars := catchAllLHS.fvarDecls.toArray.map LocalDecl.toExpr
    withEqsFor discrHNames discrExprs vars #[] 0 fun eqs => do
      let combinedEqs ← combineOrigEqs discrHNames origDiscrs origEqs? vars eqs
      let body ← mkFailCall vars combinedEqs
      mkLambdaFVars (vars ++ eqs) body

private def mapSimpleAllVarArgs (alt : ExprMatchAlt) (curDiscrs : Array Expr) :
    Option (Array Expr) :=
  let pats := alt.altLHS.patterns
  alt.altLHS.fvarDecls.toArray.mapM fun decl =>
    (pats.findIdx? fun
      | .var fv => fv == decl.fvarId
      | _       => false).bind (curDiscrs[·]?)

private def buildGroupChain (jpAlts : Array Expr) (alts : Array ExprMatchAlt)
    (i : Nat) (ordFVars combinedEqs : Array Expr) (j : Nat) (nextExpr : Expr) :
    TermElabM Expr := do
  let altJ := alts.getD j default
  let some mappedOrdFVars :=
    (if j == i then some ordFVars else mapOrdFVars (alts.getD i default) altJ ordFVars)
    | throwError "internal error in expr quotation match compilation: \
                  failed to map pattern variables"
  let cur ← buildSlotChain (jpAlts.getD j default) altJ mappedOrdFVars combinedEqs nextExpr
  if hgt : i < j then
    if (alts.getD (j - 1) default).slots.size > 1 then
      let curTy ← inferType cur
      let jpTy ← mkArrow (mkConst ``Unit) curTy
      let jpLam := mkLambda `_ .default (mkConst ``Unit) cur
      withLetDecl (← mkFreshUserName `__do_jp) jpTy jpLam (nondep := true)
          (kind := .implDetail) fun jp => do
        let upper ← buildGroupChain jpAlts alts i ordFVars combinedEqs (j - 1)
          (mkApp jp (mkConst ``Unit.unit))
        mkLetFVars (generalizeNondepLet := false) #[jp] upper
    else
      buildGroupChain jpAlts alts i ordFVars combinedEqs (j - 1) cur
  else
    return cur
termination_by j

private def buildExprMatchDispatch (discrHNames : Array (Option Name)) (origDiscrs : Array Expr)
    (isDep isExhaustive : Bool) (alts : Array ExprMatchAlt) (jpAlts : Array Expr)
    (startIdx : Nat) (curDiscrs : Array Expr) (origEqs? : Option (Array Expr))
    (curMatchType : Expr) : TermElabM Expr := do
  let discrInfos : Array Meta.Match.DiscrInfo := discrHNames.map fun hName? => { hName? }
  let firstRef? := (Array.range (alts.size - startIdx)).findSome? fun off =>
    let idx := startIdx + off
    if h : idx < alts.size then
      if !alts[idx].slots.isEmpty then some idx else none
    else
      none
  match firstRef? with
  | none =>
    let tailIdxs := (Array.range (alts.size - startIdx)).map (startIdx + ·)
    let prevIrrefs := (Array.range (min startIdx alts.size)).filter fun k =>
      (alts.getD k default).slots.isEmpty
    let allIdxs := tailIdxs ++ prevIrrefs
    if hSingle : allIdxs.size = 1 then
      let onlyIdx := allIdxs[0]
      let onlyAlt := alts.getD onlyIdx default
      if !isDep && discrHNames.all (·.isNone) && isSimpleAllVarAlt onlyAlt then
        if let some mapped := mapSimpleAllVarArgs onlyAlt curDiscrs then
          let jp := jpAlts.getD onlyIdx default
          return if mapped.isEmpty then mkApp jp (mkConst ``Unit.unit) else mkAppN jp mapped
    let lhss := allIdxs.toList.map fun k => (alts.getD k default).altLHS
    let matcherName ← Term.mkAuxName `match
    let matcherResult ← Meta.Match.mkMatcher {
      matcherName
      matchType := curMatchType
      discrInfos
      lhss
    }
    matcherResult.addMatcher
    let minors ← allIdxs.mapM fun altIdx =>
      mkOrdMinor discrHNames origDiscrs origEqs?
        (jpAlts.getD altIdx default) (alts.getD altIdx default) curDiscrs
    let motive ← forallBoundedTelescope curMatchType curDiscrs.size fun xs body =>
      mkLambdaFVars xs body
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r curDiscrs
    return mkAppN r minors
  | some i =>
    if hFirst : startIdx <= i ∧ i < alts.size then
      let mut iEnd := i
      while hNext : iEnd + 1 < alts.size do
        if !alts[iEnd + 1].slots.isEmpty &&
            canGroupSameSkeleton (alts.getD i default) alts[iEnd + 1] then
          iEnd := iEnd + 1
        else
          break
      let nextIdx := max (i + 1) (iEnd + 1)
      let hasNext := nextIdx < alts.size
      let getNonDepRetType : TermElabM Expr :=
        forallBoundedTelescope curMatchType curDiscrs.size fun _ body => pure body
      let withFailJP (k : (Array Expr → Array Expr → TermElabM Expr) → TermElabM Expr) :
          TermElabM Expr := do
        if !hasNext && !isExhaustive then
          -- Non-exhaustive match (compile error already reported); synthesize `sorry` for recovery.
          let mkFail (args _eqArgs : Array Expr) : TermElabM Expr := do
            let ty ←
              if isDep then
                forallBoundedTelescope curMatchType curDiscrs.size fun xs body =>
                  return body.replaceFVars xs args
              else
                getNonDepRetType
            mkSorry ty (synthetic := true)
          k mkFail
        else if !isDep then
          let retType ← getNonDepRetType
          let jpTy ← mkArrow (mkConst ``Unit) retType
          let failBody ← buildExprMatchDispatch discrHNames origDiscrs isDep isExhaustive
            alts jpAlts nextIdx curDiscrs origEqs? curMatchType
          let failLam := mkLambda `_ .default (mkConst ``Unit) failBody
          withLetDecl (← mkFreshUserName `__do_jp) jpTy failLam (nondep := true)
              (kind := .implDetail) fun jp => do
            let res ← k fun _ _ => return mkApp jp (mkConst ``Unit.unit)
            mkLetFVars (generalizeNondepLet := false) #[jp] res
        else
          forallBoundedTelescope curMatchType curDiscrs.size fun newDiscrs retBody =>
            withEqsFor discrHNames origDiscrs newDiscrs #[] 0 fun newOrigEqs => do
              let failBody ← buildExprMatchDispatch discrHNames origDiscrs isDep isExhaustive
                alts jpAlts nextIdx newDiscrs (some newOrigEqs) curMatchType
              let failLam ← mkLambdaFVars (newDiscrs ++ newOrigEqs) failBody
              let jpTy ← mkForallFVars (newDiscrs ++ newOrigEqs) retBody
              withLetDecl (← mkFreshUserName `__do_jp) jpTy failLam (nondep := true)
                  (kind := .implDetail) fun jp => do
                let res ← k fun args eqArgs => return mkAppN jp (args ++ eqArgs)
                mkLetFVars (generalizeNondepLet := false) #[jp] res

      withFailJP fun mkFailCall => do
        let altI := alts[i]
        if startIdx == i && i == iEnd && !isDep && discrHNames.all (·.isNone) &&
            isSimpleAllVarAlt altI then
          if let some ordMap := mapSimpleAllVarArgs altI curDiscrs then
            return ← buildSlotChain (jpAlts.getD i default) altI ordMap #[]
              (← mkFailCall curDiscrs #[])

        let prefixIdxs := (Array.range (i - startIdx)).map (startIdx + ·)
        let catchAllLHS ← mkCatchAllAltLHS curMatchType curDiscrs.size
        let stepLHSS :=
          (prefixIdxs.toList.map fun k => (alts.getD k default).altLHS) ++
          [altI.altLHS, catchAllLHS]
        let matcherName ← Term.mkAuxName `match
        let matcherResult ← Meta.Match.mkMatcher {
          matcherName
          matchType := curMatchType
          discrInfos
          lhss := stepLHSS
        }
        matcherResult.addMatcher
        let prefixMinors ← prefixIdxs.mapM fun altIdx =>
          mkOrdMinor discrHNames origDiscrs origEqs?
            (jpAlts.getD altIdx default) (alts.getD altIdx default) curDiscrs
        let groupMinor ← withExistingLocalDecls altI.altLHS.fvarDecls do
          let ordFVars := altI.altLHS.fvarDecls.toArray.map LocalDecl.toExpr
          let failArgs ← altI.altLHS.patterns.toArray.mapM
            (Meta.Match.Pattern.toExpr · (annotate := false))
          withEqsFor discrHNames curDiscrs failArgs #[] 0 fun eqs => do
            let combinedEqs ← combineOrigEqs discrHNames origDiscrs origEqs? failArgs eqs
            let failCall ← mkFailCall failArgs combinedEqs
            let chain ← buildGroupChain jpAlts alts i ordFVars combinedEqs iEnd failCall
            mkLambdaFVars (ordFVars ++ eqs) chain
        let catchAllMinor ←
          mkCatchAllMinor discrHNames origDiscrs curDiscrs origEqs? catchAllLHS mkFailCall
        let minors := prefixMinors ++ #[groupMinor, catchAllMinor]
        let motive ← forallBoundedTelescope curMatchType curDiscrs.size fun xs body =>
          mkLambdaFVars xs body
        let r := mkApp matcherResult.matcher motive
        let r := mkAppN r curDiscrs
        return mkAppN r minors
    else
      throwError "internal error in expr quotation match compilation: invalid slot index"
termination_by alts.size - startIdx

private def bindAltJPsAndDispatch (discrHNames : Array (Option Name)) (matchType : Expr)
    (isDep isExhaustive : Bool) (alts : Array ExprMatchAlt) (curDiscrs : Array Expr)
    (idx : Nat) (jpAlts : Array Expr) : TermElabM Expr := do
  if h : idx < alts.size then
    let rhs := alts[idx].rhs
    let rhsTy ← inferType rhs
    withLetDecl (← mkFreshUserName `__do_jp) rhsTy rhs (nondep := true)
        (kind := .implDetail) fun jp => do
      let body ← bindAltJPsAndDispatch discrHNames matchType isDep isExhaustive
        alts curDiscrs (idx + 1) (jpAlts.push jp)
      mkLetFVars (generalizeNondepLet := false) (usedLetOnly := true) #[jp] body
  else
    buildExprMatchDispatch discrHNames curDiscrs isDep isExhaustive alts jpAlts 0 curDiscrs
      none matchType
termination_by alts.size - idx

private def bindDiscrsAndDispatch (discrs : Array Expr) (discrHNames : Array (Option Name))
    (matchType : Expr) (isDep isExhaustive : Bool) (alts : Array ExprMatchAlt)
    (idx : Nat) (curDiscrs : Array Expr) : TermElabM Expr := do
  if h : idx < discrs.size then
    let d := discrs[idx]
    if !isDep && !d.isFVar then
      let dTy ← inferType d
      withLetDecl (← mkFreshUserName `__discr) dTy d (nondep := false)
          (kind := .implDetail) fun dv => do
        let body ← bindDiscrsAndDispatch discrs discrHNames matchType isDep isExhaustive
          alts (idx + 1) (curDiscrs.push dv)
        mkLetFVars (generalizeNondepLet := false) #[dv] body
    else
      bindDiscrsAndDispatch discrs discrHNames matchType isDep isExhaustive
        alts (idx + 1) (curDiscrs.push d)
  else
    bindAltJPsAndDispatch discrHNames matchType isDep isExhaustive alts curDiscrs 0 #[]
termination_by discrs.size - idx

private def renderPatWithSlots (slotSyntaxMap : Std.HashMap FVarId Syntax) :
    Meta.Match.Pattern → MetaM MessageData
  | .var fv =>
    match slotSyntaxMap[fv]? with
    | some stx => return m!"{stx}"
    | none     => return toMessageData (mkFVar fv)
  | .as x p _ => return m!"{mkFVar x}@{← renderPatWithSlots slotSyntaxMap p}"
  | .arrayLit _ ps => do
    let items ← goList ps
    return m!"#[{MessageData.joinSep items ", "}]"
  | p => return toMessageData (← Meta.Match.Pattern.toExpr p)
where
  goList : List Meta.Match.Pattern → MetaM (List MessageData)
    | []      => return []
    | p :: ps => return (← renderPatWithSlots slotSyntaxMap p) :: (← goList ps)

private def renderExprMatchAltPatterns (alt : ExprMatchAlt) : TermElabM MessageData := do
  withExistingLocalDecls alt.altLHS.fvarDecls do
    let decls := alt.altLHS.fvarDecls.toArray
    let mut slotFVs : FVarIdSet := {}
    let mut slotSyntaxMap : Std.HashMap FVarId Syntax := {}
    for slot in alt.slots do
      if let some d := decls[slot.ordVarIdx]? then
        slotFVs := slotFVs.insert d.fvarId
        slotSyntaxMap := slotSyntaxMap.insert d.fvarId slot.ref
    let rec hasSlotFV : Meta.Match.Pattern → Bool
      | .var fv         => slotFVs.contains fv
      | .as x p _       => slotFVs.contains x || hasSlotFV p
      | .ctor _ _ _ fs  => fs.any hasSlotFV
      | .arrayLit _ ps  => ps.any hasSlotFV
      | _               => false
    let mut parts : List MessageData := []
    for h : colIdx in *...alt.altLHS.patterns.length do
      let p := alt.altLHS.patterns[colIdx]
      if hasSlotFV p then
        if let some (some origStx) := alt.origPats[colIdx]? then
          parts := parts.concat m!"{origStx}"
        else
          parts := parts.concat (← renderPatWithSlots slotSyntaxMap p)
      else
        parts := parts.concat (toMessageData (← Meta.Match.Pattern.toExpr p))
    return MessageData.joinSep parts ", "

/--
Compile a `match` that contains one or more `` `(expr| ...) `` patterns, using Lean's
`Meta.Match.mkMatcher` for ordinary patterns, checking exhaustiveness & redundancy accurately,
and compiling fall-through via join points without code duplication or `sorryAx` under
`match.ignoreUnusedAlts`.
-/
def compileExprMatch (discrs : Array Expr) (discrHNames : Array (Option Name))
    (matchType : Expr) (isDep : Bool) (alts : Array ExprMatchAlt)
    (reportMatcherErrors : List Meta.Match.AltLHS → Meta.Match.MatcherResult → TermElabM Unit)
    (reportUnusedAlt : Meta.Match.AltLHS → MessageData → TermElabM Unit) : TermElabM Expr := do
  let discrInfos : Array Meta.Match.DiscrInfo := discrHNames.map fun hName? => { hName? }
  -- 1. Exhaustiveness & redundancy check on irrefutable alternatives + refutable shadows.
  let irrefIdxs := (Array.range alts.size).filter fun i => (alts.getD i default).slots.isEmpty
  let irrefLHSS := irrefIdxs.toList.map fun i => (alts.getD i default).altLHS
  -- Use a static non-emitted check name (`addMatcher` is never called here).
  let checkBase := (← read).declName?.getD `expr_match_check
  let irrefRes ← Meta.Match.mkMatcher {
    matcherName := checkBase ++ `_irref_check
    matchType
    discrInfos
    lhss := irrefLHSS
  }
  let isExhaustive := irrefRes.counterExamples.isEmpty
  if !isExhaustive then
    reportMatcherErrors irrefLHSS irrefRes
  else
    unless irrefRes.unusedAltIdxs.isEmpty do
      reportMatcherErrors irrefLHSS irrefRes
    for h : i in *...alts.size do
      unless alts[i].slots.isEmpty do
        let prevIrrefs :=
          ((Array.range i).filter fun k => (alts.getD k default).slots.isEmpty).toList.map
            fun k => (alts.getD k default).altLHS
        unless prevIrrefs.isEmpty do
          let shadowRes ← Meta.Match.mkMatcher {
            matcherName := checkBase ++ `_shadow_check
            matchType
            discrInfos
            lhss := prevIrrefs ++ [alts[i].altLHS]
          }
          if shadowRes.unusedAltIdxs.contains prevIrrefs.length then
            let patsMsg ← renderExprMatchAltPatterns alts[i]
            reportUnusedAlt alts[i].altLHS patsMsg

  -- 2. Bind non-fvar discriminants once when non-dependent, then emit join-point dispatch.
  bindDiscrsAndDispatch discrs discrHNames matchType isDep isExhaustive alts 0 #[]

/-! ## Term-position building `` `(expr[rel]| t) `` -/

private inductive TermPlaceholderKind where
  | splice (term : Syntax) (isIdent : Bool)
  | hole (userName? : Option Name)
  deriving Inhabited

private structure TermPreprocessState where
  kinds           : Array TermPlaceholderKind := #[]
  holeNames       : Array Name := #[]
  namedHoleIdxs   : NameMap Nat := {}
  namedSpliceIdxs : NameMap Nat := {}

private def recordTermPlaceholder (k : TermPlaceholderKind) (baseName : Name) :
    StateT TermPreprocessState TermElabM (Nat × Name) := do
  let idx := (← get).kinds.size
  let holeName ← mkFreshUserName baseName
  modify fun s => { s with
    kinds     := s.kinds.push k
    holeNames := s.holeNames.push holeName
  }
  return (idx, holeName)

private def recordTermSplice (aqTerm : Syntax) :
    StateT TermPreprocessState TermElabM (Nat × Name) := do
  if aqTerm.isIdent then
    let name := aqTerm.getId
    if let some idx := (← get).namedSpliceIdxs.find? name then
      return (idx, (← get).holeNames.getD idx `__eqSplice)
    let (idx, holeName) ← recordTermPlaceholder (.splice aqTerm true) (`__eqSplice ++ name)
    modify fun s => { s with namedSpliceIdxs := s.namedSpliceIdxs.insert name idx }
    return (idx, holeName)
  else
    recordTermPlaceholder (.splice aqTerm false) `__eqSplice

private def recordTermHole (holeStx : Syntax) :
    StateT TermPreprocessState TermElabM (Nat × Name) := do
  if holeStx[1].isIdent then
    let id : Ident := ⟨holeStx[1]⟩
    let name := id.getId
    if let some idx := (← get).namedHoleIdxs.find? name then
      return (idx, (← get).holeNames.getD idx name)
    let (idx, holeName) ← recordTermPlaceholder (.hole (some name)) (`__eqHole ++ name)
    modify fun s => { s with namedHoleIdxs := s.namedHoleIdxs.insert name idx }
    return (idx, holeName)
  else
    recordTermPlaceholder (.hole none) `__eqHole_anon

private def preprocessTermAppHead (fnStx : Syntax)
    (elabArgs : StateT TermPreprocessState TermElabM (Array Syntax)) :
    StateT TermPreprocessState TermElabM (Option Syntax) := do
  if fnStx.isOfKind ``Parser.Term.syntheticHole then
    let (idx, holeName) ← recordTermHole fnStx
    let newArgs ← elabArgs
    return some <| mkHoleAppOrApp fnStx idx holeName newArgs
  else if fnStx.isAntiquot && !fnStx.isEscapedAntiquot then
    let aqTerm := fnStx.getAntiquotTerm
    if aqTerm.isOfKind ``Parser.Term.hole then
      throwErrorAt fnStx "expected `$e` splice; use `?_` for a metavariable hole"
    let newArgs ← elabArgs
    let (idx, holeName) ← recordTermSplice aqTerm
    return some <| mkHoleAppOrApp fnStx idx holeName newArgs
  else
    return none

private def preprocessExprTermStx (stx : Syntax) :
    StateT TermPreprocessState TermElabM Syntax := do
  if stx.isOfKind ``Parser.Term.syntheticHole then
    let (idx, _) ← recordTermHole stx
    return mkPlaceholderSyntax stx idx
  if stx.isAntiquot then
    if stx.isEscapedAntiquot then
      return Syntax.unescapeAntiquot stx
    let aqTerm := stx.getAntiquotTerm
    if aqTerm.isOfKind ``Parser.Term.hole then
      throwErrorAt stx "expected `$e` splice; use `?_` for a metavariable hole"
    let (idx, _) ← recordTermSplice aqTerm
    return mkPlaceholderSyntax stx idx
  if stx.isQuot || isExprQuot stx then
    return stx
  match stx with
  | .node i k args =>
    if k == ``Parser.Term.app then
      if _h0 : 0 < args.size then
        if h1 : 1 < args.size then
          let fnStx := args[0]
          let argsNode := args[1]
          let elabArgs : StateT TermPreprocessState TermElabM (Array Syntax) :=
            match hNode : argsNode with
            | .node _ _ innerArgs => do
              let mut out := Array.emptyWithCapacity innerArgs.size
              for hMem : a in innerArgs do
                have hSub1 : sizeOf a < sizeOf innerArgs := Array.sizeOf_lt_of_mem hMem
                have hSub2 : sizeOf argsNode < sizeOf args :=
                  Array.sizeOf_lt_of_mem (Array.getElem_mem h1)
                have hNodeSize : sizeOf innerArgs < sizeOf argsNode := by
                  rw [hNode]; simp_wf; omega
                have hSize : sizeOf a < 1 + sizeOf i + sizeOf k + sizeOf args := by omega
                out := out.push (← preprocessExprTermStx a)
              return out
            | _ => return #[]
          if let some res ← preprocessTermAppHead fnStx elabArgs then
            return res
    let mut newArgs := Array.emptyWithCapacity args.size
    for a in args do
      newArgs := newArgs.push (← preprocessExprTermStx a)
    return .node i k newArgs
  | _ => return stx
termination_by sizeOf stx

private def addExprDepsAtDepth (curDepth : Nat) (ty : Expr)
    (detM : MVarIdSet) (detL : Std.HashSet LMVarId) :
    TermElabM (MVarIdSet × Std.HashSet LMVarId) := do
  let ty ← instantiateMVars ty
  let mvs ← getMVars ty
  let lvs := (collectLevelMVars {} ty).result
  let mctx ← getMCtx
  let mut detM' := detM
  for m in mvs do
    if (mctx.findDecl? m).any (·.depth == curDepth) then
      detM' := detM'.insert m
  let mut detL' := detL
  for l in lvs do
    if mctx.getLevelDepth l == curDepth then
      detL' := detL'.insert l
  return (detM', detL')

private def exprMVarsAndLevelsSubset (curDepth : Nat) (mctx : MetavarContext)
    (e : Expr) (detM : MVarIdSet) (detL : Std.HashSet LMVarId) : TermElabM Bool := do
  let e ← instantiateMVars e
  let mvs ← getMVars e
  for m in mvs do
    if (mctx.findDecl? m).any (·.depth == curDepth) then
      unless detM.contains m do
        return false
  let lvs := (collectLevelMVars {} e).result
  for l in lvs do
    if mctx.getLevelDepth l == curDepth then
      unless detL.contains l do
        return false
  return true

private def levelMVarsSubset (curDepth : Nat) (mctx : MetavarContext)
    (u : Level) (detL : Std.HashSet LMVarId) : Bool :=
  let lvs := (collectLevelMVars {} (mkSort u)).result
  lvs.all fun l =>
    if mctx.getLevelDepth l == curDepth then detL.contains l else true

private def computeTemplateDetermined (curDepth : Nat) (rMVars : Array Expr)
    (spliceMap : Std.HashMap MVarId Nat) (pendingTCMap : Std.HashMap MVarId Expr) :
    TermElabM (MVarIdSet × Std.HashSet LMVarId × MVarIdSet) := do
  let mut detM : MVarIdSet := {}
  let mut detL : Std.HashSet LMVarId := {}
  let mut validTCs : MVarIdSet := {}
  let mut expanded : MVarIdSet := {}
  for (mId, _) in spliceMap do
    detM := detM.insert mId
  for _ in *...(rMVars.size + 2) do
    let mut progressed := false
    let curList := detM.toList
    for mId in curList do
      unless expanded.contains mId do
        expanded := expanded.insert mId
        if let some decl := (← getMCtx).findDecl? mId then
          let (detM', detL') ← addExprDepsAtDepth curDepth decl.type detM detL
          if detM'.size != detM.size || detL'.size != detL.size then
            progressed := true
          detM := detM'
          detL := detL'
    for mv in rMVars do
      let id := mv.mvarId!
      if pendingTCMap.contains id && !validTCs.contains id then
        let tcTy ← instantiateMVars (← id.getDecl).type
        let mctx ← getMCtx
        let inputsOk ←
          match ← inspectClassGoalInputs? tcTy with
          | none => exprMVarsAndLevelsSubset curDepth mctx tcTy detM detL
          | some (inExprs, inLvls) =>
            let eOk ← inExprs.allM (exprMVarsAndLevelsSubset curDepth mctx · detM detL)
            let lOk := inLvls.all (levelMVarsSubset curDepth mctx · detL)
            pure (eOk && lOk)
        if inputsOk then
          validTCs := validTCs.insert id
          let (detM', detL') ← addExprDepsAtDepth curDepth tcTy detM detL
          detM := detM'
          detL := detL'
          progressed := true
    unless progressed do
      break
  return (detM, detL, validTCs)

private def reportTermBuildErrors (e : Expr) (refStx : Syntax)
    (badMVars : Array MVarId) (badLMVars : Array LMVarId)
    (pendingTCMap : Std.HashMap MVarId Expr)
    (autoHoleTypes : Std.HashMap MVarId (Option Name)) : TermElabM Unit := do
  -- Keep only `badMVars` errors in `Core.State.messages` while calling `logUnassigned*`
  -- so `MonadLog.hasErrors` does not mask them; callers restore saved messages in `finally`.
  for id in badMVars do
    if pendingTCMap.contains id then
      if let some syn ← Term.getSyntheticMVarDecl? id then
        try
          let tcTy ← instantiateMVars (← id.getDecl).type
          discard <| synthInstance tcTy
        catch ex =>
          logErrorAt syn.stx ex.toMessageData
          throwAbortTerm
      let tcTy ← instantiateMVars (← id.getDecl).type
      throwErrorAt refStx "failed to synthesize instance of type class{indentExpr tcTy}"
    if let some syn ← Term.getSyntheticMVarDecl? id then
      throwErrorAt syn.stx
        "invalid `expr` quotation: unresolved coercion or postponed elaboration\
         {indentExpr (← instantiateMVars (← id.getDecl).type)}"
    if let some userName? := autoHoleTypes[id]? then
      let holeStr := match userName? with
        | some n => s!"?{n}"
        | none   => "?_"
      throwErrorAt refStx
        "invalid `expr` quotation: hole `{holeStr}` has unresolved type; \
         add a type annotation `({holeStr} : T)`"
  if h : 0 < badMVars.size then
    if ← Term.logUnassignedUsingErrorInfos badMVars then
      throwAbortTerm
    let firstId := badMVars[0]
    let ty ← instantiateMVars (← firstId.getDecl).type
    let mut ref := refStx
    for info in (← get).mvarErrorInfos do
      if info.mvarId == firstId then
        ref := info.ref
        break
    throwErrorAt ref
      "invalid `expr` quotation: unresolved placeholder or implicit argument of type{indentExpr ty}"
  unless badLMVars.isEmpty do
    if ← Term.logUnassignedLevelMVarsUsingErrorInfos badLMVars then
      throwAbortTerm
    throwErrorAt refStx
      "invalid `expr` quotation: unresolved universe level metavariables in{indentExpr e}"

/--
Elaborate a term-position `` `(expr[rel]| t) `` quotation into a `MetaM Expr` expression that
substitutes runtime `$e` splices into a compile-time closed template without beta-reduction or
metavariable allocation for splices, checks splice types under `rel`, synthesizes splice-dependent
type-class instances at run time, and instantiates `?h` / `?_` refine holes cleanly.
-/
@[builtin_term_elab Lean.Parser.Term.exprQuot] def elabExprQuotTerm : TermElab :=
    fun stx expectedType? => withRef stx do
  let (rel, localItemExprs) ← elabExprMatchRel stx[2] (defaultEngine := .defeq)
  if rel.engine == .sym then
    throwErrorAt stx "expr quotation `/sym` building engine is not implemented yet (Spike B / B5)"
  let (rewrittenStx, prepState) ← (preprocessExprTermStx stx[4]).run {}
  let mut spliceExprs : Array (Nat × Expr) := #[]
  for h : idx in *...prepState.kinds.size do
    if let .splice term isId := prepState.kinds[idx] then
      let sVal ← elabPinExpr term isId
      spliceExprs := spliceExprs.push (idx, sVal)
  let (tmpl, splicesArgList) ← withoutModifyingElabMetaStateWithInfo <|
    withLCtx {} {} <| withoutErrToSorry <| Term.withoutAutoBoundImplicit <|
    withNewMCtxDepth do
      modify fun s => { s with
        syntheticMVars := {}
        pendingMVars := []
        mvarErrorInfos := []
        levelMVarErrorInfos := []
      }
      let autoHoleTypesRef ← IO.mkRef ({} : Std.HashMap MVarId (Option Name))
      let mut fixedElabs : Array FixedTermElab := #[]
      for h : idx in *...prepState.holeNames.size do
        let holeName := prepState.holeNames[idx]
        let kind := prepState.kinds.getD idx (.hole none)
        fixedElabs := fixedElabs.push fun expTy? => do
          if let some mvarId := (← getMCtx).findUserName? holeName then
            Term.ensureHasType expTy? (← instantiateMVars (mkMVar mvarId))
          else
            let u ← withLCtx {} {} mkFreshLevelMVar
            let tyMV ← withLCtx {} {} <| mkFreshExprMVar (some (mkSort u))
            let mv ← withLCtx {} {} <| mkFreshExprMVar (some tyMV) .syntheticOpaque holeName
            if let .hole userName? := kind then
              if expTy?.isNone then
                autoHoleTypesRef.modify (·.insert tyMV.mvarId! userName?)
            Term.ensureHasType expTy? mv
      let baseOffset := (← read).fixedTermElabs.size
      let elabBodyStx := shiftElabPlaceholders baseOffset rewrittenStx
      let savedMsgs := (← getThe Core.State).messages
      modifyThe Core.State fun s => { s with messages := {} }
      let restoreMsgs : TermElabM Unit := do
        let curMsgs := (← getThe Core.State).messages
        modifyThe Core.State fun s => { s with messages := savedMsgs ++ curMsgs }
      let e ←
        try
          let e ← withReader (fun ctx => { ctx with
              fixedTermElabs := ctx.fixedTermElabs ++ fixedElabs.map (·.toFixedTermElabRef)
            }) do
              let e ← Term.elabTerm elabBodyStx none
              Term.synthesizeSyntheticMVars (postpone := .partial)
              instantiateMVars e
          if (← getThe Core.State).messages.hasErrors then
            restoreMsgs
            throwAbortTerm
          pure e
        catch ex =>
          restoreMsgs
          throw ex
      let curDepth := (← getMCtx).depth
      let mctx ← getMCtx
      let holeMVars ← (prepState.holeNames.zipIdx).mapM fun (holeName, hIdx) => do
        if let some mvarId := mctx.findUserName? holeName then
          return mkMVar mvarId
        else
          restoreMsgs
          match prepState.kinds.getD hIdx (.hole none) with
          | .splice _ _ =>
            throwError "splice `$...` was eliminated during quotation elaboration:\
              {indentD stx[4]}"
          | .hole userName? =>
            let hStr := match userName? with | some n => s!"?{n}" | none => "?_"
            throwError "hole `{hStr}` was eliminated during quotation elaboration:\
              {indentD stx[4]}"
      let mut spliceMap : Std.HashMap MVarId Nat := {}
      let mut orderedSplices : Array Expr := #[]
      for (hIdx, sExpr) in spliceExprs do
        let mv := holeMVars.getD hIdx default
        let pos := orderedSplices.size
        spliceMap := spliceMap.insert mv.mvarId! pos
        orderedSplices := orderedSplices.push sExpr
      let mut holeMap : Std.HashMap MVarId (Option Name) := {}
      for h : hIdx in *...prepState.kinds.size do
        if let .hole userName? := prepState.kinds[hIdx] then
          let mv := holeMVars.getD hIdx default
          holeMap := holeMap.insert mv.mvarId! userName?
      let mut pendingTCMap : Std.HashMap MVarId Expr := {}
      for pm in (← get).pendingMVars do
        if let some { kind := .typeClass _, .. } ← Term.getSyntheticMVarDecl? pm then
          pendingTCMap := pendingTCMap.insert pm (← instantiateMVars (← pm.getDecl).type)
      let r ← abstractMVars e
      let (detMVars, detLMVars, validTCs) ←
        computeTemplateDetermined curDepth r.mvars spliceMap pendingTCMap
      let mut badMVars : Array MVarId := #[]
      let mut varKinds : Array ExprTemplateVarKind := Array.emptyWithCapacity r.mvars.size
      for mv in r.mvars do
        let id := mv.mvarId!
        if let some pos := spliceMap[id]? then
          varKinds := varKinds.push (.splice pos)
        else if let some userName? := holeMap[id]? then
          varKinds := varKinds.push (.hole userName?)
        else if validTCs.contains id then
          varKinds := varKinds.push .tc
        else if detMVars.contains id then
          varKinds := varKinds.push .infer
        else
          badMVars := badMVars.push id
      let mut lState := collectLevelMVars {} e
      for mv in r.mvars do
        lState := collectLevelMVars lState (← instantiateMVars (← mv.mvarId!.getDecl).type)
      let mctxNow ← getMCtx
      let badLMVars := lState.result.filter fun lmv =>
        mctxNow.getLevelDepth lmv == curDepth && !detLMVars.contains lmv
      if !badMVars.isEmpty || !badLMVars.isEmpty then
        let autoHoleTypes ← autoHoleTypesRef.get
        try
          reportTermBuildErrors e stx badMVars badLMVars pendingTCMap autoHoleTypes
        finally
          restoreMsgs
      restoreMsgs
      let tmpl : ExprTemplate := {
        levelParams := r.paramNames.toList
        lam         := r.expr
        varKinds
      }
      return (tmpl, orderedSplices.toList)
  let tmplConst ← mkAuxTmplConst tmpl
  let splicesArrExpr ← mkArrayLit (mkConst ``Expr) splicesArgList
  let callExpr ←
    if rel.items.isEmpty && localItemExprs.isEmpty then
      let resolvedRelExpr := quoteResolvedExprMatchRel rel
      mkAppM ``ExprTemplate.instantiateResolved #[tmplConst, resolvedRelExpr, splicesArrExpr]
    else
      let relExpr ← quoteExprMatchRel rel
      let boolExprProd := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Bool) (mkConst ``Expr)
      let localItemList ← localItemExprs.toList.mapM fun (pos, e) =>
        mkAppM ``Prod.mk #[toExpr pos, e]
      let localItemsArrExpr ← mkArrayLit boolExprProd localItemList
      let siteIdExpr := toExpr (tmplConst.constName?.getD .anonymous)
      mkAppM ``ExprTemplate.instantiateSite
        #[siteIdExpr, tmplConst, relExpr, splicesArrExpr, localItemsArrExpr]
  try
    Term.ensureHasType expectedType? callExpr
  catch
    | ex@(.error _ _) =>
      if let some expTy := expectedType? then
        let metaExprTy := mkApp (mkConst ``MetaM) (mkConst ``Expr)
        let expTy ← instantiateMVars expTy
        unless ← isDefEq metaExprTy expTy do
          throwErrorAt stx
            "type mismatch{indentD stx}\nhas type{indentExpr metaExprTy}\n\
             but is expected to have type{indentExpr expTy}"
      throw ex
    | ex => throw ex

end Lean.Elab.Term.ExprQuot
