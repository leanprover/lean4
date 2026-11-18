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
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Compiler.NoncomputableAttr

public section

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
partial def collectExprQuotPatternVars (exprQuotStx : Syntax) : TermElabM (Array Ident) := do
  let mut vars : Array Ident := #[]
  let mut seen : NameSet := {}
  let rec go (stx : Syntax) : StateRefT (Array Ident × NameSet) TermElabM Unit := do
    if stx.isOfKind ``Parser.Term.syntheticHole then
      if stx[1].isIdent then
        let id : Ident := ⟨stx[1]⟩
        let name := id.getId
        unless name.eraseMacroScopes.isAtomic do
          throwErrorAt id "Invalid pattern variable: Variable name must be atomic, but `{name}` has multiple components"
        if (← get).2.contains name then
          throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
        modify fun (vs, s) => (vs.push id, s.insert name)
      return
    if stx.isAntiquot || stx.isTokenAntiquot || stx.isAntiquotSplice ||
        stx.isAntiquotSuffixSplice || stx.isQuot || isExprQuot stx then
      return
    if let .node _ _ args := stx then
      for arg in args do
        go arg
  let (_, (res, _)) ← (go exprQuotStx[4]).run (vars, seen)
  return res

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
        -- bare engine ident -> synthesize `exprQuotEngine` `"/ " ++ ident`
        mkNode ``exprQuotEngine #[mkAtomFrom engWrapped "/", engWrapped[0]]
    let items? := if inner[1].isNone then none else some inner[1][0]
    let flags := inner[2].getArgs
    (some engStx, items?, flags)
  else if inner.isOfKind ``exprQuotModuloItems then
    (none, some inner[0], inner[1].getArgs)
  else
    -- `exprQuotModuloFlags`
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

private partial def rewriteExprQuotsInPat (modRelStx : Syntax) (stx : Syntax) : Syntax :=
  if isExprQuot stx then
    stx.setArg 2 (mergeExprQuotRel modRelStx stx[2])
  else if stx.isOfKind ``Parser.Term.typeAscription then
    stx.setArg 1 (rewriteExprQuotsInPat modRelStx stx[1])
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    stx
  else match stx with
  | .node i k args => .node i k (args.map (rewriteExprQuotsInPat modRelStx))
  | _ => stx

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
    for i in *...sepArgs.size do
      if i % 2 == 0 then
        let itemStx := sepArgs[i]!
        if itemStx[1].isOfKind ``exprQuotItemPin then
          let pinNode := itemStx[1]
          let pinTerm : Term := ⟨if pinNode.getNumArgs == 2 then pinNode[1] else pinNode[2]⟩
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
          s!"unknown expr quotation flag `{flagName}`; expected `inst`, `beta`, `zeta`, `proj`, or `eta`"
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
        s!"unknown expr quotation engine `{engName}`; expected `structural`, `reducible`, `instances`, `defeq`, or `sym`"
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

@[builtin_macro Lean.Parser.Term.matchModulo] def expandMatchModulo : Macro := fun stx => do
  -- "match " >> atomic (optional generalizingParam >> optional motive >> moduloParam) >>
  -- optional generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >> " with" >> ppDedent matchAlts
  -- Flattened children:
  -- [0]="match", [1]=gen1, [2]=mot1, [3]=moduloParam, [4]=gen2, [5]=mot2, [6]=discrs, [7]="with", [8]=matchAlts
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
  let mut res : Term := ⟨mkNode ``Parser.Term.«match» #[stx[0], gen, mot, stx[6], stx[7], alts]⟩
  for (pinId, pinTerm) in liftedPins.reverse do
    res ← `(have $pinId : _root_.Lean.Expr := $pinTerm; $res)
  return res.raw

@[builtin_macro Lean.Parser.Term.doMatchModulo] def expandDoMatchModulo : Macro := fun stx => do
  -- "match " >> atomic (optional dependentParam >> optional generalizingParam >> optional motive >> moduloParam) >>
  -- optional dependentParam >> optional generalizingParam >> optional motive >>
  -- sepBy1 matchDiscr ", " >> " with" >> doMatchAlts
  -- Flattened children:
  -- [0]="match", [1]=dep1, [2]=gen1, [3]=mot1, [4]=moduloParam, [5]=dep2, [6]=gen2, [7]=mot2, [8]=discrs, [9]="with", [10]=doMatchAlts
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
  let mut res : TSyntax `doElem := ⟨mkNode ``Parser.Term.doMatch #[stx[0], dep, gen, mot, stx[8], stx[9], alts]⟩
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
    throwErrorAt stx[1] "unknown expr quotation engine `{name}`; expected `structural`, `reducible`, `instances`, `defeq`, or `sym`"

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
evaluated in the current local context.
-/
def elabExprMatchRel (relStx : Syntax) : TermElabM (ExprMatchRel × Array (Bool × Expr)) := do
  let mut engine : ExprMatchEngine := .structural
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
        let (pinTerm, isId) := if target.getNumArgs == 2 then (target[1], true) else (target[2], false)
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
      throwErrorAt flagStx[1] "unknown expr quotation flag `{flagName}`; expected `inst`, `beta`, `zeta`, `proj`, or `eta`"
  let rel : ExprMatchRel := { engine, items, flags }
  let _ ← rel.resolveStatic
  return (rel, localItems)

/-! ## Compile-time pattern quoting and auxiliary constant emission -/

private def quoteBinderInfo (bi : BinderInfo) : Expr :=
  mkConst <| match bi with
    | .default        => ``BinderInfo.default
    | .implicit       => ``BinderInfo.implicit
    | .strictImplicit => ``BinderInfo.strictImplicit
    | .instImplicit   => ``BinderInfo.instImplicit

private partial def quoteLevel : Level → TermElabM Expr
  | .zero      => return mkConst ``Level.zero
  | .succ u    => return mkApp (mkConst ``Level.succ) (← quoteLevel u)
  | .max u v   => return mkApp2 (mkConst ``Level.max) (← quoteLevel u) (← quoteLevel v)
  | .imax u v  => return mkApp2 (mkConst ``Level.imax) (← quoteLevel u) (← quoteLevel v)
  | .param n   => return mkApp (mkConst ``Level.param) (toExpr n)
  | .mvar _    => throwError "internal error in expr quotation: unexpected universe metavariable"

private partial def quoteExpr : Expr → TermElabM Expr
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
    return mkApp4 (mkConst ``Expr.lam) (toExpr n) (← quoteExpr t) (← quoteExpr b) (quoteBinderInfo bi)
  | .forallE n t b bi =>
    return mkApp4 (mkConst ``Expr.forallE) (toExpr n) (← quoteExpr t) (← quoteExpr b) (quoteBinderInfo bi)
  | .letE n t v b nd =>
    return mkApp5 (mkConst ``Expr.letE) (toExpr n) (← quoteExpr t) (← quoteExpr v) (← quoteExpr b) (toExpr nd)
  | .lit l => return mkApp (mkConst ``Expr.lit) (toExpr l)
  | .mdata _ e => quoteExpr e
  | .proj s i e => return mkApp3 (mkConst ``Expr.proj) (toExpr s) (toExpr i) (← quoteExpr e)
  | .fvar _ | .mvar _ => throwError "internal error in expr quotation: compiled pattern is not closed"

private def quoteExprMatchEngine : ExprMatchEngine → Expr
  | .structural => mkConst ``ExprMatchEngine.structural
  | .reducible  => mkConst ``ExprMatchEngine.reducible
  | .instances  => mkConst ``ExprMatchEngine.instances
  | .defeq      => mkConst ``ExprMatchEngine.defeq
  | .sym        => mkConst ``ExprMatchEngine.sym

private def quoteExprMatchItem (item : ExprMatchItem) : Expr :=
  mkApp3 (mkConst ``ExprMatchItem.mk) (toExpr item.positive) (toExpr item.declName) (toExpr item.isSimpSet)

private def quoteOptionBool : Option Bool → Expr
  | none   => mkApp (mkConst ``Option.none [0]) (mkConst ``Bool)
  | some b => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Bool) (toExpr b)

private def quoteExprMatchFlags (f : ExprMatchFlags) : Expr :=
  mkApp5 (mkConst ``ExprMatchFlags.mk)
    (quoteOptionBool f.inst) (quoteOptionBool f.beta) (quoteOptionBool f.zeta)
    (quoteOptionBool f.proj) (quoteOptionBool f.eta)

def quoteExprMatchRel (rel : ExprMatchRel) : TermElabM Expr := do
  let itemsArr ← mkArrayLit (mkConst ``ExprMatchItem) (rel.items.map quoteExprMatchItem).toList
  return mkApp3 (mkConst ``ExprMatchRel.mk)
    (quoteExprMatchEngine rel.engine) itemsArr (quoteExprMatchFlags rel.flags)

private def mkListLitExpr (elemTy : Expr) (elems : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [0]) elemTy
  let cons := mkApp (mkConst ``List.cons [0]) elemTy
  elems.foldr (init := nil) fun e acc => mkApp2 cons e acc

private def mkAuxPatConst (pat : ExprPattern) : TermElabM Expr := do
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
  let env ← getEnv
  let isMeta := (← read).isMetaSection || (← read).declName?.any (isMarkedMeta env) ||
    (← read).declName?.isNone
  let baseName ← Term.mkAuxName `exprPat
  let patAuxName :=
    if env.header.isModule && !env.isExporting then
      mkPrivateName env baseName
    else
      baseName
  let decl := Declaration.defnDecl {
    name        := patAuxName
    levelParams := []
    type        := mkConst ``ExprPattern
    value       := patVal
    hints       := .opaque
    safety      := .safe
  }
  let logCompileErrors := !(← read).isNoncomputableSection &&
    !(← read).declName?.any (Lean.isNoncomputable env)
  addAndCompile decl (logCompileErrors := logCompileErrors) (markMeta := isMeta)
  return mkConst patAuxName

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

private partial def preprocessExprPatStx (stx : Syntax) : StateT PatPreprocessState TermElabM Syntax := do
  let recordHole (hk : PatHoleKind) : StateT PatPreprocessState TermElabM (Nat × Name) := do
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
  let mkPlaceholder (idx : Nat) : Syntax :=
    mkNode ``Parser.Term.elabToSyntax #[mkAtomFrom stx "elabToSyntax% ", Syntax.mkNatLit idx]
  let mkHoleAppOrApp (ref : Syntax) (idx : Nat) (holeName : Name) (newArgs : Array Syntax) : Syntax :=
    if newArgs.any (fun a => a.isOfKind ``Parser.Term.namedArgument || a.isOfKind ``Parser.Term.ellipsis) then
      mkNode ``Parser.Term.app #[mkPlaceholder idx, mkNullNode newArgs]
    else
      mkNode ``Parser.Term.exprQuotHoleApp #[mkIdentFrom ref holeName, mkPlaceholder idx, mkNullNode newArgs]
  let handleAppHead (fnStx : Syntax) (argsStx : Array Syntax) : StateT PatPreprocessState TermElabM (Option Syntax) := do
    if fnStx.isOfKind ``Parser.Term.syntheticHole && fnStx[1].isIdent then
      let id : Ident := ⟨fnStx[1]⟩
      let name := id.getId
      unless name.eraseMacroScopes.isAtomic do
        throwErrorAt id "Invalid pattern variable: Variable name must be atomic, but `{name}` has multiple components"
      if (← get).binderHoleIdx.contains name then
        throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
      let (idx, holeName) ← recordHole (.binder id argsStx.size)
      modify fun s => { s with
        binders := s.binders.push id
        binderArity := s.binderArity.insert name argsStx.size
        binderHoleIdx := s.binderHoleIdx.insert name idx
      }
      let newArgs ← argsStx.mapM preprocessExprPatStx
      return some <| mkHoleAppOrApp fnStx idx holeName newArgs
    else if fnStx.isAntiquot && !fnStx.isEscapedAntiquot then
      let aqTerm := fnStx.getAntiquotTerm
      if aqTerm.isOfKind ``Parser.Term.hole then
        throwErrorAt fnStx "expected `$e` pin; use `_` for a wildcard"
      let newArgs ← argsStx.mapM preprocessExprPatStx
      if aqTerm.isIdent then
        let name := aqTerm.getId
        if let some idx := (← get).binderHoleIdx.find? name then
          let holeName := (← get).holeNames[idx]!
          modify fun s => { s with selfPins := s.selfPins.push (⟨aqTerm⟩, name) }
          return some <| mkHoleAppOrApp fnStx idx holeName newArgs
      let (idx, holeName) ← recordHole (.pin aqTerm argsStx.size aqTerm.isIdent)
      return some <| mkHoleAppOrApp fnStx idx holeName newArgs
    else
      return none
  if stx.isOfKind ``Parser.Term.app then
    if let some res ← handleAppHead stx[0] stx[1].getArgs then
      return res
  if stx.isOfKind ``Parser.Term.syntheticHole then
    if stx[1].isIdent then
      let id : Ident := ⟨stx[1]⟩
      let name := id.getId
      unless name.eraseMacroScopes.isAtomic do
        throwErrorAt id "Invalid pattern variable: Variable name must be atomic, but `{name}` has multiple components"
      if (← get).binderHoleIdx.contains name then
        throwErrorAt id "repeated pattern variable `?{name}`; use `${name}` to pin"
      let (idx, _) ← recordHole (.binder id 0)
      modify fun s => { s with
        binders := s.binders.push id
        binderArity := s.binderArity.insert name 0
        binderHoleIdx := s.binderHoleIdx.insert name idx
      }
      return mkPlaceholder idx
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
        return mkPlaceholder idx
    let (idx, _) ← recordHole (.pin aqTerm 0 aqTerm.isIdent)
    return mkPlaceholder idx
  if stx.isQuot || isExprQuot stx then
    return stx
  match stx with
  | .node i k args => return .node i k (← args.mapM preprocessExprPatStx)
  | _ => return stx

@[builtin_term_elab Lean.Parser.Term.exprQuotHoleApp]
def elabExprQuotHoleApp : TermElab := fun stx expectedType? => do
  let holeName := stx[0].getId
  let placeholder := stx[1]
  let idx := placeholder[1].isNatLit?.getD 0
  unless placeholder.isOfKind ``Parser.Term.elabToSyntax && idx < (← read).fixedTermElabs.size do
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
      withLCtx {} {} mkFreshTypeMVar
    else
      let u ← withLCtx {} {} mkFreshLevelMVar
      let retTyFunTy ← mkForallFVars fvarBinders (mkSort u)
      if retTyFunTy.hasFVar then
        throwError "pattern hole cannot depend on bound variables not passed as arguments"
      let retTyMVar ← withLCtx {} {} <| mkFreshExprMVar (some retTyFunTy)
      pure (mkAppN retTyMVar fvarBinders)
  for i in (Array.range argExprs.size).reverse do
    let a := argExprs[i]!
    if isDistinctBinder[i]! then
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
Detect which pattern metavariables `m` in `e` are used ONLY in higher-order Miller position
(i.e. applied to distinct bound variables of `e`), returning `true` for first-order and `false`
for higher-order.
-/
private partial def computeFirstOrderMask (e : Expr) (mvars : Array Expr) : Array Bool := Id.run do
  let mvarIds := mvars.map fun m => if m.isMVar then some m.mvarId! else none
  let isHigherOrder : Array Bool := .replicate mvars.size false
  let rec visit (e : Expr) (depth : Nat) : StateM (Array Bool) Unit := do
    let e := e.consumeMData
    if let .mvar mvarId := e.getAppFn.consumeMData then
      let args := e.getAppArgs
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
            modify (·.set! idx true)
      for arg in args do
        visit arg depth
      return
    match e with
    | .app f a          => visit f depth; visit a depth
    | .lam _ d b _      => visit d depth; visit b (depth + 1)
    | .forallE _ d b _  => visit d depth; visit b (depth + 1)
    | .letE _ t v b _   => visit t depth; visit v depth; visit b (depth + 1)
    | .mdata _ b        => visit b depth
    | .proj _ _ b       => visit b depth
    | _                 => return
  let (_, ho) := (visit e 0).run isHigherOrder
  return ho.map (!·)

private partial def shiftElabPlaceholders (baseOffset : Nat) : Syntax → Syntax
  | stx@(.node i k args) =>
    if k == ``Parser.Term.elabToSyntax then
      let idx := stx[1].isNatLit?.getD 0
      Syntax.node i k #[stx[0], Syntax.mkNatLit (baseOffset + idx)]
    else
      .node i k (args.map (shiftElabPlaceholders baseOffset))
  | stx => stx

/-- Compiled expr quotation slot ready for match dispatch. -/
structure CompiledExprSlot where
  ref             : Syntax
  ordVarIdx       : Nat
  rel             : ExprMatchRel
  patConst        : Expr
  pinIdxs         : Array Nat
  pinsLam         : Expr
  localItemsLam   : Expr
  binders         : Array Ident
  selfPins        : Array (Ident × Name) := #[]
  deriving Inhabited

/--
Compile an `` `(expr[rel]| p) `` pattern in the current local context (which includes ordinary
pattern vars + earlier quotation binders from the same alternative).
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
  -- Compile pattern in empty LCtx; hole metavariables are allocated lazily in empty LCtx.
  let (pat, pinIdxs) ← withoutModifyingElabMetaStateWithInfo <|
    withLCtx {} {} <| withoutErrToSorry <|
    withTheReader Term.Context ({ · with ignoreTCFailures := true }) <|
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
      let e ← withReader (fun ctx => { ctx with
          fixedTermElabs := ctx.fixedTermElabs ++ fixedElabs.map (·.toFixedTermElabRef)
        }) do
          let e ← Term.elabTerm elabBodyStx none
          Term.synthesizeSyntheticMVars (postpone := .partial)
          instantiateMVars e
      let mctx ← getMCtx
      let holeMVars ← (prepState.holeNames.zipIdx).mapM fun (holeName, hIdx) => do
        if let some mvarId := mctx.findUserName? holeName then
          return mkMVar mvarId
        else
          match prepState.holes[hIdx]! with
          | .binder id _ =>
            throwError "pattern variable `?{id.getId}` was eliminated during pattern elaboration:{indentD exprQuotStx[4]}"
          | .pin _ _ _ =>
            throwError "pin `$...` was eliminated during pattern elaboration:{indentD exprQuotStx[4]}"
      let r ← abstractMVars e
      let firstOrder := computeFirstOrderMask e r.mvars
      let mut binderMVars : Array Expr := #[]
      for bId in prepState.binders do
        let some hIdx := prepState.binderHoleIdx.find? bId.getId | unreachable!
        binderMVars := binderMVars.push holeMVars[hIdx]!
      let indexOf (mv : Expr) (what : MessageData) : TermElabM Nat := do
        let some j := r.mvars.idxOf? mv
          | throwError "{what} was eliminated during pattern elaboration:{indentD exprQuotStx[4]}"
        return j
      let namedIdx ← prepState.binders.zip binderMVars |>.mapM fun (bId, mv) =>
        indexOf mv m!"pattern variable `?{bId.getId}`"
      let mut pinIndices : Array Nat := #[]
      for (hIdx, _) in pinExprs do
        let mv := holeMVars[hIdx]!
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
  let patConst ← mkAuxPatConst pat
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
    patConst
    pinIdxs
    pinsLam
    localItemsLam
    binders := prepState.binders
    selfPins := prepState.selfPins
  }

/-! ## Extracting expr quotations from match alternatives -/

/-- Specification of one extracted expr quotation slot within a match alternative. -/
structure AltExprSlotSpec where
  placeholderId : Ident
  exprQuotStx   : Syntax
  colIdx        : Nat
  deriving Inhabited

private partial def hasExprQuotInPat : Syntax → Bool
  | stx =>
    if isExprQuot stx then true
    else if stx.isOfKind ``Parser.Term.typeAscription then
      hasExprQuotInPat stx[1]
    else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
        stx.isAntiquot || stx.isTokenAntiquot then false
    else match stx with
      | .node _ _ args => args.any hasExprQuotInPat
      | _ => false

/-- Return `true` iff any pattern in any alternative contains an `` `(expr| ...) `` quotation. -/
def hasExprQuotInAltViews (altViews : Array (MatchAltView k)) : Bool :=
  altViews.any (·.patterns.any hasExprQuotInPat)

private partial def collectExprQuotBinderNames (stx : Syntax) : StateRefT (Array Name) TermElabM Unit := do
  if isExprQuot stx then
    let vs ← collectExprQuotPatternVars stx
    modify (· ++ vs.map (·.getId))
  else if stx.isOfKind ``Parser.Term.typeAscription then
    collectExprQuotBinderNames stx[1]
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    return
  else if let .node _ _ args := stx then
    for arg in args do
      collectExprQuotBinderNames arg

/-- Return the binder names declared by any `exprQuot` inside `pats`, for generalization shadowing checks. -/
def getExprQuotBinderNamesInPats (pats : Array Syntax) : TermElabM (Array Name) := do
  let (_, res) ← (pats.forM collectExprQuotBinderNames).run #[]
  return res

/--
Reject `match h : e` on any discriminant column whose patterns contain an expr quotation.
-/
def checkNoEqProofOnQuotDiscrs (discrH?s : Array (Option Syntax))
    (altViews : Array (MatchAltView k)) : TermElabM Unit := do
  for h : colIdx in *...discrH?s.size do
    if let some hStx := discrH?s[colIdx] then
      if altViews.any fun alt => alt.patterns[colIdx]?.any hasExprQuotInPat then
        throwErrorAt hStx
          "`{hStx}:` equality proof is not supported on a discriminant matched with `expr` quotations (the `Expr` values may only be related, not equal)"

private partial def extractPatExprQuots (altIdx colIdx : Nat) (stx : Syntax) :
    StateRefT (Array AltExprSlotSpec) TermElabM Syntax := do
  if isExprQuot stx then
    let slotIdx := (← get).size
    let phId := mkIdentFrom stx (← mkFreshUserName <| Name.mkSimple s!"__eq_{altIdx}_{slotIdx}")
    modify (·.push { placeholderId := phId, exprQuotStx := stx, colIdx })
    let exprTyId := mkCIdentFrom stx ``Lean.Expr
    `(($phId : $exprTyId))
  else if stx.isOfKind ``Parser.Term.typeAscription then
    return stx.setArg 1 (← extractPatExprQuots altIdx colIdx stx[1])
  else if stx.isOfKind ``Parser.Term.inaccessible || stx.isQuot ||
      stx.isAntiquot || stx.isTokenAntiquot then
    return stx
  else match stx with
  | .node i k args => return .node i k (← args.mapM (extractPatExprQuots altIdx colIdx))
  | _ => return stx

/--
Extract all `` `(expr| ...) `` quotations from each alternative in `altViews`, replacing each
occurrence with `(__eq_i_t : Lean.Expr)` so Lean's ordinary pattern elaborator checks surrounding
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

/--
Check that no `?`-binder in `slots` collides with ordinary pattern variables or earlier `?`-binders
in the same alternative, and elaborate each `AltExprSlotSpec` sequentially in `TermElabM`.
-/
partial def withElaboratedExprSlots {α} (specs : Array AltExprSlotSpec)
    (ordFVarDecls : Array LocalDecl) (eqs : Array Expr)
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
        | throwErrorAt spec.exprQuotStx "internal error: placeholder for expr quotation was eliminated (likely in an inaccessible pattern position)"
      let slot ← elabExprQuotPattern spec.exprQuotStx ordVarIdx ctxFVars
      for bId in slot.binders do
        if usedNames.contains bId.getId then
          throwErrorAt bId "Invalid pattern variable: Variable name `{bId.getId}` was already used"
      let usedNames' := slot.binders.foldl (init := usedNames) fun s id => s.insert id.getId
      withNewBinders i slot.binders 0 slots quotDecls usedNames' ctxFVars slot {}
    else
      k slots quotDecls

  withNewBinders (i : Nat) (binders : Array Ident) (j : Nat) (slots : Array CompiledExprSlot)
      (quotDecls : Array LocalDecl) (usedNames : NameSet) (ctxFVars : Array Expr)
      (slot : CompiledExprSlot) (bvMap : NameMap Expr) : TermElabM α := do
    if h : j < binders.size then
      let bId := binders[j]
      withLocalDeclD bId.getId (mkConst ``Expr) fun bv => do
        Term.addTermInfo' (isBinder := true) bId bv
        let decl ← bv.fvarId!.getDecl
        withNewBinders i binders (j + 1) slots (quotDecls.push decl) usedNames (ctxFVars.push bv) slot
          (bvMap.insert bId.getId bv)
    else
      for (pinId, name) in slot.selfPins do
        if let some bv := bvMap.find? name then
          Term.addTermInfo' (isBinder := false) pinId bv
      loop (i + 1) (slots.push slot) quotDecls usedNames ctxFVars

/-! ## Join-point match dispatch compiler -/

/-- One alternative ready for join-point match compilation. -/
structure ExprMatchAlt where
  altLHS        : Meta.Match.AltLHS
  eqsCount      : Nat
  slots         : Array CompiledExprSlot
  quotFVarDecls : Array LocalDecl
  rhs           : Expr
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

/-- Check if two `Meta.Match.Pattern`s have the exact same ordinary structural skeleton. -/
private partial def sameOrdPatternSkeleton : Meta.Match.Pattern → Meta.Match.Pattern → Bool
  | .var _, .var _ => true
  | .ctor n₁ us₁ ps₁ fs₁, .ctor n₂ us₂ ps₂ fs₂ =>
    n₁ == n₂ && us₁ == us₂ && ps₁ == ps₂ && fs₁.length == fs₂.length &&
      (fs₁.zip fs₂).all fun (a, b) => sameOrdPatternSkeleton a b
  | .arrayLit t₁ ps₁, .arrayLit t₂ ps₂ =>
    t₁ == t₂ && ps₁.length == ps₂.length &&
      (ps₁.zip ps₂).all fun (a, b) => sameOrdPatternSkeleton a b
  | .val v₁, .val v₂ => v₁ == v₂
  | .inaccessible e₁, .inaccessible e₂ => e₁ == e₂
  | _, _ => false

private def isSimpleAllVarAlt (alt : ExprMatchAlt) : Bool :=
  alt.eqsCount == 0 &&
  alt.altLHS.fvarDecls.length == alt.altLHS.patterns.length &&
  alt.altLHS.patterns.all fun
    | .var _ => true
    | _      => false

/--
Given `ordFVars` of `baseAlt` (matching `sameOrdPatternSkeleton`), map `targetAlt`'s `fvarDecls`
positions to the corresponding `ordFVar` in `ordFVars`.
-/
private partial def collectVarMapping (pBase pTgt : Meta.Match.Pattern)
    (baseDecls tgtDecls : List LocalDecl) (ordFVars : Array Expr) :
    StateM (Array (Option Expr)) Unit := do
  match pBase, pTgt with
  | .var fvB, .var fvT =>
    if let some bIdx := baseDecls.findIdx? (·.fvarId == fvB) then
      if let some tIdx := tgtDecls.findIdx? (·.fvarId == fvT) then
        modify (·.set! tIdx (some ordFVars[bIdx]!))
  | .ctor _ _ _ fsB, .ctor _ _ _ fsT =>
    for (a, b) in fsB.zip fsT do
      collectVarMapping a b baseDecls tgtDecls ordFVars
  | .arrayLit _ psB, .arrayLit _ psT =>
    for (a, b) in psB.zip psT do
      collectVarMapping a b baseDecls tgtDecls ordFVars
  | _, _ => return

private def mapOrdFVars (baseAlt tgtAlt : ExprMatchAlt) (ordFVars : Array Expr) : Option (Array Expr) :=
  let init : Array (Option Expr) := .replicate tgtAlt.altLHS.fvarDecls.length none
  let (_, mapped) := (go baseAlt.altLHS.patterns tgtAlt.altLHS.patterns).run init
  mapped.mapM id
where
  go : List Meta.Match.Pattern → List Meta.Match.Pattern → StateM (Array (Option Expr)) Unit
    | a :: as, b :: bs => do
      collectVarMapping a b baseAlt.altLHS.fvarDecls tgtAlt.altLHS.fvarDecls ordFVars
      go as bs
    | _, _ => return

private def canGroupSameSkeleton (a b : ExprMatchAlt) : Bool :=
  a.eqsCount == 0 && b.eqsCount == 0 &&
  a.altLHS.fvarDecls.length == b.altLHS.fvarDecls.length &&
  a.altLHS.patterns.length == b.altLHS.patterns.length &&
  a.altLHS.fvarDecls.all (fun d => !d.type.hasFVar) &&
  b.altLHS.fvarDecls.all (fun d => !d.type.hasFVar) &&
  (a.altLHS.patterns.zip b.altLHS.patterns).all (fun (p₁, p₂) => sameOrdPatternSkeleton p₁ p₂) &&
  (mapOrdFVars a b (a.altLHS.fvarDecls.toArray.map LocalDecl.toExpr)).isSome

mutual

private partial def buildSlotChainGo (jpAlt : Expr) (alt : ExprMatchAlt) (ordFVars eqs : Array Expr)
    (failCall : Expr) (slotIdx : Nat) (quotFVars ctxArgs : Array Expr) : TermElabM Expr := do
  if h : slotIdx < alt.slots.size then
    let slot := alt.slots[slotIdx]
    let scrutinee := ordFVars[slot.ordVarIdx]!
    let relExpr ← quoteExprMatchRel slot.rel
    let pinIdxsExpr ← mkArrayLit (mkConst ``Nat) (slot.pinIdxs.toList.map toExpr)
    let pinsExpr :=
      if slot.pinIdxs.isEmpty then
        Expr.app (mkConst ``Array.empty [0]) (mkConst ``Expr)
      else
        (slot.pinsLam.beta ctxArgs)
    let localItemsExpr := (slot.localItemsLam.beta ctxArgs)
    let onMatchLam ← withLocalDeclD (← mkFreshUserName `__xs)
        (mkApp (mkConst ``Array [0]) (mkConst ``Expr)) fun xsVar => do
      let body ← buildSlotChainBind jpAlt alt ordFVars eqs failCall slotIdx slot xsVar 0 quotFVars ctxArgs
      mkLambdaFVars #[xsVar] body
    let onFailLam ← withLocalDeclD `_ (mkConst ``Unit) fun u =>
      mkLambdaFVars #[u] failCall
    try
      let siteIdExpr := toExpr (slot.patConst.constName?.getD .anonymous)
      mkAppM ``ExprPattern.matchSiteOrElse
        #[siteIdExpr, slot.patConst, relExpr, pinIdxsExpr, pinsExpr, localItemsExpr, scrutinee,
          onMatchLam, onFailLam]
    catch ex =>
      let retTy ← inferType failCall
      let retTyWhnf ← whnf retTy
      if (← ex.toMessageData.toString).contains "MonadLiftT" || !retTyWhnf.isApp then
        throwError "expr quotation matching requires a monad lifting `MetaM`, got result type{indentExpr retTy}\n{ex.toMessageData}"
      else
        throw ex
  else
    let allArgs := ordFVars ++ eqs ++ quotFVars
    if allArgs.isEmpty then
      return mkApp jpAlt (mkConst ``Unit.unit)
    else
      return mkAppN jpAlt allArgs

private partial def buildSlotChainBind (jpAlt : Expr) (alt : ExprMatchAlt) (ordFVars eqs : Array Expr)
    (failCall : Expr) (slotIdx : Nat) (slot : CompiledExprSlot) (xsVar : Expr) (j : Nat)
    (quotFVars ctxArgs : Array Expr) : TermElabM Expr := do
  if h : j < slot.binders.size then
    let bId := slot.binders[j]
    let val := mkApp2 (mkConst ``ExprPattern.arg) xsVar (toExpr j)
    withLetDecl bId.getId (mkConst ``Expr) val (nondep := true) fun bv => do
      let body ← buildSlotChainBind jpAlt alt ordFVars eqs failCall slotIdx slot xsVar (j + 1)
        (quotFVars.push bv) (ctxArgs.push bv)
      mkLetFVars (generalizeNondepLet := false) #[bv] body
  else
    buildSlotChainGo jpAlt alt ordFVars eqs failCall (slotIdx + 1) quotFVars ctxArgs

end

private def buildSlotChain (jpAlt : Expr) (alt : ExprMatchAlt) (ordFVars eqs : Array Expr)
    (failCall : Expr) : TermElabM Expr :=
  buildSlotChainGo jpAlt alt ordFVars eqs failCall 0 #[] (ordFVars ++ eqs)

private partial def withEqsFor (discrHNames : Array (Option Name)) (lhs rhs : Array Expr)
    (eqs : Array Expr) (i : Nat) (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if _h : i < lhs.size then
    if let some hName := discrHNames[i]! then
      withLocalDeclD hName (← mkEqHEq lhs[i]! rhs[i]!) fun eq =>
        withEqsFor discrHNames lhs rhs (eqs.push eq) (i + 1) k
    else
      withEqsFor discrHNames lhs rhs eqs (i + 1) k
  else
    k eqs

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
        let origEq := origEqs[eqIdx]!
        let stepEq := stepEqs[eqIdx]!
        let combined ← combineEqHEq origDiscrs[i]! stepArgs[i]! origEq stepEq
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

private def mkCatchAllAltLHS (curMatchType : Expr) (numDiscrs : Nat) : TermElabM Meta.Match.AltLHS := do
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

private partial def buildExprMatchDispatch (discrHNames : Array (Option Name)) (origDiscrs : Array Expr)
    (isDep : Bool) (alts : Array ExprMatchAlt) (jpAlts : Array Expr)
    (startIdx : Nat) (curDiscrs : Array Expr) (origEqs? : Option (Array Expr))
    (curMatchType : Expr) : TermElabM Expr := do
  let discrInfos : Array Meta.Match.DiscrInfo := discrHNames.map fun hName? => { hName? }
  let firstRef? := (Array.range (alts.size - startIdx)).findSome? fun off =>
    let idx := startIdx + off
    if !alts[idx]!.slots.isEmpty then some idx else none
  match firstRef? with
  | none =>
    let tailIdxs := (Array.range (alts.size - startIdx)).map (startIdx + ·)
    let prevIrrefs := (Array.range startIdx).filter (alts[·]!.slots.isEmpty)
    let allIdxs := tailIdxs ++ prevIrrefs
    let lhss := allIdxs.toList.map (alts[·]!.altLHS)
    let matcherName ← Term.mkAuxName `match
    let matcherResult ← Meta.Match.mkMatcher {
      matcherName
      matchType := curMatchType
      discrInfos
      lhss
    }
    matcherResult.addMatcher
    let minors ← allIdxs.mapM fun altIdx =>
      mkOrdMinor discrHNames origDiscrs origEqs? jpAlts[altIdx]! alts[altIdx]! curDiscrs
    let motive ← forallBoundedTelescope curMatchType curDiscrs.size fun xs body =>
      mkLambdaFVars xs body
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r curDiscrs
    return mkAppN r minors
  | some i =>
    let mut iEnd := i
    while iEnd + 1 < alts.size && !alts[iEnd + 1]!.slots.isEmpty &&
        canGroupSameSkeleton alts[i]! alts[iEnd + 1]! do
      iEnd := iEnd + 1
    let nextIdx := iEnd + 1
    let hasNext := nextIdx < alts.size
    let getNonDepRetType : TermElabM Expr :=
      forallBoundedTelescope curMatchType curDiscrs.size fun _ body => pure body
    let withFailJP (k : (Array Expr → Array Expr → TermElabM Expr) → TermElabM Expr) : TermElabM Expr := do
      if !hasNext then
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
        let failBody ← buildExprMatchDispatch discrHNames origDiscrs isDep alts jpAlts nextIdx curDiscrs origEqs? curMatchType
        let failLam := mkLambda `_ .default (mkConst ``Unit) failBody
        withLetDecl (← mkFreshUserName `__do_jp) jpTy failLam (nondep := true) (kind := .implDetail) fun jp => do
          let res ← k fun _ _ => return mkApp jp (mkConst ``Unit.unit)
          mkLetFVars (generalizeNondepLet := false) #[jp] res
      else
        forallBoundedTelescope curMatchType curDiscrs.size fun newDiscrs retBody =>
          withEqsFor discrHNames origDiscrs newDiscrs #[] 0 fun newOrigEqs => do
            let failBody ← buildExprMatchDispatch discrHNames origDiscrs isDep alts jpAlts nextIdx newDiscrs (some newOrigEqs) curMatchType
            let failLam ← mkLambdaFVars (newDiscrs ++ newOrigEqs) failBody
            let jpTy ← mkForallFVars (newDiscrs ++ newOrigEqs) retBody
            withLetDecl (← mkFreshUserName `__do_jp) jpTy failLam (nondep := true) (kind := .implDetail) fun jp => do
              let res ← k fun args eqArgs => return mkAppN jp (args ++ eqArgs)
              mkLetFVars (generalizeNondepLet := false) #[jp] res

    withFailJP fun mkFailCall => do
      if startIdx == i && i == iEnd && !isDep && discrHNames.all (·.isNone) && isSimpleAllVarAlt alts[i]! then
        let pats := alts[i]!.altLHS.patterns
        let ordMap? := alts[i]!.altLHS.fvarDecls.toArray.mapM fun decl =>
          (pats.findIdx? fun
            | .var fv => fv == decl.fvarId
            | _       => false).map (curDiscrs[·]!)
        if let some ordMap := ordMap? then
          return ← buildSlotChain jpAlts[i]! alts[i]! ordMap #[] (← mkFailCall curDiscrs #[])

      let prefixIdxs := (Array.range (i - startIdx)).map (startIdx + ·)
      let catchAllLHS ← mkCatchAllAltLHS curMatchType curDiscrs.size
      let stepLHSS := (prefixIdxs.toList.map (alts[·]!.altLHS)) ++ [alts[i]!.altLHS, catchAllLHS]
      let matcherName ← Term.mkAuxName `match
      let matcherResult ← Meta.Match.mkMatcher {
        matcherName
        matchType := curMatchType
        discrInfos
        lhss := stepLHSS
      }
      matcherResult.addMatcher
      let prefixMinors ← prefixIdxs.mapM fun altIdx =>
        mkOrdMinor discrHNames origDiscrs origEqs? jpAlts[altIdx]! alts[altIdx]! curDiscrs
      let groupMinor ← withExistingLocalDecls alts[i]!.altLHS.fvarDecls do
        let ordFVars := alts[i]!.altLHS.fvarDecls.toArray.map LocalDecl.toExpr
        let failArgs ← alts[i]!.altLHS.patterns.toArray.mapM (Meta.Match.Pattern.toExpr · (annotate := false))
        withEqsFor discrHNames curDiscrs failArgs #[] 0 fun eqs => do
          let combinedEqs ← combineOrigEqs discrHNames origDiscrs origEqs? failArgs eqs
          let failCall ← mkFailCall failArgs combinedEqs
          let rec buildGroup (j : Nat) (nextExpr : Expr) : TermElabM Expr := do
            let some mappedOrdFVars :=
              (if j == i then some ordFVars else mapOrdFVars alts[i]! alts[j]! ordFVars)
              | throwError "internal error in expr quotation match compilation: failed to map pattern variables"
            let cur ← buildSlotChain jpAlts[j]! alts[j]! mappedOrdFVars combinedEqs nextExpr
            if _hgt : j > i then
              if alts[j - 1]!.slots.size > 1 then
                let curTy ← inferType cur
                let jpTy ← mkArrow (mkConst ``Unit) curTy
                let jpLam := mkLambda `_ .default (mkConst ``Unit) cur
                withLetDecl (← mkFreshUserName `__do_jp) jpTy jpLam (nondep := true) (kind := .implDetail) fun jp => do
                  let upper ← buildGroup (j - 1) (mkApp jp (mkConst ``Unit.unit))
                  mkLetFVars (generalizeNondepLet := false) #[jp] upper
              else
                buildGroup (j - 1) cur
            else
              return cur
          let chain ← buildGroup iEnd failCall
          mkLambdaFVars (ordFVars ++ eqs) chain
      let catchAllMinor ← mkCatchAllMinor discrHNames origDiscrs curDiscrs origEqs? catchAllLHS mkFailCall
      let minors := prefixMinors ++ #[groupMinor, catchAllMinor]
      let motive ← forallBoundedTelescope curMatchType curDiscrs.size fun xs body =>
        mkLambdaFVars xs body
      let r := mkApp matcherResult.matcher motive
      let r := mkAppN r curDiscrs
      return mkAppN r minors

private partial def bindAltJPsAndDispatch (discrHNames : Array (Option Name)) (matchType : Expr)
    (isDep : Bool) (alts : Array ExprMatchAlt) (curDiscrs : Array Expr)
    (idx : Nat) (jpAlts : Array Expr) : TermElabM Expr := do
  if h : idx < alts.size then
    let rhs := alts[idx].rhs
    let rhsTy ← inferType rhs
    withLetDecl (← mkFreshUserName `__do_jp) rhsTy rhs (nondep := true) (kind := .implDetail) fun jp => do
      let body ← bindAltJPsAndDispatch discrHNames matchType isDep alts curDiscrs (idx + 1) (jpAlts.push jp)
      mkLetFVars (generalizeNondepLet := false) (usedLetOnly := true) #[jp] body
  else
    buildExprMatchDispatch discrHNames curDiscrs isDep alts jpAlts 0 curDiscrs none matchType

private partial def bindDiscrsAndDispatch (discrs : Array Expr) (discrHNames : Array (Option Name))
    (matchType : Expr) (isDep : Bool) (alts : Array ExprMatchAlt)
    (idx : Nat) (curDiscrs : Array Expr) : TermElabM Expr := do
  if h : idx < discrs.size then
    let d := discrs[idx]
    if !isDep && !d.isFVar then
      let dTy ← inferType d
      withLetDecl (← mkFreshUserName `__discr) dTy d (nondep := false) (kind := .implDetail) fun dv => do
        let body ← bindDiscrsAndDispatch discrs discrHNames matchType isDep alts (idx + 1) (curDiscrs.push dv)
        mkLetFVars (generalizeNondepLet := false) #[dv] body
    else
      bindDiscrsAndDispatch discrs discrHNames matchType isDep alts (idx + 1) (curDiscrs.push d)
  else
    bindAltJPsAndDispatch discrHNames matchType isDep alts curDiscrs 0 #[]

/--
Compile a `match` that contains one or more `` `(expr| ...) `` patterns, using Lean's
`Meta.Match.mkMatcher` for ordinary patterns, checking exhaustiveness & redundancy accurately,
and compiling fall-through via join points without code duplication.
-/
partial def compileExprMatch (discrs : Array Expr) (discrHNames : Array (Option Name))
    (matchType : Expr) (isDep : Bool) (alts : Array ExprMatchAlt)
    (reportMatcherErrors : List Meta.Match.AltLHS → Meta.Match.MatcherResult → TermElabM Unit)
    (reportUnusedAlt : Meta.Match.AltLHS → TermElabM Unit) : TermElabM Expr := do
  let discrInfos : Array Meta.Match.DiscrInfo := discrHNames.map fun hName? => { hName? }
  -- 1. Exhaustiveness & redundancy check on irrefutable alternatives + refutable shadows.
  let irrefIdxs := (Array.range alts.size).filter fun i => alts[i]!.slots.isEmpty
  let irrefLHSS := irrefIdxs.toList.map (alts[·]!.altLHS)
  let checkName ← Term.mkAuxName `expr_match_check
  let irrefRes ← Meta.Match.mkMatcher {
    matcherName := checkName
    matchType
    discrInfos
    lhss := irrefLHSS
  }
  if !irrefRes.counterExamples.isEmpty then
    reportMatcherErrors irrefLHSS irrefRes
  else
    -- Report unused irrefutable alts if any, plus any refutable alt shadowed by preceding irrefutable alts.
    unless irrefRes.unusedAltIdxs.isEmpty do
      reportMatcherErrors irrefLHSS irrefRes
    for h : i in *...alts.size do
      unless alts[i].slots.isEmpty do
        let prevIrrefs := (Array.range i).filter (alts[·]!.slots.isEmpty) |>.toList.map (alts[·]!.altLHS)
        unless prevIrrefs.isEmpty do
          let shadowCheckName ← Term.mkAuxName `expr_match_shadow
          let shadowRes ← Meta.Match.mkMatcher {
            matcherName := shadowCheckName
            matchType
            discrInfos
            lhss := prevIrrefs ++ [alts[i].altLHS]
          }
          if shadowRes.unusedAltIdxs.contains prevIrrefs.length then
            reportUnusedAlt alts[i].altLHS

  -- 2. If non-dependent, bind any non-fvar discriminant once so it is never re-evaluated.
  bindDiscrsAndDispatch discrs discrHNames matchType isDep alts 0 #[]

@[builtin_term_elab Lean.Parser.Term.exprQuot] def elabExprQuotTerm : TermElab := fun stx _ => do
  throwErrorAt stx "expr quotation `{stx}` in term (building) position is not implemented yet (B3)"

end Lean.Elab.Term.ExprQuot
