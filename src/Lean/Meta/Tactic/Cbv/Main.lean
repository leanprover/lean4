/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Tactic.Cbv.Opaque
public import Lean.Meta.Tactic.Cbv.ControlFlow
import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Core
import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Array
import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.String
import Lean.Meta.Tactic.Cbv.Util
import Lean.Meta.Tactic.Cbv.TheoremsLookup
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.Sym
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Assert

/-!
# Cbv Evaluator

Proof-producing symbolic evaluator that tries to match call-by-value evaluation
semantics as closely as possible. Built on top of `Lean.Meta.Sym.Simp`, it runs
as a pair of `Simproc`s (pre/post) that drive the simplifier loop.

## Evaluation strategy

The pre-pass (`cbvPre`) handles structural dispatch: projections, let-bindings,
constants, and control flow. Before doing any work, it short-circuits on proof
terms and ground literal values (Nat, Int, BitVec, String, etc.), marking them
as done so the simplifier does not recurse into them.

For applications, the pre-pass first tries control flow simprocs (`ite`, `dite`,
`cond`, `match`, `Decidable.rec`) before the simplifier recurses into the
arguments. This matters because control flow reduction can eliminate branches
entirely, avoiding unnecessary work on arguments that would be discarded.

It converts non-dependent lets into beta-applications (via `toBetaApp`) so the
simplifier's congruence machinery can process arguments in parallel.

The post-pass (`cbvPost`) fires after the simplifier has recursed into subterms.
It evaluates ground arithmetic (`evalGround`) and unfolds/beta-reduces remaining
applications (`handleApp`).

Neither pass enters binders — lambdas, foralls, and free variables are marked
`done := true` immediately.

## Limitations

This is a best-effort tactic. It reduces as far as it can, but cannot always
fully evaluate a term.

Rewriting is fundamentally non-dependent: congruence lemmas like `congrArg`
cannot rewrite an argument when the return type of the function depends on it.
When the simplifier encounters such a dependency, it leaves that subterm alone.

There are also places where we deviate from strict call-by-value semantics:
- Dependent let-expressions are zeta-reduced (substituted directly) rather than
  evaluated as an argument first, because the type dependency prevents us from
  using congruence-based rewriting on the value.
- Dependent projections that cannot be rewritten via `congrArg` are reduced
  directly when possible. As a last resort, if the types on which the projection
  function depends are definitionally equal, we use `HCongr` to build the proof.

## Attributes

- `@[cbv_opaque]`: prevents `cbv` from unfolding a definition. Equation theorems,
  unfold theorems, and kernel reduction are all suppressed. However, `@[cbv_eval]`
  rules can still fire on an `@[cbv_opaque]` constant, allowing users to provide
  custom rewrite rules without exposing the full definition.
- `@[cbv_eval]`: registers a theorem as a custom rewrite rule for `cbv`. The
  theorem must be an unconditional equality whose LHS is an application of a
  constant. Use `@[cbv_eval ←]` to rewrite right-to-left. These rules are tried
  before equation theorems and can override `@[cbv_opaque]`.

## Unfolding order

For a constant application, `handleApp` first checks `@[cbv_opaque]`. If the
constant is opaque, only `@[cbv_eval]` rewrite rules are attempted; the result
is marked done regardless of whether a rule fires. Otherwise it tries in order:
1. `@[cbv_eval]` rewrite rules
2. Equation theorems (e.g. `foo.eq_1`, `foo.eq_2`)
3. Unfold equations
4. Kernel matcher reduction (`reduceRecMatcher`), which also handles quotients
   and recursors

## Entry points

- `cbvEntry`: reduces a single expression (used by `conv => cbv`)
- `cbvGoal`: reduces goal target and/or hypothesis types (used by the `cbv` tactic)
- `cbvDecideGoal`: reduces `decide P = true` and closes or errors (used by `decide_cbv`)
-/

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

/-- Like `Sym.unfoldReducibleStep` but skips `@[cbv_opaque]` declarations. -/
private def unfoldReducibleStep (e : Expr) : MetaM TransformStep := do
  let .const declName _ := e.getAppFn | return .continue
  unless (← isReducible declName) do return .continue
  if (← getEnv).isProjectionFn declName then return .continue
  if (← isCbvOpaque declName) then return .continue
  let some v ← unfoldDefinition? e | return .continue
  return .visit v

/-- Like `Sym.unfoldReducible` but skips `@[cbv_opaque]` declarations. -/
private def unfoldReducible (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := unfoldReducibleStep)

/-- Like `Sym.preprocessExpr` but skips `@[cbv_opaque]` declarations during unfolding. -/
private def preprocessExpr (e : Expr) : Sym.SymM Expr := do
  Sym.shareCommon (← unfoldReducible (← instantiateMVars e))

/-- Like `Sym.preprocessMVar` but skips `@[cbv_opaque]` declarations during unfolding. -/
private def preprocessMVar (mvarId : MVarId) : Sym.SymM MVarId := do
  let mvarDecl ← mvarId.getDecl
  let lctx ← preprocessLCtx mvarDecl.lctx
  let type ← preprocessExpr mvarDecl.type
  let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances type .syntheticOpaque mvarDecl.userName
  mvarId.assign mvarNew
  return mvarNew.mvarId!
where
  preprocessLCtx (lctx : LocalContext) : Sym.SymM LocalContext := do
    let auxDeclToFullName := lctx.auxDeclToFullName
    let mut fvarIdToDecl := {}
    let mut decls := {}
    let mut index := 0
    for decl in lctx do
      let decl ← match decl with
        | .cdecl _ fvarId userName type bi kind =>
          let type ← preprocessExpr type
          pure <| LocalDecl.cdecl index fvarId userName type bi kind
        | .ldecl _ fvarId userName type value nondep kind =>
          let type ← preprocessExpr type
          let value ← preprocessExpr value
          pure <| LocalDecl.ldecl index fvarId userName type value nondep kind
      index := index + 1
      decls := decls.push (some decl)
      fvarIdToDecl := fvarIdToDecl.insert decl.fvarId decl
    return { fvarIdToDecl, decls, auxDeclToFullName }

public register_builtin_option cbv.warning : Bool := {
  defValue := false
  descr    := "When enabled, displays a warning that the `cbv` tactic is being used."
}

public register_builtin_option cbv.maxSteps : Nat := {
  defValue := 100_000
  descr    := "Controls the maximum number of steps for the `cbv` tactic."
}

def tryEquations : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let thms ← getEqnTheorems appFn
  let result ← Simproc.tryCatch (thms.rewrite (d := dischargeNone)) e
  if let .step e' .. := result then
    trace[Meta.Tactic.cbv.rewrite] "equation `{appFn}`:{indentExpr e}\n==>{indentExpr e'}"
  return result

def tryUnfold : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some thm ← getUnfoldTheorem appFn | return .rfl
  let result ← Simproc.tryCatch (fun e => Theorem.rewrite thm e) e
  if let .step e' .. := result then
    trace[Meta.Tactic.cbv.unfold] "unfold `{appFn}`:{indentExpr e}\n==>{indentExpr e'}"
  return result

def betaReduce : Simproc := fun e => do
  -- TODO: Improve term sharing
  let new := e.headBeta
  let new ← Sym.share new
  trace[Debug.Meta.Tactic.cbv.reduce] "beta:{indentExpr e}\n==>{indentExpr new}"
  return .step new (← Sym.mkEqRefl new)

def tryCbvTheorems : Simproc := fun e => do
  let some fnName := e.getAppFn.constName? | return .rfl
  let some evalLemmas ← getCbvEvalLemmas fnName | return .rfl
  let result ← Simproc.tryCatch (Theorems.rewrite evalLemmas (d := dischargeNone)) e
  if let .step e' .. := result then
    trace[Meta.Tactic.cbv.rewrite] "@[cbv_eval] `{fnName}`:{indentExpr e}\n==>{indentExpr e'}"
  return result

/-- Try equation theorems, then unfold equations. -/
def handleConstApp : Simproc := fun e => do
  tryEquations <|> tryUnfold <| e

/--
Post-pass handler for applications. For a constant-headed application, if the
constant is `@[cbv_opaque]`, only `@[cbv_eval]` rules are tried (and the result
is marked done). Otherwise tries `@[cbv_eval]` rules, equation/unfold theorems,
and `reduceRecMatcher`. For a lambda-headed application, beta-reduces.
-/
def handleApp : Simproc := fun e => do
  unless e.isApp do return .rfl
  let fn := e.getAppFn
  match fn with
  | .const constName _ =>
    if (← isCbvOpaque constName) then
      return markAsDoneIfFailed <| ← tryCbvTheorems e
    let info ← getConstInfo constName
    tryCbvTheorems <|> (guardSimproc (fun _ => info.hasValue) handleConstApp) <|> reduceRecMatcher <| e
  | .lam .. => betaReduce e
  | _ => return .rfl

def handleOpaqueConst : Simproc := fun e => do
  let .const constName _ := e | return .rfl
  if (← isCbvOpaque constName) then
    return markAsDoneIfFailed <| ← tryCbvTheorems e
  return .rfl

def foldLit : Simproc := fun e => do
  let some n := e.rawNatLit? | return .rfl
  -- TODO: check performance of sharing
  let new ← Sym.share <| mkNatLit n
  trace[Debug.Meta.Tactic.cbv.reduce] "foldLit: {e} ==> {new}"
  return .step new (← Sym.mkEqRefl e)

def zetaReduce : Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  -- TODO: Improve sharing
  let new ← Sym.share new
  trace[Debug.Meta.Tactic.cbv.reduce] "zeta:{indentExpr e}\n==>{indentExpr new}"
  return .step new (← Sym.mkEqRefl new)

/--
Recursively simplifies the struct inside a projection, then reduces the projection.
For non-dependent projection types, uses `congrArg` to lift the proof.
For dependent projection types, tries direct reduction first; if that fails and
the original and rewritten struct are definitionally equal, falls back to `HCongr`.
-/
def handleProj : Simproc := fun e => do
  let Expr.proj typeName idx struct := e | return .rfl
  withTraceNode `Debug.Meta.Tactic.cbv.reduce (fun
      | .ok (Result.step e' ..) => return m!"proj `{typeName}`.{idx}:{indentExpr e}\n==>{indentExpr e'}"
      | .ok (Result.rfl true _) => return m!"proj `{typeName}`.{idx}: stuck{indentExpr e}"
      | .ok _                   => return m!"proj `{typeName}`.{idx}: no change"
      | .error err              => return m!"proj `{typeName}`.{idx}: {err.toMessageData}") do
  -- We recursively simplify the projection
  let res ← simp struct
  match res with
  | .rfl _ _ =>
    let some reduced ← withCbvOpaqueGuard <| reduceProj? <| .proj typeName idx struct | do
      return .rfl (done := true)

    -- TODO: Figure if we can share this term incrementally
    let reduced ← Sym.share reduced
    return .step reduced (← Sym.mkEqRefl reduced)
  | .step e' proof _ _ =>
    let type ← Sym.inferType e'
    let congrArgFun := Lean.mkLambda `x .default type <| .proj typeName idx <| .bvar 0
    let congrArgFunType ← inferType congrArgFun
    -- If the type of a projection function is non-dependent, we can safely prove `e.i = e'.i` from `e = e'`
    if (congrArgFunType.isArrow) then
      let newProof ← mkCongrArg congrArgFun proof
      return .step (← Lean.Expr.updateProjS! e e') newProof
    else
      -- If the type of the projection function is dependent, we first try to reduce the projection
      let reduced ← withCbvOpaqueGuard <| reduceProj? e
      match reduced with
      | .some reduced =>
        let reduced ← Sym.share reduced
        return .step reduced (← Sym.mkEqRefl reduced)
      | .none =>
       -- If we failed to reduce it, we turn to a last resort; we try use heterogeneous congruence lemma that we then try to turn into an equality.
        unless (← isDefEq struct e') do
          -- If we rewrote the projection body using something that holds up to propositional equality, then there is nothing we can do.
          -- TODO: Check if there is a need to report this to a user, or shall we fail silently.
          return .rfl (done := true)
        let hcongr ← mkHCongr congrArgFun
        let newProof := mkApp3 (hcongr.proof) struct e' proof
        -- We have already checked if `struct` and `e'` are defEq, so we can skip the check.
        let newProof ← mkEqOfHEq newProof (check := false)
        return .step (← Lean.Expr.updateProjS! e e') newProof

open Sym.Internal in
/--
For an application whose head is neither a constant nor a lambda (e.g. a projection
like `p.1 x`), simplify the function head and lift the proof via `congrArg`.
-/
def simplifyAppFn : Simproc := fun e => do
    unless e.isApp do return .rfl
    let fn := e.getAppFn
    if fn.isLambda || fn.isConst then
      return .rfl
    else
    let res ← simp fn
    match res with
    | .rfl _ _ => return res
    | .step e' proof _ _ =>
      let newType ← Sym.inferType e'
      let congrArgFun := Lean.mkLambda `x .default newType (mkAppN (.bvar 0) e.getAppArgs)
      let newValue ← mkAppNS e' e.getAppArgs
      let newProof ← mkCongrArg congrArgFun proof
      trace[Debug.Meta.Tactic.cbv.reduce] "simplifyAppFn:{indentExpr e}\n==>{indentExpr newValue}"
      return .step newValue newProof

def handleConst : Simproc := fun e => do
  let .const n lvls := e | return .rfl
  let info ← getConstInfo n
  unless info.isDefinition do return .rfl
  let eType ← Sym.inferType e
  let eType ← whnfD eType
  if eType matches .forallE .. then return .rfl
  unless info.hasValue && info.levelParams.length == lvls.length do return .rfl
  let fBody ← instantiateValueLevelParams info lvls
  let eNew ← Sym.share fBody
  trace[Meta.Tactic.cbv.unfold] "const `{n}`:{indentExpr e}\n==>{indentExpr eNew}"
  return .step eNew (← Sym.mkEqRefl eNew)

/--
Pre-pass structural dispatch. Routes each expression form to the appropriate handler:
literals, projections, constants, applications (control flow first), and let-bindings
(non-dependent → `toBetaApp`, dependent → zeta-reduce). Binders and variables are
marked done immediately.
-/
def cbvPreStep : Simproc := fun e => do
  match e with
  | .lit .. => foldLit e
  | .proj .. => handleProj e
  | .const .. => handleOpaqueConst >> (tryCbvTheorems <|> handleConst) <| e
  | .app .. => tryMatcher <|> simplifyAppFn <| e
  | .letE .. =>
    if e.letNondep! then
      let betaAppResult ← toBetaApp e
      return .step (betaAppResult.e) (betaAppResult.h)
    else
      zetaReduce e
  | .forallE .. | .lam .. | .fvar .. | .mvar .. | .bvar .. | .sort .. => return .rfl (done := true)
  | _ => return .rfl

/-- Pre-pass: skip builtin values and proofs, run pre simprocs, then dispatch structurally. -/
def cbvPre (simprocs : CbvSimprocs) : Simproc :=
  isBuiltinValue <|> isProofTerm <|> cbvSimprocDispatch simprocs.pre simprocs.erased <|> cbvPreStep

/-- Post-pass: evaluate ground arithmetic, then try eval simprocs, then try unfolding/beta-reducing applications and finally run post simprocs -/
def cbvPost (simprocs : CbvSimprocs) : Simproc :=
  evalGround <|> cbvSimprocDispatch simprocs.eval simprocs.erased <|> handleApp <|> cbvSimprocDispatch simprocs.post simprocs.erased

def mkCbvMethods (simprocs : CbvSimprocs) : Methods :=
  { pre := cbvPre simprocs, post := cbvPost simprocs }

def cbvCore (e : Expr) (config : Sym.Simp.Config := {}) : Sym.SymM Result := do
  let simprocs ← getCbvSimprocs
  let methods := mkCbvMethods simprocs
  SimpM.run' (methods := methods) (config := config)
    <| simp e

/-- Reduce a single expression. Unfolds reducibles, shares subterms, then runs the
simplifier with `cbvPre`/`cbvPost`. Used by `conv => cbv`. -/
public def cbvEntry (e : Expr) : MetaM Result := do
  withTraceNode `Meta.Tactic.cbv (fun
      | .ok (Result.step e' ..) => return m!"cbv:{indentExpr e}\n==>{indentExpr e'}"
      | .ok (Result.rfl ..)     => return m!"cbv: no change{indentExpr e}"
      | .error err              => return m!"cbv: {err.toMessageData}") do
  let simprocs ← getCbvSimprocs
  let config : Sym.Simp.Config := { maxSteps := cbv.maxSteps.get (← getOptions) }
  let methods := mkCbvMethods simprocs
  let e ← unfoldReducible e
  Sym.SymM.run do
    let e ← Sym.shareCommon e
    SimpM.run' (simp e) (methods := methods) (config := config)

/-- Reduce goal target and/or hypothesis types using call-by-value evaluation.

Preprocesses the goal via `Sym.preprocessMVar` (instantiates metavariables, unfolds
reducibles, shares common subterms), then runs `cbvCore` on each selected hypothesis
and the target within a single `SymM` context.

For each hypothesis in `fvarIdsToSimp`, reduces its type via `cbvCore`. If the
reduced type is `False`, the goal is closed immediately. Otherwise, the hypothesis
is replaced with the reduced type.

If `simplifyTarget` is true, reduces the goal type via `cbvCore`. If the reduced
type is `True`, the goal is closed. Otherwise, the target is replaced.

After all reductions, attempts `refl` to close equation goals of the form `v = v`. -/
public def cbvGoal (mvarId : MVarId) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) : MetaM (Option MVarId) := do
  let config : Sym.Simp.Config := { maxSteps := cbv.maxSteps.get (← getOptions) }
  Sym.SymM.run do
    let mvarId ← preprocessMVar mvarId
    mvarId.withContext do
      let mut mvarIdNew := mvarId
      let mut toAssert : Array Hypothesis := #[]
      -- Process hypotheses
      for fvarId in fvarIdsToSimp do
        let localDecl ← fvarId.getDecl
        let type := localDecl.type
        let result ← withTraceNode `Meta.Tactic.cbv (fun
            | .ok (Result.step type' ..) => return m!"hypothesis `{localDecl.userName}`:{indentExpr type}\n==>{indentExpr type'}"
            | .ok (Result.rfl ..)        => return m!"hypothesis `{localDecl.userName}`: no change"
            | .error err                 => return m!"hypothesis `{localDecl.userName}`: {err.toMessageData}") do
          cbvCore type config
        match result with
        | .rfl _ _ => pure ()
        | .step type' proof _ _ =>
          if type'.isFalse then
            let u ← getLevel type
            mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkApp4 (mkConst ``Eq.mp [u]) type type' proof (mkFVar fvarId)))
            return none
          else
            let u ← getLevel type
            toAssert := toAssert.push { userName := localDecl.userName, type := type', value := mkApp4 (mkConst ``Eq.mp [u]) type type' proof (mkFVar fvarId) }
      -- Process target
      if simplifyTarget then
        let target ← mvarIdNew.getType
        let result ← withTraceNode `Meta.Tactic.cbv (fun
            | .ok (Result.step target' ..) => return m!"target:{indentExpr target}\n==>{indentExpr target'}"
            | .ok (Result.rfl ..)          => return m!"target: no change"
            | .error err                   => return m!"target: {err.toMessageData}") do
          cbvCore target config
        match result with
        | .rfl _ _ => pure ()
        | .step target' proof _ _ =>
          if target'.isTrue then
            mvarIdNew.assign (← mkOfEqTrue proof)
            return none
          else
            mvarIdNew ← mvarIdNew.replaceTargetEq target' proof
      -- Assert new hypotheses and clear old ones
      let (_, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
      mvarIdNew := mvarIdNew'
      mvarIdNew ← mvarIdNew.tryClearMany fvarIdsToSimp
      -- Try refl to close equation goals
      let s ← Meta.saveState
      try mvarIdNew.refl; return none
      catch _ => s.restore; return some mvarIdNew

/--
Attempt to close a goal of the form `decide P = true` by reducing only the LHS using `cbv`.

- If the LHS reduces to `Bool.true`, the goal is closed successfully.
- If the LHS reduces to `Bool.false`, throws a user-friendly error indicating the proposition is false.
- Otherwise, throws a user-friendly error showing where the reduction got stuck.
-/
public def cbvDecideGoal (m : MVarId) : MetaM Unit := do
  withTraceNode `Meta.Tactic.cbv (fun
      | .ok ()   => return m!"decide_cbv: closed goal"
      | .error err => return m!"decide_cbv: {err.toMessageData}") do
  let config : Sym.Simp.Config := { maxSteps := cbv.maxSteps.get (← getOptions) }
  Sym.SymM.run do
    let m ← preprocessMVar m
    let mType ← m.getType
    let some (_, lhs, _) := mType.eq? |
      throwError "`decide_cbv`: expected goal of the form `decide _ = true`, got: {indentExpr mType}"
    let result ← cbvCore lhs config
    trace[Meta.Tactic.cbv] "decide_cbv:{indentExpr lhs}\n==>{indentExpr (result.getResultExpr lhs)}"
    let checkResult (e : Expr) (onTrue : Sym.SymM Unit) : Sym.SymM Unit := do
      if (← Sym.isBoolTrueExpr e) then
        onTrue
      else if (← Sym.isBoolFalseExpr e) then
        throwError "`decide_cbv` failed: the proposition evaluates to `false`"
      else
        throwError "`decide_cbv` failed: could not reduce the expression to a boolean value; got stuck at: {indentExpr e}"
    match result with
    | .rfl _ _ => checkResult lhs (m.refl)
    | .step e' proof _ _ => checkResult e' (m.assign proof)


end Lean.Meta.Tactic.Cbv
