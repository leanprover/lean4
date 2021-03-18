/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Meta
namespace Simp

builtin_initialize congrHypothesisExceptionId : InternalExceptionId ←
  registerInternalExceptionId `congrHypothesisFailed

def throwCongrHypothesisFailed : MetaM α :=
  throw <| Exception.internal congrHypothesisExceptionId

def Result.getProof (r : Result) : MetaM Expr := do
  match r.proof? with
  | some p => return p
  | none   => mkEqRefl r.expr

private def mkEqTrans (r₁ r₂ : Result) : MetaM Result := do
  match r₁.proof? with
  | none => return r₂
  | some p₁ => match r₂.proof? with
    | none    => return { r₂ with proof? := r₁.proof? }
    | some p₂ => return { r₂ with proof? := (← Meta.mkEqTrans p₁ p₂) }

private def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a) }

private def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }

private def mkImpCongr (r₁ r₂ : Result) : MetaM Result := do
  let e ← mkArrow r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | _,        _      => return { expr := e, proof? := (← Meta.mkImpCongr (← r₁.getProof) (← r₂.getProof)) } -- TODO specialize if bootleneck

private def reduceProj (e : Expr) : MetaM Expr := do
  match (← reduceProj? e) with
  | some e => return e
  | _      => return e

private def reduceProjFn? (e : Expr) : SimpM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      if projInfo.fromClass then
        if (← read).simpLemmas.isDeclToUnfold cinfo.name then
          -- We only unfold class projections when the user explicitly requested them to be unfolded.
          -- Recall that `unfoldDefinition?` has support for unfolding this kind of projection.
          withReducibleAndInstances <| unfoldDefinition? e
        else
          return none
      else
        -- `structure` projection
        match (← unfoldDefinition? e) with
        | none   => pure none
        | some e =>
          match (← reduceProj? e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none

private def reduceFVar (cfg : Config) (e : Expr) : MetaM Expr := do
  if cfg.zeta then
    match (← getFVarLocalDecl e).value? with
    | some v => return v
    | none   => return e
  else
    return e

private def unfold? (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  if (← read).simpLemmas.isDeclToUnfold e.getAppFn.constName! then
    withDefault <| unfoldDefinition? e
  else
    return none

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let cfg := (← read).config
  if cfg.beta then
    let e' := e.headBeta
    if e' != e then
      return (← reduce e')
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProjFn? e) with
    | some e => return (← reduce e)
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return (← reduce e)
    | none   => pure ()
  match (← unfold? e) with
  | some e => reduce e
  | none => return e

private partial def dsimp (e : Expr) : M Expr := do
  transform e (post := fun e => return TransformStep.done (← reduce e))

partial def simp (e : Expr) : M Result := withIncRecDepth do
  let cfg ← getConfig
  if (← isProof e) then
    return { expr := e }
  if cfg.memoize then
    if let some result := (← get).cache.find? e then
      return result
  simpLoop { expr := e }

where
  simpLoop (r : Result) : M Result := do
    let cfg ← getConfig
    if (← get).numSteps > cfg.maxSteps then
      throwError "simp failed, maximum number of steps exceeded"
    else
      let init := r.expr
      modify fun s => { s with numSteps := s.numSteps + 1 }
      match (← pre r.expr) with
      | Step.done r   => cacheResult cfg r
      | Step.visit r' =>
        let r ← mkEqTrans r r'
        let r ← mkEqTrans r (← simpStep r.expr)
        match (← post r.expr) with
        | Step.done r'  => cacheResult cfg (← mkEqTrans r r')
        | Step.visit r' =>
          let r ← mkEqTrans r r'
          if cfg.singlePass || init == r.expr then
            cacheResult cfg r
          else
            simpLoop r

  simpStep (e : Expr) : M Result := do
    match e with
    | Expr.mdata _ e _ => simp e
    | Expr.proj ..     => pure { expr := (← reduceProj e) }
    | Expr.app ..      => simpApp e
    | Expr.lam ..      => simpLambda e
    | Expr.forallE ..  => simpForall e
    | Expr.letE ..     => simpLet e
    | Expr.const ..    => simpConst e
    | Expr.bvar ..     => unreachable!
    | Expr.sort ..     => pure { expr := e }
    | Expr.lit ..      => pure { expr := e }
    | Expr.mvar ..     => pure { expr := (← instantiateMVars e) }
    | Expr.fvar ..     => pure { expr := (← reduceFVar (← getConfig) e) }

  congrDefault (e : Expr) : M Result :=
    withParent e <| e.withApp fun f args => do
      let infos := (← getFunInfoNArgs f args.size).paramInfo
      let mut r ← simp f
      let mut i := 0
      for arg in args do
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        if i < infos.size && !infos[i].hasFwdDeps then
          r ← mkCongr r (← simp arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← simp arg)
        else
          r ← mkCongrFun r (← dsimp arg)
        i := i + 1
      return r

  /- Return true iff processing the given congruence lemma hypothesis produced a non-refl proof. -/
  processCongrHypothesis (h : Expr) : M Bool := do
    forallTelescopeReducing (← inferType h) fun xs hType => withNewLemmas xs do
      let lhs ← instantiateMVars hType.appFn!.appArg!
      let r ← simp lhs
      let rhs := hType.appArg!
      rhs.withApp fun m zs => do
        let val ← mkLambdaFVars zs r.expr
        unless (← isDefEq m val) do
          throwCongrHypothesisFailed
        unless (← isDefEq h (← mkLambdaFVars xs (← r.getProof))) do
          throwCongrHypothesisFailed
        return r.proof?.isSome

  /- Try to rewrite `e` children using the given congruence lemma -/
  tryCongrLemma? (c : CongrLemma) (e : Expr) : M (Option Result) := withNewMCtxDepth do
    trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
    let info ← getConstInfo c.theoremName
    let lemma := mkConst c.theoremName (← info.levelParams.mapM fun _ => mkFreshLevelMVar)
    let (xs, bis, type) ← forallMetaTelescopeReducing (← inferType lemma)
    if c.hypothesesPos.any (· ≥ xs.size) then
      return none
    let lhs := type.appFn!.appArg!
    let rhs := type.appArg!
    if (← isDefEq lhs e) then
      let mut modified := false
      for i in c.hypothesesPos do
        let x := xs[i]
        try
          if (← processCongrHypothesis x) then
            modified := true
        catch _ =>
          trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {← inferType x}"
          return none
      unless modified do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
        return none
      unless (← synthesizeArgs c.theoremName xs bis (← read).discharge?) do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
        return none
      let eNew ← instantiateMVars rhs
      let proof ← instantiateMVars (mkAppN lemma xs)
      return some { expr := eNew, proof? := proof }
    else
      return none

  congr (e : Expr) : M Result := do
    let f := e.getAppFn
    if f.isConst then
      let congrLemmas ← getCongrLemmas
      let cs := congrLemmas.get f.constName!
      for c in cs do
        match (← tryCongrLemma? c e) with
        | none   => pure ()
        | some r => return r
      congrDefault e
    else
      congrDefault e

  simpApp (e : Expr) : M Result := do
    let e ← reduce e
    if !e.isApp then
      simp e
    else
      congr e

  simpConst (e : Expr) : M Result :=
    return { expr := (← reduce e) }

  withNewLemmas {α} (xs : Array Expr) (f : M α) : M α := do
    if (← getConfig).contextual then
      let mut s ← getSimpLemmas
      let mut updated := false
      for x in xs do
        if (← isProof x) then
          s ← s.add x
          updated := true
      if updated then
        withSimpLemmas s f
      else
        f
    else
      f

  simpLambda (e : Expr) : M Result :=
    withParent e <| lambdaTelescope e fun xs e => withNewLemmas xs do
      let r ← simp e
      let eNew ← mkLambdaFVars xs r.expr
      match r.proof? with
      | none   => return { expr := eNew }
      | some h =>
        let p ← xs.foldrM (init := h) fun x h => do
          mkFunExt (← mkLambdaFVars #[x] h)
        return { expr := eNew, proof? := p }

  simpArrow (e : Expr) : M Result := do
    trace[Debug.Meta.Tactic.simp] "arrow {e}"
    let p := e.bindingDomain!
    let q := e.bindingBody!
    let rp ← simp p
    trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
    if (← (← getConfig).contextual <&&> isProp p <&&> isProp q) then
      trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
      withLocalDeclD e.bindingName! rp.expr fun h => do
        let s ← getSimpLemmas
        let s ← s.add h
        withSimpLemmas s do
          let rq ← simp q
          match rq.proof? with
          | none    => mkImpCongr rp rq
          | some hq =>
            let hq ← mkLambdaFVars #[h] hq
            return { expr := (← mkArrow rp.expr rq.expr), proof? := (← mkImpCongrCtx (← rp.getProof) hq) }
    else
      mkImpCongr rp (← simp q)

  simpForall (e : Expr) : M Result := withParent e do
    trace[Debug.Meta.Tactic.simp] "forall {e}"
    if e.isArrow then
      simpArrow e
    else if (← isProp e) then
      withLocalDecl e.bindingName! e.bindingInfo! e.bindingDomain! fun x => withNewLemmas #[x] do
        let b := e.bindingBody!.instantiate1 x
        let rb ← simp b
        let eNew ← mkForallFVars #[x] rb.expr
        match rb.proof? with
        | none   => return { expr := eNew }
        | some h => return { expr := eNew, proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
    else
      return { expr := (← dsimp e) }

  simpLet (e : Expr) : M Result := do
    if (← getConfig).zeta then
      match e with
      | Expr.letE _ _ v b _ => return { expr := b.instantiate1 v }
      | _ => unreachable!
    else
      -- TODO: simplify nondependent let-decls
      return { expr := (← dsimp e) }

  cacheResult (cfg : Config) (r : Result) : M Result := do
    if cfg.memoize then
      modify fun s => { s with cache := s.cache.insert e r }
    return r

def main (e : Expr) (ctx : Context) (methods : Methods := {}) : MetaM Result := do
  withReducible do
    simp e methods ctx |>.run' {}

namespace DefaultMethods
mutual
  partial def discharge? (e : Expr) : SimpM (Option Expr) := do
    let r ← simp e methods
    if r.expr.isConstOf ``True then
      try
        return some (← mkOfEqTrue (← r.getProof))
      catch _ =>
        return none
    else
      return none

  partial def pre (e : Expr) : SimpM Step :=
    preDefault e discharge?

  partial def post (e : Expr) : SimpM Step :=
    postDefault e discharge?

  partial def methods : Methods :=
    { pre := pre, post := post, discharge? := discharge? }
end
end DefaultMethods

end Simp

def simp (e : Expr) (ctx : Simp.Context) : MetaM Simp.Result := do profileitM Exception "simp" (← getOptions) do
  Simp.main e ctx (methods := Simp.DefaultMethods.methods)

end Lean.Meta
