/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.CongrTheorems
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Meta
namespace Simp

builtin_initialize congrHypothesisExceptionId : InternalExceptionId ←
  registerInternalExceptionId `congrHypothesisFailed

def throwCongrHypothesisFailed : MetaM α :=
  throw <| Exception.internal congrHypothesisExceptionId

/--
  Helper method for bootstrapping purposes. It disables `arith` if support theorems have not been defined yet.
-/
def Config.updateArith (c : Config) : CoreM Config := do
  if c.arith then
    if (← getEnv).contains ``Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq then
      return c
    else
      return { c with arith := false }
  else
    return c

def Result.getProof (r : Result) : MetaM Expr := do
  match r.proof? with
  | some p => return p
  | none   => mkEqRefl r.expr

def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a) }

def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }

private def mkImpCongr (src : Expr) (r₁ r₂ : Result) : MetaM Result := do
  let e := src.updateForallE! r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | _,        _      => return { expr := e, proof? := (← Meta.mkImpCongr (← r₁.getProof) (← r₂.getProof)) } -- TODO specialize if bootleneck

/-- Return true if `e` is of the form `ofNat n` where `n` is a kernel Nat literal -/
def isOfNatNatLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg!.isNatLit

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
        if (← read).simpTheorems.isDeclToUnfold cinfo.name then
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
  if (← read).simpTheorems.isDeclToUnfold e.getAppFn.constName! then
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

inductive SimpLetCase where
  | dep -- `let x := v; b` is not equivalent to `(fun x => b) v`
  | nondepDepVar -- `let x := v; b` is equivalent to `(fun x => b) v`, but result type depends on `x`
  | nondep -- `let x := v; b` is equivalent to `(fun x => b) v`, and result type does not depend on `x`

def getSimpLetCase (n : Name) (t : Expr) (v : Expr) (b : Expr) : MetaM SimpLetCase := do
  withLocalDeclD n t fun x => do
    let bx := b.instantiate1 x
    /- The following step is potentially very expensive when we have many nested let-decls.
       TODO: handle a block of nested let decls in a single pass if this becomes a performance problem. -/
    if (← isTypeCorrect bx) then
      let bxType ← whnf (← inferType bx)
      if (← dependsOn bxType x.fvarId!) then
        return SimpLetCase.nondepDepVar
      else
        return SimpLetCase.nondep
    else
      return SimpLetCase.dep

/-- Given the application `e`, remove unnecessary casts of the form `Eq.rec a rfl` and `Eq.ndrec a rfl`. -/
partial def removeUnnecessaryCasts (e : Expr) : MetaM Expr := do
  let mut args := e.getAppArgs
  let mut modified := false
  for i in [:args.size] do
    let arg := args[i]
    if isDummyEqRec arg then
      args := args.set! i (elimDummyEqRec arg)
      modified := true
  if modified then
    return mkAppN e.getAppFn args
  else
    return e
where
  isDummyEqRec (e : Expr) : Bool :=
    (e.isAppOfArity ``Eq.rec 6 || e.isAppOfArity ``Eq.ndrec 6) && e.appArg!.isAppOf ``Eq.refl

  elimDummyEqRec (e : Expr) : Expr :=
    if isDummyEqRec e then
      elimDummyEqRec e.appFn!.appFn!.appArg!
    else
      e

partial def simp (e : Expr) : M Result := withIncRecDepth do
  checkMaxHeartbeats "simp"
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
      | Step.done r'  => cacheResult cfg (← mkEqTrans r r')
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
    | Expr.mdata m e _ => let r ← simp e; return { r with expr := mkMData m r.expr }
    | Expr.proj ..     => simpProj e
    | Expr.app ..      => simpApp e
    | Expr.lam ..      => simpLambda e
    | Expr.forallE ..  => simpForall e
    | Expr.letE ..     => simpLet e
    | Expr.const ..    => simpConst e
    | Expr.bvar ..     => unreachable!
    | Expr.sort ..     => return { expr := e }
    | Expr.lit ..      => simpLit e
    | Expr.mvar ..     => return { expr := (← instantiateMVars e) }
    | Expr.fvar ..     => return { expr := (← reduceFVar (← getConfig) e) }

  simpLit (e : Expr) : M Result := do
    match e.natLit? with
    | some n =>
      /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
         to avoid non-termination. See issue #788.  -/
      if (← getSimpTheorems).isDeclToUnfold ``OfNat.ofNat then
        return { expr := e }
      else
        return { expr := (← mkNumeral (mkConst ``Nat) n) }
    | none   => return { expr := e }

  simpProj (e : Expr) : M Result := do
    match (← reduceProj? e) with
    | some e => return { expr := e }
    | none =>
      let s := e.projExpr!
      let motive? ← withLocalDeclD `s (← inferType s) fun s => do
        let p := e.updateProj! s
        if (← dependsOn (← inferType p) s.fvarId!) then
          return none
        else
          let motive ← mkLambdaFVars #[s] (← mkEq e p)
          if !(← isTypeCorrect motive) then
            return none
          else
            return some motive
      if let some motive := motive? then
        let r ← simp s
        let eNew := e.updateProj! r.expr
        match r.proof? with
        | none => return { expr := eNew }
        | some h =>
          let hNew ← mkEqNDRec motive (← mkEqRefl e) h
          return { expr := eNew, proof? := some hNew }
      else
        return { expr := (← dsimp e) }

  congrArgs (r : Result) (args : Array Expr) : M Result := do
    if args.isEmpty then
      return r
    else
      let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
      let mut r := r
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

  visitFn (e : Expr) : M Result := do
    let f := e.getAppFn
    let fNew ← simp f
    if fNew.expr == f then
      return { expr := e }
    else
      let args := e.getAppArgs
      let eNew := mkAppN fNew.expr args
      if fNew.proof?.isNone then return { expr := eNew }
      let mut proof ← fNew.getProof
      for arg in args do
        proof ← Meta.mkCongrFun proof arg
      return { expr := eNew, proof? := proof }

  mkCongrSimp? (f : Expr) : M (Option CongrTheorem) := do
    if f.isConst then if (← isMatcher f.constName!) then
      -- We always use simple congruence theorems for auxiliary match applications
      return none
    let info ← getFunInfo f
    let kinds := getCongrSimpKinds info
    if kinds.all fun k => match k with | CongrArgKind.fixed => true | CongrArgKind.eq => true | _ => false then
      /- If all argument kinds are `fixed` or `eq`, then using
         simple congruence theorems `congr`, `congrArg`, and `congrFun` produces a more compact proof -/
      return none
    match (← get).congrCache.find? f with
    | some thm? => return thm?
    | none =>
      let thm? ← mkCongrSimpCore? f info kinds
      modify fun s => { s with congrCache := s.congrCache.insert f thm? }
      return thm?

  /-- Try to use automatically generated congruence theorems. See `mkCongrSimp?`. -/
  tryAutoCongrTheorem? (e : Expr) : M (Option Result) := do
    let f := e.getAppFn
    -- TODO: cache
    let some cgrThm ← mkCongrSimp? f | return none
    if cgrThm.argKinds.size != e.getAppNumArgs then return none
    let mut simplified := false
    let mut hasProof   := false
    let mut hasCast    := false
    let mut argsNew    := #[]
    let mut argResults := #[]
    let args := e.getAppArgs
    for arg in args, kind in cgrThm.argKinds do
      match kind with
      | CongrArgKind.fixed => argsNew := argsNew.push (← dsimp arg)
      | CongrArgKind.cast  => hasCast := true; argsNew := argsNew.push arg
      | CongrArgKind.subsingletonInst => argsNew := argsNew.push arg
      | CongrArgKind.eq =>
        let argResult ← simp arg
        argResults := argResults.push argResult
        argsNew    := argsNew.push argResult.expr
        if argResult.proof?.isSome then hasProof := true
        if arg != argResult.expr then simplified := true
      | _ => unreachable!
    if !simplified then return some { expr := e }
    if !hasProof then return some { expr := mkAppN f argsNew }
    let mut proof := cgrThm.proof
    let mut type  := cgrThm.type
    let mut j := 0 -- index at argResults
    let mut subst := #[]
    for arg in args, kind in cgrThm.argKinds do
      proof := mkApp proof arg
      subst := subst.push arg
      type := type.bindingBody!
      match kind with
      | CongrArgKind.fixed => pure ()
      | CongrArgKind.cast  => pure ()
      | CongrArgKind.subsingletonInst =>
        let clsNew := type.bindingDomain!.instantiateRev subst
        let instNew ←
          if (← isDefEq (← inferType arg) clsNew) then
            pure arg
          else
            match (← trySynthInstance clsNew) with
            | LOption.some val => pure val
            | _ =>
              trace[Meta.Tactic.simp.congr] "failed to synthesize instance{indentExpr clsNew}"
              return none
        proof := mkApp proof instNew
        subst := subst.push instNew
        type := type.bindingBody!
      | CongrArgKind.eq =>
        let argResult := argResults[j]
        let argProof ← argResult.getProof
        j := j + 1
        proof := mkApp2 proof argResult.expr argProof
        subst := subst.push argResult.expr |>.push argProof
        type := type.bindingBody!.bindingBody!
      | _ => unreachable!
    let some (_, _, rhs) := type.instantiateRev subst |>.eq? | unreachable!
    let rhs ← if hasCast then removeUnnecessaryCasts rhs else pure rhs
    return some { expr := rhs, proof? := proof }

  congrDefault (e : Expr) : M Result := do
    if let some result ← tryAutoCongrTheorem? e then
      mkEqTrans result (← visitFn result.expr)
    else
      withParent e <| e.withApp fun f args => do
        congrArgs (← simp f) args

  /- Return true iff processing the given congruence theorem hypothesis produced a non-refl proof. -/
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

  /- Try to rewrite `e` children using the given congruence theorem -/
  trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : M (Option Result) := withNewMCtxDepth do
    trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
    let thm ← mkConstWithFreshMVarLevels c.theoremName
    let (xs, bis, type) ← forallMetaTelescopeReducing (← inferType thm)
    if c.hypothesesPos.any (· ≥ xs.size) then
      return none
    let lhs := type.appFn!.appArg!
    let rhs := type.appArg!
    let numArgs := lhs.getAppNumArgs
    let mut e := e
    let mut extraArgs := #[]
    if e.getAppNumArgs > numArgs then
      let args := e.getAppArgs
      e := mkAppN e.getAppFn args[:numArgs]
      extraArgs := args[numArgs:].toArray
    if (← isDefEq lhs e) then
      let mut modified := false
      for i in c.hypothesesPos do
        let x := xs[i]
        try
          if (← processCongrHypothesis x) then
            modified := true
        catch ex =>
          trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {← inferType x}"
          if ex.isMaxRecDepth then
            -- Recall that `processCongrHypothesis` invokes `simp` recursively.
            throw ex
          else
            return none
      unless modified do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
        return none
      unless (← synthesizeArgs c.theoremName xs bis (← read).discharge?) do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
        return none
      let eNew ← instantiateMVars rhs
      let proof ← instantiateMVars (mkAppN thm xs)
      congrArgs { expr := eNew, proof? := proof } extraArgs
    else
      return none

  congr (e : Expr) : M Result := do
    let f := e.getAppFn
    if f.isConst then
      let congrThms ← getSimpCongrTheorems
      let cs := congrThms.get f.constName!
      for c in cs do
        match (← trySimpCongrTheorem? c e) with
        | none   => pure ()
        | some r => return r
      congrDefault e
    else
      congrDefault e

  simpApp (e : Expr) : M Result := do
    let e ← reduce e
    if !e.isApp then
      simp e
    else if isOfNatNatLit e then
      -- Recall that we expand "orphan" kernel nat literals `n` into `ofNat n`
      return { expr := e }
    else
      congr e

  simpConst (e : Expr) : M Result :=
    return { expr := (← reduce e) }

  withNewLemmas {α} (xs : Array Expr) (f : M α) : M α := do
    if (← getConfig).contextual then
      let mut s ← getSimpTheorems
      let mut updated := false
      for x in xs do
        if (← isProof x) then
          s ← s.add #[] x
          updated := true
      if updated then
        withSimpTheorems s f
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
    if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
      trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
      withLocalDeclD e.bindingName! rp.expr fun h => do
        let s ← getSimpTheorems
        let s ← s.add #[] h
        withSimpTheorems s do
          let rq ← simp q
          match rq.proof? with
          | none    => mkImpCongr e rp rq
          | some hq =>
            let hq ← mkLambdaFVars #[h] hq
            if rq.expr.containsFVar h.fvarId! then
              return { expr := (← mkForallFVars #[h] rq.expr), proof? := (← mkImpDepCongrCtx (← rp.getProof) hq) }
            else
              return { expr := e.updateForallE! rp.expr rq.expr, proof? := (← mkImpCongrCtx (← rp.getProof) hq) }
    else
      mkImpCongr e rp (← simp q)

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
    let Expr.letE n t v b _ := e | unreachable!
    if (← getConfig).zeta then
      return { expr := b.instantiate1 v }
    else
      match (← getSimpLetCase n t v b) with
      | SimpLetCase.dep => return { expr := (← dsimp e) }
      | SimpLetCase.nondep =>
        let rv ← simp v
        withLocalDeclD n t fun x => do
          let bx := b.instantiate1 x
          let rbx ← simp bx
          let hb? ← match rbx.proof? with
            | none => pure none
            | some h => pure (some (← mkLambdaFVars #[x] h))
          let e' := mkLet n t rv.expr (← abstract rbx.expr #[x])
          match rv.proof?, hb? with
          | none,   none   => return { expr := e' }
          | some h, none   => return { expr := e', proof? := some (← mkLetValCongr (← mkLambdaFVars #[x] rbx.expr) h) }
          | _,      some h => return { expr := e', proof? := some (← mkLetCongr (← rv.getProof) h) }
      | SimpLetCase.nondepDepVar =>
        let v' ← dsimp v
        withLocalDeclD n t fun x => do
          let bx := b.instantiate1 x
          let rbx ← simp bx
          let e' := mkLet n t v' (← abstract rbx.expr #[x])
          match rbx.proof? with
          | none => return { expr := e' }
          | some h =>
            let h ← mkLambdaFVars #[x] h
            return { expr := e', proof? := some (← mkLetBodyCongr v' h) }

  cacheResult (cfg : Config) (r : Result) : M Result := do
    if cfg.memoize then
      modify fun s => { s with cache := s.cache.insert e r }
    return r

def main (e : Expr) (ctx : Context) (methods : Methods := {}) : MetaM Result := do
  let ctx := { ctx with config := (← ctx.config.updateArith) }
  withConfig (fun c => { c with etaStruct := ctx.config.etaStruct }) <| withReducible do
    try
      simp e methods ctx |>.run' {}
    catch ex =>
      if ex.isMaxHeartbeat then throwNestedTacticEx `simp ex else throw ex

partial def isEqnThmHypothesis (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    if e.isForall then
      go e.bindingBody!
    else
      e.isConstOf ``False

abbrev Discharge := Expr → SimpM (Option Expr)

def dischargeUsingAssumption (e : Expr) : SimpM (Option Expr) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isAuxDecl then
      return none
    else if (← isDefEq e localDecl.type) then
      return some localDecl.toExpr
    else
      return none

namespace DefaultMethods
mutual
  partial def discharge? (e : Expr) : SimpM (Option Expr) := do
    if isEqnThmHypothesis e then
      let r ← dischargeUsingAssumption e
      if r.isSome then
        return r
    let ctx ← read
    trace[Meta.Tactic.simp.discharge] ">> discharge?: {e}"
    if ctx.dischargeDepth >= ctx.config.maxDischargeDepth then
      trace[Meta.Tactic.simp.discharge] "maximum discharge depth has been reached"
      return none
    else
      withReader (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
        let r ← simp e { pre := pre, post := post, discharge? := discharge? }
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
end

def methods : Methods :=
  { pre := pre, post := post, discharge? := discharge? }

end DefaultMethods

end Simp

def simp (e : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) : MetaM Simp.Result := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.main e ctx (methods := Simp.DefaultMethods.methods)
  | some d => Simp.main e ctx (methods := { pre := (Simp.preDefault · d), post := (Simp.postDefault · d), discharge? := d })

/--
  Auxiliary method.
  Given the current `target` of `mvarId`, apply `r` which is a new target and proof that it is equaal to the current one.
-/
def applySimpResultToTarget (mvarId : MVarId) (target : Expr) (r : Simp.Result) : MetaM MVarId := do
  match r.proof? with
  | some proof => replaceTargetEq mvarId r.expr proof
  | none =>
    if target != r.expr then
      replaceTargetDefEq mvarId r.expr
    else
      return mvarId

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) : MetaM (Option MVarId) := do
  let target ← instantiateMVars (← getMVarType mvarId)
  let r ← simp target ctx discharge?
  if mayCloseGoal && r.expr.isConstOf ``True then
    match r.proof? with
    | some proof => assignExprMVar mvarId  (← mkOfEqTrue proof)
    | none => assignExprMVar mvarId (mkConst ``True.intro)
    return none
  else
    applySimpResultToTarget mvarId target r

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) : MetaM (Option MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    simpTargetCore mvarId ctx discharge? mayCloseGoal

/--
  Apply the result `r` for `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToProp (mvarId : MVarId) (proof : Expr) (prop : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isConstOf ``False then
    match r.proof? with
    | some eqProof => assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) (← mkEqMP eqProof proof))
    | none => assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) proof)
    return none
  else
    match r.proof? with
    | some eqProof => return some ((← mkEqMP eqProof proof), r.expr)
    | none =>
      if r.expr != prop then
        return some ((← mkExpectedTypeHint proof r.expr), r.expr)
      else
        return some (proof, r.expr)

def applySimpResultToFVarId (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) : MetaM (Option (Expr × Expr)) := do
  let localDecl ← getLocalDecl fvarId
  applySimpResultToProp mvarId (mkFVar fvarId) localDecl.type r

/--
  Simplify `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpStep (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  let r ← simp prop ctx discharge?
  applySimpResultToProp mvarId proof prop r (mayCloseGoal := mayCloseGoal)

def applySimpResultToLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (r : Option (Expr × Expr)) : MetaM (Option (FVarId × MVarId)) := do
  match r with
  | none => return none
  | some (value, type') =>
    let localDecl ← getLocalDecl fvarId
    if localDecl.type != type' then
      let mvarId ← assert mvarId localDecl.userName type' value
      let mvarId ← tryClear mvarId localDecl.fvarId
      let (fvarId, mvarId) ← intro1P mvarId
      return some (fvarId, mvarId)
    else
      return some (fvarId, mvarId)

/--
  Simplify `simp` result to the given local declaration. Return `none` if the goal was closed.
  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToLocalDecl (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) : MetaM (Option (FVarId × MVarId)) := do
  applySimpResultToLocalDeclCore mvarId fvarId (← applySimpResultToFVarId mvarId fvarId r)

def simpLocalDecl (mvarId : MVarId) (fvarId : FVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) : MetaM (Option (FVarId × MVarId)) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    let localDecl ← getLocalDecl fvarId
    let type ← instantiateMVars localDecl.type
    applySimpResultToLocalDeclCore mvarId fvarId (← simpStep mvarId (mkFVar fvarId) type ctx discharge? mayCloseGoal)

abbrev FVarIdToLemmaId := FVarIdMap Name

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) (fvarIdToLemmaId : FVarIdToLemmaId := {}) : MetaM (Option (Array FVarId × MVarId)) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    let mut mvarId := mvarId
    let mut toAssert : Array Hypothesis := #[]
    for fvarId in fvarIdsToSimp do
      let localDecl ← getLocalDecl fvarId
      let type ← instantiateMVars localDecl.type
      let ctx ← match fvarIdToLemmaId.find? localDecl.fvarId with
        | none => pure ctx
        | some thmId => pure { ctx with simpTheorems := ctx.simpTheorems.eraseCore thmId }
      match (← simpStep mvarId (mkFVar fvarId) type ctx discharge?) with
      | none => return none
      | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
    if simplifyTarget then
      match (← simpTarget mvarId ctx discharge?) with
      | none => return none
      | some mvarIdNew => mvarId := mvarIdNew
    let (fvarIdsNew, mvarIdNew) ← assertHypotheses mvarId toAssert
    let mvarIdNew ← tryClearMany mvarIdNew fvarIdsToSimp
    return (fvarIdsNew, mvarIdNew)

def simpTargetStar (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) : MetaM TacticResultCNM := withMVarContext mvarId do
  trace[Meta.debug] "simpTargetStar:\n{mvarId}"
  let mut ctx := ctx
  for h in (← getPropHyps) do
    let localDecl ← getLocalDecl h
    let proof  := localDecl.toExpr
    trace[Meta.debug] "adding {localDecl.toExpr}"
    let simpTheorems ← ctx.simpTheorems.add #[] proof
    ctx := { ctx with simpTheorems }
  match (← simpTarget mvarId ctx discharge?) with
  | none => return TacticResultCNM.closed
  | some mvarId' =>
    trace[Meta.debug] "simpTargetStar result:\n{mvarId'}"
    if (← getMVarType mvarId) == (← getMVarType mvarId') then
      return TacticResultCNM.noChange
    else
      return TacticResultCNM.modified mvarId'

end Lean.Meta
