/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.UnifyEq
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Match.Value

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
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (e? : Option Expr) : SimpM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← reduceProj? e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none
      if projInfo.fromClass then
        -- `class` projection
        if (← read).isDeclToUnfold cinfo.name then
          /-
          If user requested `class` projection to be unfolded, we set transparency mode to `.instances`,
          and invoke `unfoldDefinition?`.
          Recall that `unfoldDefinition?` has support for unfolding this kind of projection when transparency mode is `.instances`.
          -/
          let e? ← withReducibleAndInstances <| unfoldDefinition? e
          if e?.isSome then
            recordSimpTheorem (.decl cinfo.name)
          return e?
        else
          /-
          Recall that class projections are **not** marked with `[reducible]` because we want them to be
          in "reducible canonical form". However, if we have a class projection of the form `Class.projFn (Class.mk ...)`,
          we want to reduce it. See issue #1869 for an example where this is important.
          -/
          unless e.getAppNumArgs > projInfo.numParams do
            return none
          let major := e.getArg! projInfo.numParams
          unless major.isConstructorApp (← getEnv) do
            return none
          reduceProjCont? (← withDefault <| unfoldDefinition? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)

private def reduceFVar (cfg : Config) (thms : SimpTheoremsArray) (e : Expr) : MetaM Expr := do
  if cfg.zeta || thms.isLetDeclToUnfold e.fvarId! then
    match (← getFVarLocalDecl e).value? with
    | some v => return v
    | none   => return e
  else
    return e

/--
  Return true if `declName` is the name of a definition of the form
  ```
  def declName ... :=
    match ... with
    | ...
  ```
-/
private partial def isMatchDef (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName | return false
  return go (← getEnv) info.value
where
  go (env : Environment) (e : Expr) : Bool :=
    if e.isLambda then
      go env e.bindingBody!
    else
      let f := e.getAppFn
      f.isConst && isMatcherCore env f.constName!

/--
Auxiliary function for implementing `ctx.config.ground`: evaluate ground terms eagerly.
We currently use `whnf` to implement this feature, but we want to stop ground evaluation at symbols marked with the `-` modifier.
For example, `simp (config := { ground := true }) [-f]` should not unfold `f` even if the goal contains a ground term such as `f 2`.
-/
private def canUnfoldAtSimpGround (erased : SimpTheoremsArray) (_ : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  return !erased.isErased (.decl info.name)

/--
Try to unfold `e`.
-/
private def unfold? (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← read
  -- TODO: remove `rec` after we switch to new code generator
  let rec unfoldGround? : SimpM (Option Expr) := do
      unless ctx.config.ground do return none
      -- We are assuming that assigned metavariables are going to be instantiated by the main simp loop.
      if e.hasExprMVar || e.hasFVar then return none
      if ctx.simpTheorems.isErased (.decl fName) then return none
      -- TODO: check whether we need more filters
      if (← isType e) then return none -- we don't unfold types
      if (← isProof e) then return none -- we don't unfold proofs
      if (← isInstance fName) then return none -- we don't unfold instances
      -- TODO: we must have a notion of `simp` value, or more general solution for Lean
      if Meta.isMatchValue e || isOfNatNatLit e then return none
      if e.isConst then
        -- We don't unfold constants that take arguments
        -- TODO: add support for skipping partial applications too.
        if let .forallE .. ← whnfD (← inferType e) then
          return none
      /-
      We are currently using `whnf` with a custom `canUnfold?` predicate to reduce ground terms.
      This can be inefficient, and produce proofs that are too expensive to type check in the Kernel. Some reasons:
      - Functions defined by Well-founded recursion are expensive to reduce here and in the kernel.
      - The kernel does not know we may have controlled reduction using `canUnfold?`.

      It would be great to reduce the ground term using a to-be-implemented `cbv` tactic which produces a
      proof that can be efficiently checked by the kernel.
      -/
      let eNew ← withDefault <|
        withTheReader Meta.Context (fun c => { c with canUnfold? := canUnfoldAtSimpGround ctx.simpTheorems }) <| whnf e
      if eNew == e then return none
      trace[Meta.Tactic.simp.ground] "{e}\n---->\n{eNew}"
      return some eNew
  let rec unfoldDeclToUnfold? : SimpM (Option Expr) := do
    let options ← getOptions
    let cfg ← getConfig
    -- Support for issue #2042
    if cfg.unfoldPartialApp -- If we are unfolding partial applications, ignore issue #2042
       -- When smart unfolding is enabled, and `f` supports it, we don't need to worry about issue #2042
       || (smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName)) then
      withDefault <| unfoldDefinition? e
    else
      -- `We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      withDefault <| unfoldDefinition? e
  if let some eNew ← unfoldGround? then
    return some eNew
  else if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      withDefault <| unfoldDefinition? e
    else if (← isMatchDef fName) then
      let some value ← withDefault <| unfoldDefinition? e | return none
      let .reduced value ← reduceMatcher? value | return none
      return some value
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let cfg := (← read).config
  if e.getAppFn.isMVar then
    let e' ← instantiateMVars e
    if e' != e then
      return (← reduce e')
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
  if cfg.zeta then
    if let some (args, _, _, v, b) := e.letFunAppArgs? then
      return (← reduce <| mkAppN (b.instantiate1 v) args)
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {mkConst e.getAppFn.constName!}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    reduce e'
  | none => return e

private partial def dsimp (e : Expr) : M Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let pre (e : Expr) : M TransformStep := do
    if let Step.visit r ← rewritePre e (fun _ => pure none) (rflOnly := true) then
      if r.expr != e then
        return .visit r.expr
    return .continue
  let post (e : Expr) : M TransformStep := do
    if let Step.visit r ← rewritePost e (fun _ => pure none) (rflOnly := true) then
      if r.expr != e then
        return .visit r.expr
    let mut eNew ← reduce e
    if eNew.isFVar then
      eNew ← reduceFVar cfg (← getSimpTheorems) eNew
    if eNew != e then return .visit eNew else return .done e
  transform (usedLetOnly := cfg.zeta) e (pre := pre) (post := post)

instance : Inhabited (M α) where
  default := fun _ _ _ => default

partial def lambdaTelescopeDSimp (e : Expr) (k : Array Expr → Expr → M α) : M α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : M α := do
    match e with
    | .lam n d b c => withLocalDecl n c (← dsimp d) fun x => go (xs.push x) (b.instantiate1 x)
    | e => k xs e

inductive SimpLetCase where
  | dep -- `let x := v; b` is not equivalent to `(fun x => b) v`
  | nondepDepVar -- `let x := v; b` is equivalent to `(fun x => b) v`, but result type depends on `x`
  | nondep -- `let x := v; b` is equivalent to `(fun x => b) v`, and result type does not depend on `x`

def getSimpLetCase (n : Name) (t : Expr) (b : Expr) : MetaM SimpLetCase := do
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

partial def simp (e : Expr) : M Result := withIncRecDepth do
  checkSystem "simp"
  let cfg ← getConfig
  if (← isProof e) then
    return { expr := e }
  if cfg.memoize then
    if let some result := (← get).cache.find? e then
      /-
         If the result was cached at a dischargeDepth > the current one, it may not be valid.
         See issue #1234
      -/
      if result.dischargeDepth ≤ (← readThe Simp.Context).dischargeDepth then
        return result
  trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
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
    | .mdata m e   => let r ← simp e; return { r with expr := mkMData m r.expr }
    | .proj ..     => simpProj e
    | .app ..      => simpApp e
    | .lam ..      => simpLambda e
    | .forallE ..  => simpForall e
    | .letE ..     => simpLet e
    | .const ..    => simpConst e
    | .bvar ..     => unreachable!
    | .sort ..     => return { expr := e }
    | .lit ..      => simpLit e
    | .mvar ..     => return { expr := (← instantiateMVars e) }
    | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }

  simpLit (e : Expr) : M Result := do
    match e.natLit? with
    | some n =>
      /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
         to avoid non-termination. See issue #788.  -/
      if (← readThe Simp.Context).isDeclToUnfold ``OfNat.ofNat then
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
    Simp.congrArgs simp dsimp r args

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

  /-- Try to use automatically generated congruence theorems. See `mkCongrSimp?`. -/
  tryAutoCongrTheorem? (e : Expr) : M (Option Result) := do
    Simp.tryAutoCongrTheorem? simp dsimp e

  congrDefault (e : Expr) : M Result := do
    if let some result ← tryAutoCongrTheorem? e then
      mkEqTrans result (← visitFn result.expr)
    else
      withParent e <| e.withApp fun f args => do
        congrArgs (← simp f) args

  /-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
  processCongrHypothesis (h : Expr) : M Bool := do
    forallTelescopeReducing (← inferType h) fun xs hType => withNewLemmas xs do
      let lhs ← instantiateMVars hType.appFn!.appArg!
      let r ← simp lhs
      let rhs := hType.appArg!
      rhs.withApp fun m zs => do
        let val ← mkLambdaFVars zs r.expr
        unless (← isDefEq m val) do
          throwCongrHypothesisFailed
        let mut proof ← r.getProof
        if hType.isAppOf ``Iff then
          try proof ← mkIffOfEq proof
          catch _ => throwCongrHypothesisFailed
        unless (← isDefEq h (← mkLambdaFVars xs proof)) do
          throwCongrHypothesisFailed
        /- We used to return `false` if `r.proof? = none` (i.e., an implicit `rfl` proof) because we
           assumed `dsimp` would also be able to simplify the term, but this is not true
           for non-trivial user-provided theorems.
           Example:
           ```
           @[congr] theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a, mem a s → f a = g a) : image f s = image g s :=
           ...

           example {Γ: Set Nat}: (image (Nat.succ ∘ Nat.succ) Γ) = (image (fun a => a.succ.succ) Γ) := by
             simp only [Function.comp_apply]
           ```
           `Function.comp_apply` is a `rfl` theorem, but `dsimp` will not apply it because the composition
           is not fully applied. See comment at issue #1113

           Thus, we have an extra check now if `xs.size > 0`. TODO: refine this test.
        -/
        return r.proof?.isSome || (xs.size > 0 && lhs != r.expr)

  /-- Try to rewrite `e` children using the given congruence theorem -/
  trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : M (Option Result) := withNewMCtxDepth do
    trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
    let thm ← mkConstWithFreshMVarLevels c.theoremName
    let (xs, bis, type) ← forallMetaTelescopeReducing (← inferType thm)
    if c.hypothesesPos.any (· ≥ xs.size) then
      return none
    let isIff := type.isAppOf ``Iff
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
        let x := xs[i]!
        try
          if (← processCongrHypothesis x) then
            modified := true
        catch _ =>
          trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {← inferType x}"
          -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
          -- does not catch runtime exceptions by default.
          return none
      unless modified do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
        return none
      unless (← synthesizeArgs (.decl c.theoremName) xs bis (← read).discharge?) do
        trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
        return none
      let eNew ← instantiateMVars rhs
      let mut proof ← instantiateMVars (mkAppN thm xs)
      if isIff then
        try proof ← mkAppM ``propext #[proof]
        catch _ => return none
      if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
        trace[Meta.Tactic.simp.congr] "{c.theoremName} has unassigned metavariables"
        return none
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
          s ← s.addTheorem (.fvar x.fvarId!) x
          updated := true
      if updated then
        withSimpTheorems s f
      else
        f
    else
      f

  simpLambda (e : Expr) : M Result :=
    withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
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
        let s ← s.addTheorem (.fvar h.fvarId!) h
        withSimpTheorems s do
          let rq ← simp q
          match rq.proof? with
          | none    => mkImpCongr e rp rq
          | some hq =>
            let hq ← mkLambdaFVars #[h] hq
            /-
              We use the default reducibility setting at `mkImpDepCongrCtx` and `mkImpCongrCtx` because they use the theorems
              ```lean
              @implies_dep_congr_ctx : ∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
              @implies_congr_ctx : ∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p₁ → q₁) = (p₂ → q₂)
              ```
              And the proofs may be from `rfl` theorems which are now omitted. Moreover, we cannot establish that the two
              terms are definitionally equal using `withReducible`.
              TODO (better solution): provide the problematic implicit arguments explicitly. It is more efficient and avoids this
              problem.
             -/
            if rq.expr.containsFVar h.fvarId! then
              return { expr := (← mkForallFVars #[h] rq.expr), proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
            else
              return { expr := e.updateForallE! rp.expr rq.expr, proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
    else
      mkImpCongr e rp (← simp q)

  simpForall (e : Expr) : M Result := withParent e do
    trace[Debug.Meta.Tactic.simp] "forall {e}"
    if e.isArrow then
      simpArrow e
    else if (← isProp e) then
      /- The forall is a proposition. -/
      let domain := e.bindingDomain!
      if (← isProp domain) then
        /-
        The domain of the forall is also a proposition, and we can use `forall_prop_domain_congr`
        IF we can simplify the domain.
        -/
        let rd ← simp domain
        if let some h₁ := rd.proof? then
          /- Using
          ```
          theorem forall_prop_domain_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
              (h₁ : p₁ = p₂)
              (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
              : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a)
          ```
          Remark: we should consider whether we want to add congruence lemma support for arbitrary `forall`-expressions.
          Then, the theroem above can be marked as `@[congr]` and the following code deleted.
          -/
          let p₁ := domain
          let p₂ := rd.expr
          let q₁ := mkLambda e.bindingName! e.bindingInfo! p₁ e.bindingBody!
          let result ← withLocalDecl e.bindingName! e.bindingInfo! p₂ fun a => withNewLemmas #[a] do
            let prop := mkSort levelZero
            let h₁_substr_a := mkApp6 (mkConst ``Eq.substr [levelOne]) prop (mkLambda `x .default prop (mkBVar 0)) p₂ p₁ h₁ a
            let q_h₁_substr_a := e.bindingBody!.instantiate1 h₁_substr_a
            let rb ← simp q_h₁_substr_a
            let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
            let q₂ ← mkLambdaFVars #[a] rb.expr
            let result ← mkForallFVars #[a] rb.expr
            let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
            return { expr := result, proof? := proof }
          return result
      let domain ← dsimp domain
      withLocalDecl e.bindingName! e.bindingInfo! domain fun x => withNewLemmas #[x] do
        let b := e.bindingBody!.instantiate1 x
        let rb ← simp b
        let eNew ← mkForallFVars #[x] rb.expr
        match rb.proof? with
        | none   => return { expr := eNew }
        | some h => return { expr := eNew, proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
    else
      return { expr := (← dsimp e) }

  simpLet (e : Expr) : M Result := do
    let .letE n t v b _ := e | unreachable!
    if (← getConfig).zeta then
      return { expr := b.instantiate1 v }
    else
      match (← getSimpLetCase n t b) with
      | SimpLetCase.dep => return { expr := (← dsimp e) }
      | SimpLetCase.nondep =>
        let rv ← simp v
        withLocalDeclD n t fun x => do
          let bx := b.instantiate1 x
          let rbx ← simp bx
          let hb? ← match rbx.proof? with
            | none => pure none
            | some h => pure (some (← mkLambdaFVars #[x] h))
          let e' := mkLet n t rv.expr (← rbx.expr.abstractM #[x])
          match rv.proof?, hb? with
          | none,   none   => return { expr := e' }
          | some h, none   => return { expr := e', proof? := some (← mkLetValCongr (← mkLambdaFVars #[x] rbx.expr) h) }
          | _,      some h => return { expr := e', proof? := some (← mkLetCongr (← rv.getProof) h) }
      | SimpLetCase.nondepDepVar =>
        let v' ← dsimp v
        withLocalDeclD n t fun x => do
          let bx := b.instantiate1 x
          let rbx ← simp bx
          let e' := mkLet n t v' (← rbx.expr.abstractM #[x])
          match rbx.proof? with
          | none => return { expr := e' }
          | some h =>
            let h ← mkLambdaFVars #[x] h
            return { expr := e', proof? := some (← mkLetBodyCongr v' h) }

  cacheResult (cfg : Config) (r : Result) : M Result := do
    if cfg.memoize then
      let dischargeDepth := (← readThe Simp.Context).dischargeDepth
      modify fun s => { s with cache := s.cache.insert e { r with dischargeDepth } }
    return r

@[inline] def withSimpConfig (ctx : Context) (x : MetaM α) : MetaM α :=
  withConfig (fun c => { c with etaStruct := ctx.config.etaStruct }) <| withReducible x

def main (e : Expr) (ctx : Context) (usedSimps : UsedSimps := {}) (methods : Methods := {}) : MetaM (Result × UsedSimps) := do
  let ctx := { ctx with config := (← ctx.config.updateArith) }
  withSimpConfig ctx do withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do
        let (r, s) ← simp e methods ctx |>.run { usedTheorems := usedSimps }
        trace[Meta.Tactic.simp.numSteps] "{s.numSteps}"
        return (r, s.usedTheorems)
    catch ex =>
      if ex.isRuntime then throwNestedTacticEx `simp ex else throw ex

def dsimpMain (e : Expr) (ctx : Context) (usedSimps : UsedSimps := {}) (methods : Methods := {}) : MetaM (Expr × UsedSimps) := do
  withSimpConfig ctx do withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do
        let (r, s) ← dsimp e methods ctx |>.run { usedTheorems := usedSimps }
        pure (r, s.usedTheorems)
    catch ex =>
      if ex.isRuntime then throwNestedTacticEx `dsimp ex else throw ex

/--
  Return true if `e` is of the form `(x : α) → ... → s = t → ... → False`

  Recall that this kind of proposition is generated by Lean when creating equations for
  functions and match-expressions with overlapping cases.
  Example: the following `match`-expression has overlapping cases.
  ```
  def f (x y : Nat) :=
    match x, y with
    | Nat.succ n, Nat.succ m => ...
    | _, _ => 0
  ```
  The second equation is of the form
  ```
  (x y : Nat) → ((n m : Nat) → x = Nat.succ n → y = Nat.succ m → False) → f x y = 0
  ```
  The hypothesis `(n m : Nat) → x = Nat.succ n → y = Nat.succ m → False` is essentially
  saying the first case is not applicable.
-/
partial def isEqnThmHypothesis (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ d b _ => (d.isEq || d.isHEq || b.hasLooseBVar 0) && go b
    | _ => e.consumeMData.isConstOf ``False

abbrev Discharge := Expr → SimpM (Option Expr)

def dischargeUsingAssumption? (e : Expr) : SimpM (Option Expr) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if (← isDefEq e localDecl.type) then
      return some localDecl.toExpr
    else
      return none

/--
  Tries to solve `e` using `unifyEq?`.
  It assumes that `isEqnThmHypothesis e` is `true`.
-/
partial def dischargeEqnThmHypothesis? (e : Expr) : MetaM (Option Expr) := do
  assert! isEqnThmHypothesis e
  let mvar ← mkFreshExprSyntheticOpaqueMVar e
  withReader (fun ctx => { ctx with canUnfold? := canUnfoldAtMatcher }) do
    if let .none ← go? mvar.mvarId! then
      instantiateMVars mvar
    else
      return none
where
  go? (mvarId : MVarId) : MetaM (Option MVarId) :=
    try
      let (fvarId, mvarId) ← mvarId.intro1
      mvarId.withContext do
        let localDecl ← fvarId.getDecl
        if localDecl.type.isEq || localDecl.type.isHEq then
          if let some { mvarId, .. } ← unifyEq? mvarId fvarId {} then
            go? mvarId
          else
            return none
        else
          go? mvarId
    catch _  =>
      return some mvarId

namespace DefaultMethods
mutual
  partial def discharge? (e : Expr) : SimpM (Option Expr) := do
    if isEqnThmHypothesis e then
      if let some r ← dischargeUsingAssumption? e then
        return some r
      if let some r ← dischargeEqnThmHypothesis? e then
        return some r
    let ctx ← read
    trace[Meta.Tactic.simp.discharge] ">> discharge?: {e}"
    if ctx.dischargeDepth >= ctx.config.maxDischargeDepth then
      trace[Meta.Tactic.simp.discharge] "maximum discharge depth has been reached"
      return none
    else
      withReader (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
        let r ← simp e { pre := pre, post := post, discharge? := discharge? }
        if r.expr.consumeMData.isConstOf ``True then
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
open Simp (UsedSimps)

def simp (e : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (usedSimps : UsedSimps := {}) : MetaM (Simp.Result × UsedSimps) := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.main e ctx usedSimps (methods := Simp.DefaultMethods.methods)
  | some d => Simp.main e ctx usedSimps (methods := { pre := (Simp.preDefault · d), post := (Simp.postDefault · d), discharge? := d })

def dsimp (e : Expr) (ctx : Simp.Context)
    (usedSimps : UsedSimps := {}) : MetaM (Expr × UsedSimps) := do profileitM Exception "dsimp" (← getOptions) do
  Simp.dsimpMain e ctx usedSimps (methods := Simp.DefaultMethods.methods)

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option MVarId × UsedSimps) := do
  let target ← instantiateMVars (← mvarId.getType)
  let (r, usedSimps) ← simp target ctx discharge? usedSimps
  if mayCloseGoal && r.expr.consumeMData.isConstOf ``True then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return (none, usedSimps)
  else
    return (← applySimpResultToTarget mvarId target r, usedSimps)

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option MVarId × UsedSimps) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    simpTargetCore mvarId ctx discharge? mayCloseGoal usedSimps

/--
  Apply the result `r` for `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToProp (mvarId : MVarId) (proof : Expr) (prop : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.consumeMData.isConstOf ``False then
    match r.proof? with
    | some eqProof => mvarId.assign (← mkFalseElim (← mvarId.getType) (← mkEqMP eqProof proof))
    | none => mvarId.assign (← mkFalseElim (← mvarId.getType) proof)
    return none
  else
    match r.proof? with
    | some eqProof => return some ((← mkEqMP eqProof proof), r.expr)
    | none =>
      if r.expr != prop then
        return some ((← mkExpectedTypeHint proof r.expr), r.expr)
      else
        return some (proof, r.expr)

def applySimpResultToFVarId (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) (mayCloseGoal : Bool) : MetaM (Option (Expr × Expr)) := do
  let localDecl ← fvarId.getDecl
  applySimpResultToProp mvarId (mkFVar fvarId) localDecl.type r mayCloseGoal

/--
  Simplify `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpStep (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option (Expr × Expr) × UsedSimps) := do
  let (r, usedSimps) ← simp prop ctx discharge? usedSimps
  return (← applySimpResultToProp mvarId proof prop r (mayCloseGoal := mayCloseGoal), usedSimps)

def applySimpResultToLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (r : Option (Expr × Expr)) : MetaM (Option (FVarId × MVarId)) := do
  match r with
  | none => return none
  | some (value, type') =>
    let localDecl ← fvarId.getDecl
    if localDecl.type != type' then
      let mvarId ← mvarId.assert localDecl.userName type' value
      let mvarId ← mvarId.tryClear localDecl.fvarId
      let (fvarId, mvarId) ← mvarId.intro1P
      return some (fvarId, mvarId)
    else
      return some (fvarId, mvarId)

/--
  Simplify `simp` result to the given local declaration. Return `none` if the goal was closed.
  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToLocalDecl (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) (mayCloseGoal : Bool) : MetaM (Option (FVarId × MVarId)) := do
  if r.proof?.isNone then
    -- New result is definitionally equal to input. Thus, we can avoid creating a new variable if there are dependencies
    let mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
    if mayCloseGoal && r.expr.consumeMData.isConstOf ``False then
      mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
      return none
    else
      return some (fvarId, mvarId)
  else
    applySimpResultToLocalDeclCore mvarId fvarId (← applySimpResultToFVarId mvarId fvarId r mayCloseGoal)

def simpLocalDecl (mvarId : MVarId) (fvarId : FVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option (FVarId × MVarId) × UsedSimps) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let type ← instantiateMVars (← fvarId.getType)
    let (r, usedSimps) ← simpStep mvarId (mkFVar fvarId) type ctx discharge? mayCloseGoal usedSimps
    return (← applySimpResultToLocalDeclCore mvarId fvarId r, usedSimps)

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM (Option (Array FVarId × MVarId) × UsedSimps) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut usedSimps := usedSimps
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
      let (r, usedSimps') ← simp type ctx discharge? usedSimps
      usedSimps := usedSimps'
      match r.proof? with
      | some _ => match (← applySimpResultToProp mvarIdNew (mkFVar fvarId) type r) with
        | none => return (none, usedSimps)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.consumeMData.isConstOf ``False then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return (none, usedSimps)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarIdNew ctx discharge? (usedSimps := usedSimps)) with
      | (none, usedSimps') => return (none, usedSimps')
      | (some mvarIdNew', usedSimps') => mvarIdNew := mvarIdNew'; usedSimps := usedSimps'
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "simp made no progress"
    return (some (fvarIdsNew, mvarIdNew), usedSimps)

def simpTargetStar (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (usedSimps : UsedSimps := {}) : MetaM (TacticResultCNM × UsedSimps) := mvarId.withContext do
  let mut ctx := ctx
  for h in (← getPropHyps) do
    let localDecl ← h.getDecl
    let proof  := localDecl.toExpr
    let simpTheorems ← ctx.simpTheorems.addTheorem (.fvar h) proof
    ctx := { ctx with simpTheorems }
  match (← simpTarget mvarId ctx discharge? (usedSimps := usedSimps)) with
  | (none, usedSimps) => return (TacticResultCNM.closed, usedSimps)
  | (some mvarId', usedSimps') =>
    if (← mvarId.getType) == (← mvarId'.getType) then
      return (TacticResultCNM.noChange, usedSimps)
    else
      return (TacticResultCNM.modified mvarId', usedSimps')

def dsimpGoal (mvarId : MVarId) (ctx : Simp.Context) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (usedSimps : UsedSimps := {}) : MetaM (Option MVarId × UsedSimps) := do
   mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut usedSimps : UsedSimps := usedSimps
    for fvarId in fvarIdsToSimp do
      let type ← instantiateMVars (← fvarId.getType)
      let (typeNew, usedSimps') ← dsimp type ctx
      usedSimps := usedSimps'
      if typeNew.consumeMData.isConstOf ``False then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
        return (none, usedSimps)
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId typeNew
    if simplifyTarget then
      let target ← mvarIdNew.getType
      let (targetNew, usedSimps') ← dsimp target ctx usedSimps
      usedSimps := usedSimps'
      if targetNew.consumeMData.isConstOf ``True then
        mvarIdNew.assign (mkConst ``True.intro)
        return (none, usedSimps)
      if let some (_, lhs, rhs) := targetNew.consumeMData.eq? then
        if (← withReducible <| isDefEq lhs rhs) then
          mvarIdNew.assign (← mkEqRefl lhs)
          return (none, usedSimps)
      if target != targetNew then
        mvarIdNew ← mvarIdNew.replaceTargetDefEq targetNew
      pure () -- FIXME: bug in do notation if this is removed?
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "dsimp made no progress"
    return (some mvarIdNew, usedSimps)

end Lean.Meta
