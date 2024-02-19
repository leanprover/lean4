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
        if (← getContext).isDeclToUnfold cinfo.name then
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
Try to unfold `e`.
-/
private def unfold? (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
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
  if (← isProjectionFn fName) then
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

private def reduceStep (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    return (← instantiateMVars e)
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProjFn? e) with
    | some e => return e
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return e
    | none   => pure ()
  if cfg.zeta then
    if let some (args, _, _, v, b) := e.letFunAppArgs? then
      return mkAppN (b.instantiate1 v) args
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {mkConst e.getAppFn.constName!}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
  | none => return e

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    reduce e'

instance : Inhabited (SimpM α) where
  default := fun _ _ _ => default

partial def lambdaTelescopeDSimp (e : Expr) (k : Array Expr → Expr → SimpM α) : SimpM α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : SimpM α := do
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

def withNewLemmas {α} (xs : Array Expr) (f : SimpM α) : SimpM α := do
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

def simpLit (e : Expr) : SimpM Result := do
  match e.natLit? with
  | some n =>
    /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
        to avoid non-termination. See issue #788.  -/
    if (← readThe Simp.Context).isDeclToUnfold ``OfNat.ofNat then
      return { expr := e }
    else
      return { expr := (← mkNumeral (mkConst ``Nat) n) }
  | none   => return { expr := e }

def simpProj (e : Expr) : SimpM Result := do
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

def simpConst (e : Expr) : SimpM Result :=
  return { expr := (← reduce e) }

def simpLambda (e : Expr) : SimpM Result :=
  withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
    let r ← simp e
    let eNew ← mkLambdaFVars xs r.expr
    match r.proof? with
    | none   => return { expr := eNew }
    | some h =>
      let p ← xs.foldrM (init := h) fun x h => do
        mkFunExt (← mkLambdaFVars #[x] h)
      return { expr := eNew, proof? := p }

def simpArrow (e : Expr) : SimpM Result := do
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

def simpForall (e : Expr) : SimpM Result := withParent e do
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

def simpLet (e : Expr) : SimpM Result := do
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

@[export lean_dsimp]
private partial def dsimpImpl (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let pre (e : Expr) : SimpM TransformStep := do
    if let Step.visit r ← rewritePre (rflOnly := true) e then
      if r.expr != e then
        return .visit r.expr
    return .continue
  let post (e : Expr) : SimpM TransformStep := do
    if let Step.visit r ← rewritePost (rflOnly := true) e then
      if r.expr != e then
        return .visit r.expr
    let mut eNew ← reduce e
    if eNew.isFVar then
      eNew ← reduceFVar cfg (← getSimpTheorems) eNew
    if eNew != e then return .visit eNew else return .done e
  transform (usedLetOnly := cfg.zeta) e (pre := pre) (post := post)

def visitFn (e : Expr) : SimpM Result := do
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

def congrDefault (e : Expr) : SimpM Result := do
  if let some result ← tryAutoCongrTheorem? e then
    result.mkEqTrans (← visitFn result.expr)
  else
    withParent e <| e.withApp fun f args => do
      congrArgs (← simp f) args

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
def processCongrHypothesis (h : Expr) : SimpM Bool := do
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
def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : SimpM (Option Result) := withNewMCtxDepth do
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
    unless (← synthesizeArgs (.decl c.theoremName) xs bis) do
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

def congr (e : Expr) : SimpM Result := do
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

def simpApp (e : Expr) : SimpM Result := do
  if isOfNatNatLit e then
    -- Recall that we expand "orphan" kernel nat literals `n` into `ofNat n`
    return { expr := e }
  else
    congr e

def simpStep (e : Expr) : SimpM Result := do
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

def cacheResult (e : Expr) (cfg : Config) (r : Result) : SimpM Result := do
  if cfg.memoize && r.cache then
    let ctx ← readThe Simp.Context
    let dischargeDepth := ctx.dischargeDepth
    modify fun s => { s with cache := s.cache.insert e { r with dischargeDepth } }
  return r

partial def simpLoop (e : Expr) : SimpM Result := withIncRecDepth do
  let cfg ← getConfig
  if (← get).numSteps > cfg.maxSteps then
    throwError "simp failed, maximum number of steps exceeded"
  else
    checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult e cfg r
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : SimpM Result := do
    let eNew ← reduceStep r.expr
    if eNew != r.expr then
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    else
      let r ← r.mkEqTrans (← simpStep r.expr)
      visitPost cfg r
  visitPost (cfg : Config) (r : Result) : SimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Config) (r : Result) : SimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoop r.expr)
    cacheResult e cfg r

@[export lean_simp]
def simpImpl (e : Expr) : SimpM Result := withIncRecDepth do
  checkSystem "simp"
  if (← isProof e) then
    return { expr := e }
  go
where
  go : SimpM Result := do
    let cfg ← getConfig
    if cfg.memoize then
      let cache := (← get).cache
      if let some result := cache.find? e then
        /-
          If the result was cached at a dischargeDepth > the current one, it may not be valid.
          See issue #1234
        -/
        if result.dischargeDepth ≤ (← readThe Simp.Context).dischargeDepth then
          return result
    trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
    simpLoop e

@[inline] def withSimpConfig (ctx : Context) (x : MetaM α) : MetaM α :=
  withConfig (fun c => { c with etaStruct := ctx.config.etaStruct }) <| withReducible x

def main (e : Expr) (ctx : Context) (usedSimps : UsedSimps := {}) (methods : Methods := {}) : MetaM (Result × UsedSimps) := do
  let ctx := { ctx with config := (← ctx.config.updateArith) }
  withSimpConfig ctx do withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do
        let (r, s) ← simp e methods.toMethodsRef ctx |>.run { usedTheorems := usedSimps }
        trace[Meta.Tactic.simp.numSteps] "{s.numSteps}"
        return (r, s.usedTheorems)
    catch ex =>
      if ex.isRuntime then throwNestedTacticEx `simp ex else throw ex

def dsimpMain (e : Expr) (ctx : Context) (usedSimps : UsedSimps := {}) (methods : Methods := {}) : MetaM (Expr × UsedSimps) := do
  withSimpConfig ctx do withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do
        let (r, s) ← dsimp e methods.toMethodsRef ctx |>.run { usedTheorems := usedSimps }
        pure (r, s.usedTheorems)
    catch ex =>
      if ex.isRuntime then throwNestedTacticEx `dsimp ex else throw ex

end Simp
open Simp (UsedSimps SimprocsArray)

def simp (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (usedSimps : UsedSimps := {}) : MetaM (Simp.Result × UsedSimps) := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.main e ctx usedSimps (methods := Simp.mkDefaultMethodsCore simprocs)
  | some d => Simp.main e ctx usedSimps (methods := Simp.mkMethods simprocs d)

def dsimp (e : Expr) (ctx : Simp.Context)
    (usedSimps : UsedSimps := {}) : MetaM (Expr × UsedSimps) := do profileitM Exception "dsimp" (← getOptions) do
  Simp.dsimpMain e ctx usedSimps (methods := Simp.mkDefaultMethodsCore {})

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option MVarId × UsedSimps) := do
  let target ← instantiateMVars (← mvarId.getType)
  let (r, usedSimps) ← simp target ctx simprocs discharge? usedSimps
  if mayCloseGoal && r.expr.isTrue then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return (none, usedSimps)
  else
    return (← applySimpResultToTarget mvarId target r, usedSimps)

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option MVarId × UsedSimps) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    simpTargetCore mvarId ctx simprocs discharge? mayCloseGoal usedSimps

/--
  Apply the result `r` for `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToProp (mvarId : MVarId) (proof : Expr) (prop : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isFalse then
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
def simpStep (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option (Expr × Expr) × UsedSimps) := do
  let (r, usedSimps) ← simp prop ctx simprocs discharge? usedSimps
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
    if mayCloseGoal && r.expr.isFalse then
      mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
      return none
    else
      return some (fvarId, mvarId)
  else
    applySimpResultToLocalDeclCore mvarId fvarId (← applySimpResultToFVarId mvarId fvarId r mayCloseGoal)

def simpLocalDecl (mvarId : MVarId) (fvarId : FVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (usedSimps : UsedSimps := {}) : MetaM (Option (FVarId × MVarId) × UsedSimps) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let type ← instantiateMVars (← fvarId.getType)
    let (r, usedSimps) ← simpStep mvarId (mkFVar fvarId) type ctx simprocs discharge? mayCloseGoal usedSimps
    return (← applySimpResultToLocalDeclCore mvarId fvarId r, usedSimps)

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
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
      let (r, usedSimps') ← simp type ctx simprocs discharge? usedSimps
      usedSimps := usedSimps'
      match r.proof? with
      | some _ => match (← applySimpResultToProp mvarIdNew (mkFVar fvarId) type r) with
        | none => return (none, usedSimps)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return (none, usedSimps)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarIdNew ctx simprocs discharge? (usedSimps := usedSimps)) with
      | (none, usedSimps') => return (none, usedSimps')
      | (some mvarIdNew', usedSimps') => mvarIdNew := mvarIdNew'; usedSimps := usedSimps'
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "simp made no progress"
    return (some (fvarIdsNew, mvarIdNew), usedSimps)

def simpTargetStar (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (usedSimps : UsedSimps := {}) : MetaM (TacticResultCNM × UsedSimps) := mvarId.withContext do
  let mut ctx := ctx
  for h in (← getPropHyps) do
    let localDecl ← h.getDecl
    let proof  := localDecl.toExpr
    let simpTheorems ← ctx.simpTheorems.addTheorem (.fvar h) proof
    ctx := { ctx with simpTheorems }
  match (← simpTarget mvarId ctx simprocs discharge? (usedSimps := usedSimps)) with
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
      if typeNew.isFalse then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
        return (none, usedSimps)
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId typeNew
    if simplifyTarget then
      let target ← mvarIdNew.getType
      let (targetNew, usedSimps') ← dsimp target ctx usedSimps
      usedSimps := usedSimps'
      if targetNew.isTrue then
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
