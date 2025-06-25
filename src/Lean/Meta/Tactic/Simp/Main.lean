/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.UnifyEq
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Simp.Diagnostics
import Lean.Meta.Match.Value

namespace Lean.Meta
namespace Simp

register_builtin_option backward.dsimp.proofs : Bool := {
    defValue := false
    descr    := "Let `dsimp` simplify proof terms"
  }

builtin_initialize congrHypothesisExceptionId : InternalExceptionId ←
  registerInternalExceptionId `congrHypothesisFailed

def throwCongrHypothesisFailed : MetaM α :=
  throw <| Exception.internal congrHypothesisExceptionId

/-- Return true if `e` is of the form `ofNat n` where `n` is a kernel Nat literal -/
def isOfNatNatLit (e : Expr) : Bool :=
  e.isAppOf ``OfNat.ofNat && e.getAppNumArgs >= 3 && (e.getArg! 1).isRawNatLit

/--
If `e` is a raw Nat literal and `OfNat.ofNat` is not in the list of declarations to unfold,
return an `OfNat.ofNat`-application.
-/
def foldRawNatLit (e : Expr) : SimpM Expr := do
  match e.rawNatLit? with
  | some n =>
    let ctx ← readThe Simp.Context
    /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
        to avoid non-termination. See issue #788.  -/
    if ctx.inNumLit || ctx.isDeclToUnfold ``OfNat.ofNat then
      return e
    else
      return toExpr n
  | none   => return e

/-- Return true if `e` is of the form `ofScientific n b m` where `n` and `m` are kernel Nat literals. -/
def isOfScientificLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfScientific.ofScientific 5 && (e.getArg! 4).isRawNatLit && (e.getArg! 2).isRawNatLit

/-- Return true if `e` is of the form `Char.ofNat n` where `n` is a kernel Nat literals. -/
def isCharLit (e : Expr) : Bool :=
  e.isAppOfArity ``Char.ofNat 1 && e.appArg!.isRawNatLit

/--
Unfold definition even if it is not marked as `@[reducible]`.
Remark: We never unfold irreducible definitions. Mathlib relies on that in the implementation of the
command `irreducible_def`.
-/
private def unfoldDefinitionAny? (e : Expr) : MetaM (Option Expr) := do
  if let .const declName _ := e.getAppFn then
    if (← isIrreducible declName) then
      return none
  unfoldDefinition? e (ignoreTransparency := true)

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
          match (← withSimpMetaConfig <| reduceProj? e.getAppFn) with
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
          unless (← isConstructorApp major) do
            return none
          reduceProjCont? (← unfoldDefinitionAny? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)

private def reduceFVar (cfg : Config) (thms : SimpTheoremsArray) (e : Expr) : SimpM Expr := do
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    return v
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
      unfoldDefinitionAny? e
    else
      -- `We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      unfoldDefinitionAny? e
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      unfoldDefinitionAny? e
    else if (← isMatchDef fName) then
      let some value ← unfoldDefinitionAny? e | return none
      let .reduced value ← withSimpMetaConfig <| reduceMatcher? value | return none
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
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProj? e) with
    | some e => return e
    | none =>
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
    if e.isLet then
      return e.letBody!.instantiate1 e.letValue!
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {.ofConst e.getAppFn}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
  | none => foldRawNatLit e

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    trace[Debug.Meta.Tactic.simp] "reduce {e} => {e'}"
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
deriving Repr

def getSimpLetCase (n : Name) (t : Expr) (b : Expr) (nondep : Bool) : MetaM SimpLetCase := do
  withLocalDeclD n t fun x => do
    let bx := b.instantiate1 x
    /-
    If the let has `nondep := true`, then we know the body does not depend on the value already.
    Then there are two cases, depending on whether or not the type of the body refers to the variable.
    -/
    if nondep then
      let bxType ← whnf (← inferType bx)
      if (← dependsOn bxType x.fvarId!) then
        return .nondepDepVar
      else
        return .nondep
    /-
    Otherwise, we first detect whether `nondep := true` *should* have been set by checking type correctness of the body.
    If that fails, the let is dependent.
    -/
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

/--
We use `withNewlemmas` whenever updating the local context.
-/
def withNewLemmas {α} (xs : Array Expr) (f : SimpM α) : SimpM α := do
  if (← getConfig).contextual then
    withFreshCache do
      let mut s ← getSimpTheorems
      let mut updated := false
      let ctx ← getContext
      for x in xs do
        if (← isProof x) then
          s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
          updated := true
      if updated then
        withSimpTheorems s f
      else
        f
  else if (← getMethods).wellBehavedDischarge then
    -- See comment at `Methods.wellBehavedDischarge` to understand why
    -- we don't have to reset the cache
    f
  else
    withFreshCache do f

def simpProj (e : Expr) : SimpM Result := do
  match (← withSimpMetaConfig <| reduceProj? e) with
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
    r.addLambdas xs

def simpArrow (e : Expr) : SimpM Result := do
  trace[Debug.Meta.Tactic.simp] "arrow {e}"
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← simp p
  trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
  if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
    trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmas #[h] do
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
  let .letE n t v b nondep := e | unreachable!
  if (← getConfig).zeta then
    return { expr := b.instantiate1 v }
  else if !b.hasLooseBVars && (← getConfig).zetaUnused then
    return { expr := b.lowerLooseBVars 1 1 }
  else
    let simpLetCase ← getSimpLetCase n t b nondep
    trace[Debug.Meta.Tactic.simp] "getSimpLetCase is {repr simpLetCase}:{indentExpr e}"
    match simpLetCase with
    | SimpLetCase.dep => return { expr := (← dsimp e) }
    | SimpLetCase.nondep =>
      let rv ← simp v
      withLocalDeclD n t fun x => withNewLemmas #[x] do
        let bx := b.instantiate1 x
        let rbx ← simp bx
        let hb? ← match rbx.proof? with
          | none => pure none
          | some h => pure (some (← mkLambdaFVars #[x] h))
        let e' := mkLet n t rv.expr (← rbx.expr.abstractM #[x]) (nondep := true)
        match rv.proof?, hb? with
        | none,   none   => return { expr := e' }
        | some h, none   => return { expr := e', proof? := some (← mkLetValCongr (← mkLambdaFVars #[x] rbx.expr) h) }
        | _,      some h => return { expr := e', proof? := some (← mkLetCongr (← rv.getProof) h) }
    | SimpLetCase.nondepDepVar =>
      let v' ← dsimp v
      withLocalDeclD n t fun x => withNewLemmas #[x] do
        let bx := b.instantiate1 x
        let rbx ← simp bx
        let e' := mkLet n t v' (← rbx.expr.abstractM #[x]) (nondep := true)
        match rbx.proof? with
        | none => return { expr := e' }
        | some h =>
          let h ← mkLambdaFVars #[x] h
          return { expr := e', proof? := some (← mkLetBodyCongr v' h) }

private def dsimpReduce : DSimproc := fun e => do
  let mut eNew ← reduce e
  if eNew.isFVar then
    eNew ← reduceFVar (← getConfig) (← getSimpTheorems) eNew
  if eNew != e then return .visit eNew else return .done e

/-- Auxiliary `dsimproc` for not visiting proof terms. -/
private def doNotVisitProofs : DSimproc := fun e => do
  if ← isProof e then
    if !backward.dsimp.proofs.get (← getOptions) then
      return .done e
    else
      return .continue e
  else
    return .continue e

/-- Helper `dsimproc` for `visitOfNat` and `visitOfScientific` -/
@[specialize] private def visitNum (pred : Expr → Bool) (declName : Name) : DSimproc := fun e => do
  if pred e then
    if (← readThe Simp.Context).isDeclToUnfold declName then
      return .continue e
    else
      let e ← withFreshDSimpCache <| withInNumLit <| e.withApp fun f args => return mkAppN f (← args.mapM dsimp)
      -- Users may have added a `[simp]` rfl theorem for the literal
      match (← (← getMethods).dpost e) with
      | .continue none => return .done e
      | r => return r
  else
    return .continue e

/--
Auxiliary `dsimproc` for not visiting `OfNat.ofNat` application subterms.
This is the `dsimp` equivalent of the approach used at `visitApp`.
Recall that we fold orphan raw Nat literals.
-/
private def visitOfNat : DSimproc := visitNum isOfNatNatLit ``OfNat.ofNat

/--
Auxiliary `dsimproc` for not visiting `OfScientific.ofScientific` application subterms.
-/
private def visitOfScientific : DSimproc := visitNum isOfScientificLit ``OfScientific.ofScientific

/--
Auxiliary `dsimproc` for not visiting `Char` literal subterms.
-/
private def visitCharLit : DSimproc := visitNum isCharLit ``Char.ofNat

@[export lean_dsimp]
private partial def dsimpImpl (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let m ← getMethods
  let pre := m.dpre >> visitOfNat >> visitOfScientific >> visitCharLit >> doNotVisitProofs
  let post := m.dpost >> dsimpReduce
  withInDSimpWithCache fun cache => do
    transformWithCache e cache (usedLetOnly := cfg.zeta || cfg.zetaUnused) (pre := pre) (post := post)

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
def processCongrHypothesis (h : Expr) (hType : Expr) : SimpM Bool := do
  forallTelescopeReducing hType fun xs hType => withNewLemmas xs do
    let lhs ← instantiateMVars hType.appFn!.appArg!
    let r ← simp lhs
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← withSimpMetaConfig <| isDefEq m val) do
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
def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : SimpM (Option Result) := withNewMCtxDepth do withParent e do
  recordCongrTheorem c.theoremName
  trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let thmType ← inferType thm
  let thmHasBinderNameHint := thmType.hasBinderNameHint
  let (xs, bis, type) ← forallMetaTelescopeReducing thmType
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
  if (← withSimpMetaConfig <| isDefEq lhs e) then
    let mut modified := false
    for i in c.hypothesesPos do
      let h := xs[i]!
      let hType ← instantiateMVars (← inferType h)
      let hType ← if thmHasBinderNameHint then hType.resolveBinderNameHint else pure hType
      try
        if (← processCongrHypothesis h hType) then
          modified := true
      catch _ =>
        trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {hType}"
        -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
        -- does not catch runtime exceptions by default.
        return none
    unless modified do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
      return none
    unless (← synthesizeArgs (.decl c.theoremName) bis xs) do
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

/--
Returns `true` if `e` is of the form `@letFun _ (fun _ => β) _ _`

`β` must not contain loose bound variables. Recall that `simp` does not have support for `let_fun`s
where resulting type depends on the `let`-value. Example:
```
let_fun n := 10;
BitVec.zero n
```
-/
def isNonDepLetFun (e : Expr) : Bool :=
  let_expr letFun _ beta _ body := e | false
  beta.isLambda && !beta.bindingBody!.hasLooseBVars && body.isLambda

/--
Auxiliary structure used to represent the return value of `simpNonDepLetFun.go`.
-/
private structure SimpLetFunResult where
  /--
  The simplified expression. Note that is may contain loose bound variables.
  `simpNonDepLetFun.go` attempts to minimize the quadratic overhead imposed
  by the locally nameless discipline in a sequence of `let_fun` declarations.
  -/
  expr     : Expr
  /--
  The proof that the simplified expression is equal to the input one.
  It may contain loose bound variables. See `expr` field.
  -/
  proof    : Expr
  /--
  `modified := false` iff `expr` is structurally equal to the input expression.
  -/
  modified : Bool

/--
Simplifies a sequence of `let_fun` declarations.
It attempts to minimize the quadratic overhead imposed by
the locally nameless discipline.
-/
partial def simpNonDepLetFun (e : Expr) : SimpM Result := do
  let cfg ← getConfig
  let rec go (xs : Array Expr) (e : Expr) : SimpM SimpLetFunResult := do
    /-
    Helper function applied when `e` is not a `let_fun` or
    is a non supported `let_fun` (e.g., the resulting type depends on the value).
    -/
    let stop : SimpM SimpLetFunResult := do
      let e := e.instantiateRev xs
      let r ← simp e
      return { expr := r.expr.abstract xs, proof := (← r.getProof).abstract xs, modified :=  r.expr != e }
    let_expr f@letFun alpha betaFun val body := e | stop
    let us := f.constLevels!
    let [_, v] := us | stop
    /-
    Recall that `let_fun x : α := val; e[x]` is encoded at
    ```
    @letFun α (fun x : α => β[x]) val (fun x : α => e[x])
    ```
    `betaFun` is `(fun x : α => β[x])`. If `β[x]` does not have loose bound variables then the resulting type
    does not depend on the value since it does not depend on `x`.

    We also check whether `alpha` does not depend on the previous `let_fun`s in the sequence.
    This check is just to make the code simpler. It is not common to have a type depending on the value of a previous `let_fun`.
    -/
    if alpha.hasLooseBVars || !betaFun.isLambda || !body.isLambda || betaFun.bindingBody!.hasLooseBVars then
      stop
    else if (cfg.zeta || cfg.zetaUnused) && !body.bindingBody!.hasLooseBVar 0 then
      /-
      Redundant `let_fun`. The simplifier will remove it when `zetaUnused := true`.
      Remark: the `hasLooseBVar` check here may introduce a quadratic overhead in the worst case.
      If observe that in practice, we may use a separate step for removing unused variables.

      Remark: note that we do **not** simplify the value in this case.
      -/
      let x := mkConst `__no_used_dummy__ -- dummy value
      let { expr, proof, .. } ← go (xs.push x) body.bindingBody!
      let proof := mkApp6 (mkConst ``letFun_unused us) alpha betaFun.bindingBody! val body.bindingBody! expr proof
      let expr := expr.lowerLooseBVars 1 1
      let proof := proof.lowerLooseBVars 1 1
      return { expr, proof, modified := true }
    else
      let beta    := betaFun.bindingBody!
      let valInst := val.instantiateRev xs
      let valResult ← simp valInst
      withLocalDecl body.bindingName! body.bindingInfo! alpha fun x => do
        let valIsNew := valResult.expr != valInst
        let { expr, proof, modified := bodyIsNew } ← go (xs.push x) body.bindingBody!
        if !valIsNew && !bodyIsNew then
          /-
          Value and body were not simplified. We just return `e` and a new refl proof.
          We must use the low-level `Expr` APIs because `e` may contain loose bound variables.
          -/
          let proof := mkApp2 (mkConst ``Eq.refl [v]) beta e
          return { expr := e, proof, modified := false }
        else
          let body' := mkLambda body.bindingName! body.bindingInfo! alpha expr
          let val'  := valResult.expr.abstract xs
          let e'    := mkApp4 f alpha betaFun val' body'
          if valIsNew && bodyIsNew then
            -- Value and body were simplified
            let valProof := (← valResult.getProof).abstract xs
            let proof := mkApp8 (mkConst ``letFun_congr us) alpha beta val val' body body' valProof (mkLambda body.bindingName! body.bindingInfo! alpha proof)
            return { expr := e', proof, modified := true }
          else if valIsNew then
            -- Only the value was simplified.
            let valProof := (← valResult.getProof).abstract xs
            let proof := mkApp6 (mkConst ``letFun_val_congr us) alpha beta val val' body valProof
            return { expr := e', proof, modified := true }
          else
            -- Only the body was simplified.
            let proof := mkApp6 (mkConst ``letFun_body_congr us) alpha beta val body body' (mkLambda body.bindingName! body.bindingInfo! alpha proof)
            return { expr := e', proof, modified := true }
  let { expr, proof, modified } ← go #[] e
  if !modified then
    return { expr := e }
  else
    return { expr, proof? := proof }

def simpApp (e : Expr) : SimpM Result := do
  if isOfNatNatLit e || isOfScientificLit e then
    -- Recall that we fold "orphan" kernel Nat literals `n` into `OfNat.ofNat n`
    withFreshCache <| withFreshDSimpCache <| withInNumLit <| congr e
  else if isCharLit e then
    return { expr := e }
  else if let some (args, n, t, v, b) := e.letFunAppArgs? then
    /-
    Note: we will be removing `letFun`, and we want everything to be in terms of `nondep := true` lets.
    This used to call `simpNonDepLetFun`, which is optimized for letFun telescopes.
    Considerations:
    - we will soon replace `simpNonDepLetFun` with a `let` version
    - simp is now using the `nondep` flag to cache which `let`s are nondependent.
    - even without the optimized version we still manage to pass the test suite for now without timing out.
    -/
    return { expr := mkAppN (Expr.letE n t v b true) args }
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
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }

def cacheResult (e : Expr) (cfg : Config) (r : Result) : SimpM Result := do
  if cfg.memoize && r.cache then
    modify fun s => { s with cache := s.cache.insert e r }
  return r

partial def simpLoop (e : Expr) : SimpM Result := withIncRecDepth do
  let cfg ← getConfig
  if cfg.memoize then
    let cache := (← get).cache
    if let some result := cache.find? e then
      return result
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
      trace[Debug.Meta.Tactic.simp] "reduceStep (pre) {e} => {eNew}"
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
  trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
  simpLoop e

@[inline] def withCatchingRuntimeEx (x : SimpM α) : SimpM α := do
  if (← getConfig).catchRuntime then
    tryCatchRuntimeEx x
      fun ex => do
        reportDiag (← get).diag
        if ex.isRuntime then
          throwNestedTacticEx `simp ex
        else
          throw ex
  else
    x

def mainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Result × State) := do
  SimpM.run ctx s methods <| withCatchingRuntimeEx <| simp e

def main (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Result × Stats) := do
  let (r, s) ← mainCore e ctx { stats with } methods
  return (r, { s with })

def dsimpMainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Expr × State) := do
  SimpM.run ctx s methods <| withCatchingRuntimeEx <| dsimp e

def dsimpMain (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Expr × Stats) := do
  let (r, s) ← dsimpMainCore e ctx { stats with } methods
  return (r, { s with })

end Simp
open Simp (SimprocsArray Stats)

def simpCore (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (s : Simp.State := {}) : MetaM (Simp.Result × Simp.State) := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.mainCore e ctx s (methods := Simp.mkDefaultMethodsCore simprocs)
  | some d => Simp.mainCore e ctx s (methods := Simp.mkMethods simprocs d (wellBehavedDischarge := false))

def simp (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (stats : Stats := {}) : MetaM (Simp.Result × Stats) := do profileitM Exception "simp" (← getOptions) do
  let (r, s) ← simpCore e ctx simprocs discharge? { stats with }
  return (r, { s with })

def dsimp (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[])
    (stats : Stats := {}) : MetaM (Expr × Stats) := do profileitM Exception "dsimp" (← getOptions) do
  Simp.dsimpMain e ctx stats (methods := Simp.mkDefaultMethodsCore simprocs )

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
  let target ← instantiateMVars (← mvarId.getType)
  let (r, stats) ← simp target ctx simprocs discharge? stats
  if mayCloseGoal && r.expr.isTrue then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return (none, stats)
  else
    return (← applySimpResultToTarget mvarId target r, stats)

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option MVarId × Stats) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    simpTargetCore mvarId ctx simprocs discharge? mayCloseGoal stats

/--
Applies the result `r` for `type` (which is inhabited by `val`). Returns `none` if the goal was closed. Returns `some (val', type')`
otherwise, where `val' : type'` and `type'` is the simplified `type`.

This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResult (mvarId : MVarId) (val : Expr) (type : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isFalse then
    match r.proof? with
    | some eqProof => mvarId.assign (← mkFalseElim (← mvarId.getType) (mkApp4 (mkConst ``Eq.mp [levelZero]) type r.expr eqProof val))
    | none => mvarId.assign (← mkFalseElim (← mvarId.getType) val)
    return none
  else
    match r.proof? with
    | some eqProof =>
      let u ← getLevel type
      return some (mkApp4 (mkConst ``Eq.mp [u]) type r.expr eqProof val, r.expr)
    | none =>
      if r.expr != type then
        return some ((← mkExpectedTypeHint val r.expr), r.expr)
      else
        return some (val, r.expr)

@[deprecated applySimpResult (since := "2025-03-26")]
def applySimpResultToProp (mvarId : MVarId) (proof : Expr) (prop : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) :=
  applySimpResult mvarId proof prop r mayCloseGoal

def applySimpResultToFVarId (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) (mayCloseGoal : Bool) : MetaM (Option (Expr × Expr)) := do
  let localDecl ← fvarId.getDecl
  applySimpResult mvarId (mkFVar fvarId) localDecl.type r mayCloseGoal

/--
  Simplify `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpStep (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option (Expr × Expr) × Stats) := do
  let (r, stats) ← simp prop ctx simprocs discharge? stats
  return (← applySimpResult mvarId proof prop r (mayCloseGoal := mayCloseGoal), stats)

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
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option (FVarId × MVarId) × Stats) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let type ← instantiateMVars (← fvarId.getType)
    let (r, stats) ← simpStep mvarId (mkFVar fvarId) type ctx simprocs discharge? mayCloseGoal stats
    return (← applySimpResultToLocalDeclCore mvarId fvarId r, stats)

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Stats := {}) : MetaM (Option (Array FVarId × MVarId) × Stats) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut stats := stats
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
      let (r, stats') ← simp type ctx simprocs discharge? stats
      stats := stats'
      match r.proof? with
      | some _ => match (← applySimpResult mvarIdNew (mkFVar fvarId) type r) with
        | none => return (none, stats)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return (none, stats)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarIdNew ctx simprocs discharge? (stats := stats)) with
      | (none, stats') => return (none, stats')
      | (some mvarIdNew', stats') => mvarIdNew := mvarIdNew'; stats := stats'
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "simp made no progress"
    return (some (fvarIdsNew, mvarIdNew), stats)

def simpTargetStar (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (stats : Stats := {}) : MetaM (TacticResultCNM × Stats) := mvarId.withContext do
  let mut ctx := ctx
  for h in (← getPropHyps) do
    let localDecl ← h.getDecl
    let proof  := localDecl.toExpr
    let simpTheorems ← ctx.simpTheorems.addTheorem (.fvar h) proof (config := ctx.indexConfig)
    ctx := ctx.setSimpTheorems simpTheorems
  match (← simpTarget mvarId ctx simprocs discharge? (stats := stats)) with
  | (none, stats) => return (TacticResultCNM.closed, stats)
  | (some mvarId', stats') =>
    if (← mvarId.getType) == (← mvarId'.getType) then
      return (TacticResultCNM.noChange, stats)
    else
      return (TacticResultCNM.modified mvarId', stats')

def dsimpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
   mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut stats : Stats := stats
    for fvarId in fvarIdsToSimp do
      let type ← instantiateMVars (← fvarId.getType)
      let (typeNew, stats') ← dsimp type ctx simprocs
      stats := stats'
      if typeNew.isFalse then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
        return (none, stats)
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId typeNew
    if simplifyTarget then
      let target ← mvarIdNew.getType
      let (targetNew, stats') ← dsimp target ctx simprocs stats
      stats := stats'
      if targetNew.isTrue then
        mvarIdNew.assign (mkConst ``True.intro)
        return (none, stats)
      if let some (_, lhs, rhs) := targetNew.consumeMData.eq? then
        if (← withReducible <| isDefEq lhs rhs) then
          mvarIdNew.assign (← mkEqRefl lhs)
          return (none, stats)
      if target != targetNew then
        mvarIdNew ← mvarIdNew.replaceTargetDefEq targetNew
      pure () -- FIXME: bug in do notation if this is removed?
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "dsimp made no progress"
    return (some mvarIdNew, stats)

end Lean.Meta
