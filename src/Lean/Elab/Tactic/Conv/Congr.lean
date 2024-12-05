/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Congr
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtin_tactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun _ => pure ()

private def congrImplies (mvarId : MVarId) : MetaM (List MVarId) := do
  let [mvarId₁, mvarId₂, _, _] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr) | throwError "'apply implies_congr' unexpected result"
  let mvarId₁ ← markAsConvGoal mvarId₁
  let mvarId₂ ← markAsConvGoal mvarId₂
  return [mvarId₁, mvarId₂]

private def isImplies (e : Expr) : MetaM Bool :=
  if e.isArrow then
    isProp e.bindingDomain! <&&> isProp e.bindingBody!
  else
    return false

private partial def mkCongrThm (origTag : Name) (f : Expr) (args : Array Expr) (addImplicitArgs := false) (nameSubgoals := true) :
    MetaM (Expr × Array (Option MVarId) × Array (Option MVarId)) := do
  let funInfo ← getFunInfoNArgs f args.size
  let some congrThm ← mkCongrSimpCore? f funInfo (← getCongrSimpKinds f funInfo) (subsingletonInstImplicitRhs := false)
    | throwError "'congr' conv tactic failed to create congruence theorem"
  let mut eNew := f
  let mut proof := congrThm.proof
  let mut mvarIdsNew := #[]
  let mut mvarIdsNewInsts := #[]
  for h : i in [:congrThm.argKinds.size] do
    let arg := args[i]!
    let argInfo := funInfo.paramInfo[i]!
    match congrThm.argKinds[i] with
    | .fixed | .cast =>
      eNew := mkApp eNew arg
      proof := mkApp proof arg;
      if addImplicitArgs || argInfo.isExplicit then
        mvarIdsNew := mvarIdsNew.push none
    | .eq =>
      if addImplicitArgs || argInfo.isExplicit then
        let tag ← if nameSubgoals then
          pure (appendTag origTag (← whnf (← inferType proof)).bindingName!)
        else pure origTag
        let (rhs, mvarNew) ← mkConvGoalFor arg tag
        eNew := mkApp eNew rhs
        proof := mkApp3 proof arg rhs mvarNew
        mvarIdsNew := mvarIdsNew.push (some mvarNew.mvarId!)
      else
        eNew := mkApp eNew arg
        proof := mkApp3 proof arg arg (← mkEqRefl arg)
    | .subsingletonInst =>
      proof := mkApp proof arg
      let rhs ← mkFreshExprMVar (← whnf (← inferType proof)).bindingDomain!
      eNew := mkApp eNew rhs
      proof := mkApp proof rhs
      mvarIdsNewInsts := mvarIdsNewInsts.push (some rhs.mvarId!)
    | .heq | .fixedNoParam => unreachable!
  if congrThm.argKinds.size < args.size then
    if congrThm.argKinds.size == 0 then
      throwError "'congr' conv tactic failed to create congruence theorem"
    let (proof', mvarIdsNew', mvarIdsNewInsts') ←
      mkCongrThm origTag eNew args[funInfo.getArity:] addImplicitArgs nameSubgoals
    for arg in args[funInfo.getArity:] do
      proof ← Meta.mkCongrFun proof arg
    proof ← mkEqTrans proof proof'
    mvarIdsNew := mvarIdsNew ++ mvarIdsNew'
    mvarIdsNewInsts := mvarIdsNewInsts ++ mvarIdsNewInsts'
  return (proof, mvarIdsNew, mvarIdsNewInsts)

private def resolveRhs (tacticName : String) (rhs rhs' : Expr) : MetaM Unit := do
  unless (← isDefEqGuarded rhs rhs') do
    throwError "invalid '{tacticName}' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"

private def resolveRhsFromProof (tacticName : String) (rhs proof : Expr) : MetaM Unit := do
  let some (_, _, rhs') := (← whnf (← inferType proof)).eq? | throwError "'{tacticName}' conv tactic failed, equality expected"
  resolveRhs tacticName rhs rhs'

def congr (mvarId : MVarId) (addImplicitArgs := false) (nameSubgoals := true) :
    MetaM (List (Option MVarId)) := mvarId.withContext do
  let origTag ← mvarId.getTag
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  if (← isImplies lhs) then
    return (← congrImplies mvarId).map Option.some
  else if lhs.isApp then
    let (proof, mvarIdsNew, mvarIdsNewInsts) ←
      mkCongrThm origTag lhs.getAppFn lhs.getAppArgs addImplicitArgs nameSubgoals
    resolveRhsFromProof "congr" rhs proof
    mvarId.assign proof
    return mvarIdsNew.toList ++ mvarIdsNewInsts.toList
  else
    throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"

@[builtin_tactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun _ => do
  replaceMainGoal <| List.filterMap id (← congr (← getMainGoal))

/-- Implementation of `arg 0`. -/
def congrFunN (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  unless lhs.isApp do
    throwError "invalid 'arg 0' conv tactic, application expected{indentExpr lhs}"
  lhs.withApp fun f xs => do
    let (g, mvarNew) ← mkConvGoalFor f
    mvarId.assign (← xs.foldlM (init := mvarNew) Meta.mkCongrFun)
    resolveRhs "arg 0" rhs (mkAppN g xs)
    return mvarNew.mvarId!

private partial def mkCongrArgZeroThm (tacticName : String) (origTag : Name) (f : Expr) (args : Array Expr) :
    MetaM (Expr × MVarId × Array MVarId) := do
  let funInfo ← getFunInfoNArgs f args.size
  let some congrThm ← mkCongrSimpCore? f funInfo (← getCongrSimpKindsForArgZero funInfo) (subsingletonInstImplicitRhs := false)
    | throwError "'{tacticName}' conv tactic failed to create congruence theorem"
  unless congrThm.argKinds[0]! matches .eq do
    throwError "'{tacticName}' conv tactic failed, cannot select argument"
  let mut eNew := f
  let mut proof := congrThm.proof
  let mut mvarIdNew? := none
  let mut mvarIdsNewInsts := #[]
  for h : i in [:congrThm.argKinds.size] do
    let arg := args[i]!
    let argInfo := funInfo.paramInfo[i]!
    match congrThm.argKinds[i] with
    | .fixed | .cast =>
      eNew := mkApp eNew arg
      proof := mkApp proof arg
    | .eq =>
      let (rhs, mvarNew) ← mkConvGoalFor arg origTag
      eNew := mkApp eNew rhs
      proof := mkApp3 proof arg rhs mvarNew
      if mvarIdNew?.isSome then throwError "'{tacticName}' conv tactic failed, cannot select argument"
      mvarIdNew? := some mvarNew.mvarId!
    | .subsingletonInst =>
      proof := mkApp proof arg
      let rhs ← mkFreshExprMVar (← whnf (← inferType proof)).bindingDomain!
      eNew := mkApp eNew rhs
      proof := mkApp proof rhs
      mvarIdsNewInsts := mvarIdsNewInsts.push rhs.mvarId!
    | .heq | .fixedNoParam => unreachable!
  let proof' ← args[congrThm.argKinds.size:].foldlM (init := proof) mkCongrFun
  return (proof', mvarIdNew?.get!, mvarIdsNewInsts)

/--
Implements `arg` for foralls. If `domain` is true, accesses the domain, otherwise accesses the codomain.
-/
def congrArgForall (tacticName : String) (domain : Bool) (mvarId : MVarId) (lhs rhs : Expr) : MetaM (List MVarId) := do
  let .forallE n t b bi := lhs | unreachable!
  if domain then
    if !b.hasLooseBVars then
      let (t', g) ← mkConvGoalFor t (← mvarId.getTag)
      mvarId.assign <| ← mkAppM ``implies_congr #[g, ← mkEqRefl b]
      resolveRhs tacticName rhs (.forallE n t' b bi)
      return [g.mvarId!]
    else if ← isProp b <&&> isProp lhs then
      let (_rhs, g) ← mkConvGoalFor t (← mvarId.getTag)
      let proof ← mkAppM ``forall_prop_congr_dom #[g, .lam n t b .default]
      resolveRhsFromProof tacticName rhs proof
      mvarId.assign proof
      return [g.mvarId!]
    else
      throwError m!"'{tacticName}' conv tactic failed, cannot select domain"
  else
    withLocalDeclD (← mkFreshUserName n) t fun arg => do
      let u ← getLevel t
      let q := b.instantiate1 arg
      let (q', g) ← mkConvGoalFor q (← mvarId.getTag)
      let v ← getLevel q
      let proof := mkAppN (.const ``pi_congr [u, v])
        #[t, .lam n t b .default, ← mkLambdaFVars #[arg] q', ← mkLambdaFVars #[arg] g]
      resolveRhsFromProof tacticName rhs proof
      mvarId.assign proof
      return [g.mvarId!]

/-- Implementation of `arg i`. -/
def congrArgN (tacticName : String) (mvarId : MVarId) (i : Int) (explicit : Bool) : MetaM (List MVarId) := mvarId.withContext do
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  if lhs.isForall then
    if i < -2 || i == 0 || i > 2 then throwError "invalid '{tacticName}' conv tactic, index is out of bounds for pi type"
    let domain := i == 1 || i == -2
    return ← congrArgForall tacticName domain mvarId lhs rhs
  else if lhs.isApp then
    lhs.withApp fun f xs => do
      let (f, xs) ← applyArgs f xs i
      let (proof, mvarIdNew, mvarIdsNewInsts) ← mkCongrArgZeroThm tacticName (← mvarId.getTag) f xs
      resolveRhsFromProof tacticName rhs proof
      mvarId.assign proof
      return mvarIdNew :: mvarIdsNewInsts.toList
  else
    throwError "invalid '{tacticName}' conv tactic, application or implication expected{indentExpr lhs}"
where
  applyArgs (f : Expr) (xs : Array Expr) (i : Int) : MetaM (Expr × Array Expr) := do
    if explicit then
      let i := if i > 0 then i - 1 else i + xs.size
      if i < 0 || i ≥ xs.size then
        throwError "invalid '{tacticName}' tactic, application has {xs.size} argument(s) but the index is out of bounds"
      let idx := i.natAbs
      return (mkAppN f xs[0:idx], xs[idx:])
    else
      let mut fType ← inferType f
      let mut j := 0
      let mut explicitIdxs := #[]
      for k in [0:xs.size] do
        unless fType.isForall do
          fType ← withTransparency .all <| whnf (fType.instantiateRevRange j k xs)
          j := k
        let .forallE _ _ b bi := fType | failure
        fType := b
        if bi.isExplicit then
          explicitIdxs := explicitIdxs.push k
      let i := if i > 0 then i - 1 else i + explicitIdxs.size
      if i < 0 || i ≥ explicitIdxs.size then
        throwError "invalid '{tacticName}' tactic, application has {explicitIdxs.size} explicit argument(s) but the index is out of bounds"
      let idx := explicitIdxs[i.natAbs]!
      return (mkAppN f xs[0:idx], xs[idx:])

def evalArg (tacticName : String) (i : Int) (explicit : Bool) : TacticM Unit := do
  if i == 0 then
    replaceMainGoal [← congrFunN (← getMainGoal)]
  else
    replaceMainGoal (← congrArgN tacticName (← getMainGoal) i explicit)

@[builtin_tactic Lean.Parser.Tactic.Conv.arg] def elabArg : Tactic := fun stx => do
  match stx with
  | `(conv| arg $[@%$tk?]? $[-%$neg?]? $i:num) =>
    let i : Int := if neg?.isSome then -i.getNat else i.getNat
    evalArg "arg" i (explicit := tk?.isSome)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun _ => do
  evalArg "lhs" (-2) false

@[builtin_tactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun _ => do
  evalArg "rhs" (-1) false

@[builtin_tactic Lean.Parser.Tactic.Conv.«fun»] def evalFun : Tactic := fun _ => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs := (← instantiateMVars lhs).cleanupAnnotations
    let .app f a := lhs
      | throwError "invalid 'fun' conv tactic, application expected{indentExpr lhs}"
    let (g, mvarNew) ← mkConvGoalFor f
    mvarId.assign (← Meta.mkCongrFun mvarNew a)
    resolveRhs "fun" rhs (.app g a)
    replaceMainGoal [mvarNew.mvarId!]

def extLetBodyCongr? (mvarId : MVarId) (lhs rhs : Expr) : MetaM (Option MVarId) := do
  match lhs with
  | .letE n t v b _ =>
    let u₁ ← getLevel t
    let f := mkLambda n .default t b
    unless (← isTypeCorrect f) do
      throwError "failed to abstract let-expression, result is not type correct"
    let (β, u₂, f') ← withLocalDeclD n t fun a => do
      let type ← inferType (mkApp f a)
      let β ← mkLambdaFVars #[a] type
      let u₂ ← getLevel type
      let rhsBody ← mkFreshExprMVar type
      let f' ← mkLambdaFVars #[a] rhsBody
      let rhs' := mkLet n t v f'.bindingBody!
      unless (← isDefEq rhs rhs') do
        throwError "failed to go inside let-declaration, type error"
      return (β, u₂, f')
    let (arg, mvarId') ← withLocalDeclD n t fun x => do
      let eqLhs := f.beta #[x]
      let eqRhs := f'.beta #[x]
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq eqLhs eqRhs)
      let arg ← mkLambdaFVars #[x] mvarNew
      return (arg, mvarNew.mvarId!)
    let val := mkApp6 (mkConst ``let_body_congr [u₁, u₂]) t β f f' v arg
    mvarId.assign val
    return some (← markAsConvGoal mvarId')
  | _ => return none

private def extCore (mvarId : MVarId) (userName? : Option Name) : MetaM MVarId :=
  mvarId.withContext do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs := (← instantiateMVars lhs).cleanupAnnotations
    if let .forallE n d b bi := lhs then
      let u ← getLevel d
      let p : Expr := .lam n d b bi
      let userName ← if let some userName := userName? then pure userName else mkFreshBinderNameForTactic n
      let (q, h, mvarNew) ← withLocalDecl userName bi d fun a => do
        let pa := b.instantiate1 a
        let (qa, mvarNew) ← mkConvGoalFor pa
        let q ← mkLambdaFVars #[a] qa
        let h ← mkLambdaFVars #[a] mvarNew
        resolveRhs "ext" rhs (← mkForallFVars #[a] qa)
        return (q, h, mvarNew)
      let proof := mkApp4 (mkConst ``forall_congr [u]) d p q h
      mvarId.assign proof
      return mvarNew.mvarId!
    else if let some mvarId ← extLetBodyCongr? mvarId lhs rhs then
      return mvarId
    else
      let lhsType ← whnfD (← inferType lhs)
      unless lhsType.isForall do
        throwError "invalid 'ext' conv tactic, function or arrow expected{indentD m!"{lhs} : {lhsType}"}"
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``funext) | throwError "'apply funext' unexpected result"
      let userNames := if let some userName := userName? then [userName] else []
      let (_, mvarId) ← mvarId.introN 1 userNames
      markAsConvGoal mvarId

private def ext (userName? : Option Name) : TacticM Unit := do
  replaceMainGoal [← extCore (← getMainGoal) userName?]

@[builtin_tactic Lean.Parser.Tactic.Conv.ext] def evalExt : Tactic := fun stx => do
  let ids := stx[1].getArgs
  if ids.isEmpty then
    ext none
  else
    for id in ids do
      withRef id <| ext id.getId

-- syntax (name := enter) "enter" " [" enterArg,+ "]" : conv
@[builtin_tactic Lean.Parser.Tactic.Conv.enter] def evalEnter : Tactic := fun stx => do
  let token := stx[0]
  let lbrak := stx[1]
  let enterArgsAndSeps := stx[2].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numEnterArgs := (enterArgsAndSeps.size + 1) / 2
  for i in [:numEnterArgs] do
    let enterArg := enterArgsAndSeps[2 * i]!
    let sep := enterArgsAndSeps.getD (2 * i + 1) .missing
    -- show state up to (incl.) next `,` and show errors on `enterArg`
    withTacticInfoContext (mkNullNode #[enterArg, sep]) <| withRef enterArg do
      match enterArg with
      | `(Parser.Tactic.Conv.enterArg| $arg:argArg) => evalTactic (← `(conv| arg $arg))
      | `(Parser.Tactic.Conv.enterArg| $id:ident)   => evalTactic (← `(conv| ext $id))
      | _ => pure ()

end Lean.Elab.Tactic.Conv
