/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.FixedParams
import Lean.Elab.PreDefinition.EqnsUtils
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Tactic.Split
import Lean.Meta.Match.Lifter

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

public structure EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  recArgPos : Nat
  declNames : Array Name
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

def brecOnMotiveIdxAndNumMajors (brecOnName : Name) (numParams numTypeFormers : Nat) :
    MetaM (Nat × Nat) := do
  let val ← getConstVal brecOnName
  let arity := val.type.getForallArity
  let .bvar motiveIdxRev := val.type.getForallBody.getAppFn | throwError "Unexpected `brecOn` type"
  let motiveIdx := arity - 1 - motiveIdxRev
  return (motiveIdx - numParams, arity - numParams - 2 * numTypeFormers)

def etaExpand1 (e : Expr) : MetaM Expr := do
  if e.isLambda then
    return e
  let ty ← inferType e
  let .forallE nm t _ bi ← whnf ty |
    return .sort 0 -- not a lambda
  return .lam nm t (e.app (.bvar 0)) bi

structure ProveContext where
  belowVar : Expr
  numInductParams : Nat
  numMajors : Nat
  alts : Array Expr
  recFns : NameSet

private def getAppArgsAux' : Expr → Array Expr → Nat → Array Expr
  | .app f a, as, i => getAppArgsAux' f (as.set! i a) (i-1)
  | .mdata _ f, as, i => getAppArgsAux' f as i
  | _, as, _ => as

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` -/
@[inline] def _root_.Lean.Expr.getAppArgs' (e : Expr) : Array Expr :=
  let dummy := mkSort Level.zero
  let nargs := e.getAppNumArgs
  getAppArgsAux' e (.replicate nargs dummy) (nargs-1)

/--
Returns `(inner, trans)` where `inner.getAppFn` is not a projection and
`trans.instantiate1 inner = e`.
-/
def peelProjs (e : Expr) : Expr × Expr :=
  match e with
  | .proj ty i s =>
    let (s', ps) := peelProjs s
    (s', .proj ty i ps)
  | .app f a =>
    let (f', ps) := peelProjs f
    if ps matches .bvar _ then
      (e, ps)
    else
      (f', .app ps a)
  | _ => (e, .bvar 0)

/--
If possible, returns `some (inner, trans)` where `trans.instantiate1 inner = e` and
`trans` is equivalent to `shape` except in application arguments.
-/
def peelProjsLike (e : Expr) (shape : Expr) : Option (Expr × Expr) := do
  match e, shape with
  | .proj ty i s, .proj ty' i' s' =>
    guard <| ty == ty' && i = i'
    let (s', ps) ← peelProjsLike s s'
    some (s', .proj ty i ps)
  | .app f a, .app f' _ =>
    let (f', ps) ← peelProjsLike f f'
    some (f', .app ps a)
  | _, .bvar 0 => some (e, .bvar 0)
  | _, _ => none

/--
Given `e` and `trans`, returns `(e', trans')` such that `e'.getAppNumArgs ≤ arity` and
`trans'.instantiate1 e' = trans.instantiate1 e`.
-/
def updateTransformationsWithOverargs (e trans : Expr) (arity : Nat) : Expr × Expr :=
  let ourArity := e.getAppNumArgs
  if arity < ourArity then
    let numOverargs := ourArity - arity
    (e.getBoundedAppFn numOverargs, trans.instantiate1 (mkAppN (.bvar 0) (e.getBoundedAppArgs numOverargs)))
  else
    (e, trans)

partial def reduceProjs (e : Expr) (argsRev : Array Expr := #[]) : Expr :=
  match e with
  | .proj ty i s =>
    let s := reduceProjs s
    let res :=
      match ty, i with
      | ``PProd, 0 => if s.isAppOfArity ``PProd.mk 4 then s.appFn!.appArg! else e
      | ``PProd, 1 => if s.isAppOfArity ``PProd.mk 4 then s.appArg! else e
      | _, _ => e
    mkAppRev res argsRev
  | .app f a => reduceProjs f (argsRev.push a)
  | .lam _ _ b _ =>
    if argsRev.isEmpty then
      e
    else
      let back := argsRev.back!
      let argsRev := argsRev.pop
      reduceProjs (b.instantiate1 back) argsRev
  | _ => mkAppRev e argsRev

def deltaRecDef (nm : Name) (us : List Level) (args : Array Expr) : MetaM (Expr × Expr) := do
  let info ← getConstInfo nm
  let value ← instantiateValueLevelParams info us
  let value := value.beta args
  let value := value.eta
  let (brecApp, projs) := peelProjs value
  let .const brecDef brecLvls := brecApp.getAppFn |
    throwError "Invalid recursive occurrence, expected application of `brecOn` at{indentExpr value}"
  unless isBRecOnRecursor (← getEnv) brecDef do
    throwError "Invalid recursive occurrence, expected application of `brecOn` at{indentExpr value}"
  let arity := (← getConstVal brecDef).type.getForallArity
  trace[Elab.definition.structural.eqns] "Before update: {projs}"
  let (brecApp, transformations) := updateTransformationsWithOverargs brecApp projs arity
  let goApp := mkAppN (.const (brecDef.str "go") brecLvls) brecApp.getAppArgs
  trace[Elab.definition.structural.eqns] "Have {goApp} and {transformations}"
  return (goApp, transformations.instantiate1 (.proj ``PProd 0 (.bvar 0)))

/--
We use this for binder types: Binder types are head-beta-reduced once in `mkForallFVars` and
`mkLambdaFVars`. However, `headBeta` might also return a expression that can be head-beta-reduced
further; to make sure we land on a common expression we head-beta-reduce both sides to a fixpoint.
-/
partial def recHeadBeta (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then recHeadBeta (f.betaRev e.getAppRevArgs) else e

/--
Note: A return value of `none` indicates a reflexivity proof.
Furthermore, `lhs` and `rhs` must not be proofs.
`isDep = true` means that the proof must be `rfl` and thus the return value always `none`.
A successful return also implies that the types of `lhs` and `rhs` are defeq.

`lhs` here is part of the elaborated construction and `rhs` part of the user-provided value.
-/
partial def proveEq (ctx : ProveContext) (lhs rhs : Expr) (isDep checkTypes : Bool) :
    MetaM (Option Expr) := withIncRecDepth do
  if lhs == rhs then
    return none
  trace[Elab.definition.structural.eqns] "Visiting{indentExpr lhs}\nand{indentExpr rhs}"
  match lhs, rhs with
  | .mdata _ lhs, rhs => proveEq ctx lhs rhs isDep checkTypes
  | lhs, .mdata _ rhs => proveEq ctx lhs rhs isDep checkTypes
  | .const nm us, .const nm' us' =>
    if nm == nm' && us.isEqv us' Level.isEquiv then
      return none
    throwError "Different constants at{indentExpr (lhs.setPPUniverses true)}\n\
      and{indentExpr (rhs.setPPUniverses true)}"
  | .sort u, .sort v =>
    if u.isEquiv v then
      return none
    throwError "Different sorts at{indentExpr lhs}\nand{indentExpr rhs}"
  | .forallE nm t b bi, .forallE nm' t' b' bi' =>
    discard <| proveEq ctx (recHeadBeta t) (recHeadBeta t') (isDep := true) (checkTypes := true)
    withLocalDecl nm bi t fun var => do
      let eq? ← proveEq ctx (b.instantiate1 var) (b'.instantiate1 var) isDep (checkTypes := true)
      eq?.mapM fun proof => do
        let u ← getLevel t
        let v ← getLevel (b.instantiate1 var)
        return mkApp4 (.const ``pi_congr [u, v]) t (.lam nm t b bi) (.lam nm' t' b' bi')
          (← mkLambdaFVars #[var] proof)
  -- eta-expansion with lambda on the left
  | .lam nm t b bi, rhs =>
    if checkTypes then
      let .lam _ t' _ _ ← etaExpand1 rhs |
        throwError "Invalid equality goal, the left-hand side is a function but the \
          right-hand side is not:{indentExpr lhs}\nand{indentExpr rhs}"
      discard <| proveEq ctx (recHeadBeta t) (recHeadBeta t') (isDep := true) (checkTypes := true)
    withLocalDecl nm bi t fun var => do
      let eq? ← proveEq ctx (b.instantiate1 var) (rhs.betaRev #[var]) isDep checkTypes
      eq?.mapM fun proof => do
        let u ← getLevel t
        let β ← inferType (b.instantiate1 var)
        let v ← getLevel β
        return mkApp5 (.const ``funext [u, v]) t (← mkLambdaFVars #[var] β) lhs rhs
          (← mkLambdaFVars #[var] proof)
  | .proj ty i s, .proj ty' i' s' =>
    unless ty == ty' && i == i' do
      throwError "Different projections on left-hand side{indentExpr lhs}\nand right-hand side{indentExpr rhs}"
    let eq? ← proveEq ctx s s' isDep (checkTypes := true)
    eq?.mapM fun proof => do
      -- at this point `s` have `s'` have defeq types
      let sType ← inferType s'
      let resType ← inferType rhs
      let sUniv ← getLevel sType
      let resUniv ← getLevel resType
      return mkApp6 (.const ``congrArg [sUniv, resUniv]) sType resType s s'
        (.lam `x sType (.proj ty i (.bvar 0)) .default) proof
  | .letE nm t v b nd, .letE nm' t' v' b' nd' =>
    let u ← getLevel t
    let valueEq? ← if u.isAlwaysZero then pure none else proveEq ctx v v' (isDep || !nd || !nd') (checkTypes := true)
    withLetDecl nm t v fun var => do
      let bodyEq? ← proveEq ctx (b.instantiate1 var) (b'.instantiate1 var) isDep (checkTypes := true)
      match valueEq?, bodyEq? with
      | none, none => return none
      | none, some bproof =>
        let btype ← inferType (b'.instantiate1 var)
        let blvl ← getLevel btype
        return mkApp6 (.const ``have_body_congr_dep' [u, blvl]) t
          (.lam nm t (btype.abstract #[var]) .default) v (.lam nm t b .default)
          (.lam nm' t' b' .default) (.lam nm t (bproof.abstract #[var]) .default)
      | some vproof, none =>
        let btype ← inferType (b'.instantiate1 var)
        let blvl ← getLevel btype
        let β ← mkLetFVars #[var] btype (generalizeNondepLet := false)
        return mkApp6 (.const ``have_val_congr' [u, blvl]) t β
          v v' (.lam nm t b .default) vproof
      | some vproof, some bproof =>
        let btype ← inferType (b'.instantiate1 var)
        let blvl ← getLevel btype
        let β ← mkLetFVars #[var] btype (generalizeNondepLet := false)
        return mkApp8 (.const ``have_congr' [u, blvl]) t β
          v v' (.lam nm t b .default) (.lam nm' t' b' .default) vproof
          (.lam nm t (bproof.abstract #[var]) .default)
  | _, .app _ _ =>
    let lhsFn := lhs.getAppFn'
    let lhsArgs := lhs.getAppArgs'
    let rhsFn := rhs.getAppFn'
    let rhsArgs := rhs.getAppArgs'
    -- There are three cases for application transformations we need to handle:
    -- 1. Congruence: Nothing more happens than just visiting each subexpression
    -- 2. Match transformations: The match gains one argument on the lhs
    -- 3. Recursive applications: The right-hand side is an application of a recursion argument
    if let .const nm us := rhsFn then
      -- Recursive application
      if ctx.recFns.contains nm then
        let (rhsInner, rhsTrans) ← deltaRecDef nm us rhsArgs
        let some (lhsInner, lhsTrans) := peelProjsLike (mkAppN lhsFn lhsArgs) rhsTrans |
          throwError "Different shapes and recursive occurrence:{indentExpr lhs}\nand{indentExpr (rhsTrans.instantiate1 rhsInner)}"
        unless ← isDefEq lhsInner rhsInner do
          throwError "Failed to prove equality at recursive occurrence:{indentExpr lhsInner}\nand{indentExpr rhsInner}"
        -- Since we showed defeq we can now use `lhsInner` for both sides
        let newLhs := lhsTrans.instantiate1 lhsInner
        let newRhs := rhsTrans.instantiate1 lhsInner
        return ← proveEq ctx newLhs newRhs isDep checkTypes
    if h : lhsArgs.size = rhsArgs.size then
      -- Congruence
      let arity := rhsArgs.size
      discard <| proveEq ctx lhsFn rhsFn (isDep := false) (checkTypes := true)
      let mut ty ← inferType rhsFn
      let mut vars : Array Expr := #[]
      let mut proof? : Option Expr := none
      let mut lhsFn := lhsFn
      let mut rhsFn := rhsFn
      for h : i in 0...arity do
        have : i < arity := h.2
        let lhs := lhsArgs[i]
        let rhs := rhsArgs[i]
        let .forallE nm t b bi ← whnf ty | throwFunctionExpected (rhsFn.app rhs)
        let t := t.instantiateRev vars
        let u ← getLevel t
        let argEq? ← if u.isAlwaysZero then pure none else
          proveEq ctx lhs rhs (isDep || b.hasLooseBVars) (checkTypes := false)
        proof? ← match proof?, argEq? with
          | none, none => pure none
          | none, some aproof =>
            let v ← getLevel b
            pure (mkApp6 (.const ``congrArg [u, v]) t b lhs rhs rhsFn aproof)
          | some fproof, none =>
            if b.hasLooseBVars then
              let v ← getLevel (b.instantiate1 rhs)
              pure (mkApp6 (.const ``congrFun [u, v]) t (.lam nm t b bi) lhsFn rhsFn fproof rhs)
            else
              let v ← getLevel b
              pure (mkApp6 (.const ``congrFun' [u, v]) t b lhsFn rhsFn fproof rhs)
          | some fproof, some aproof =>
            let v ← getLevel b
            pure (mkApp8 (.const ``congr [u, v]) t b lhsFn rhsFn lhs rhs fproof aproof)
        vars := vars.push rhs
        ty := b.instantiate1 rhs
        lhsFn := lhsFn.app lhs
        rhsFn := rhsFn.app rhs
      return proof?
    else
      -- Match transformation
      let fail {α} (s : MessageData) : MetaM α := do
        throwError "Failed to prove equality of unrelated applications; {s} at{indentExpr lhs}\nand{indentExpr rhs}"
      let .const matcherName matcherLvls := lhsFn | fail "expected constant application"
      let some info ← Match.getPseudoMatcherInfo? matcherName | fail "expected matcher"
      if isDep then fail "cannot rewrite matcher in dependent position"
      if lhsArgs.size ≤ info.arity then fail m!"insufficient arity for {lhsFn}"
      let some elimPos := info.uElimPos? |
        return none -- proof
      let some lifter ← Match.getLifterFor? matcherName | fail "could not derive lifter"
      let params := lhsArgs.take info.numParams
      let motive := lhsArgs[info.numParams]!
      let addArg := lhsArgs[info.arity]!
      let .proj _ 1 thing := addArg | fail "expected additional argument to be projection"
      unless thing.getAppFn == ctx.belowVar do fail m!"expected function `{ctx.belowVar}` in additional argument"
      let (rhsLvl, motive', fn) ← lambdaTelescope motive fun discrs body => do
        unless discrs.size = info.numDiscrs do fail m!"motive does not take all {info.numDiscrs} arguments"
        let .forallE _ d b _ := body | fail "expected implication in motive"
        if b.hasLooseBVars then fail "expected implication in motive"
        let motive' ← mkLambdaFVars discrs b
        let belowArgs := d.getAppArgsN ctx.numMajors
        let brecApp := mkAppN (mkAppN ctx.belowVar belowArgs) ctx.alts
        let brecApp : Expr := .proj ``PProd 1 brecApp
        let fn := .lam `g body (.app (.bvar 0) brecApp) .default
        return (← getLevel b, motive', ← mkLambdaFVars discrs fn)
      let lifterLvls := rhsLvl :: matcherLvls
      let discrs := lhsArgs[info.getFirstDiscrPos...info.getFirstAltPos].toArray
      let alts := lhsArgs[info.getFirstAltPos...info.arity].toArray
      let overargs := lhsArgs[(info.arity+1)...*].toArray
      let lifterApp := mkApp3 (mkAppN (.const lifter lifterLvls) params) motive motive' fn
      let lifterApp := mkAppN (mkAppN lifterApp discrs) alts
      let some (_, _, mid) := (← inferType lifterApp).eq? | unreachable!
      let mut newAlts := #[]
      let discrEqs := info.getNumDiscrEqs
      let midAlts := mid.getAppArgsN info.numAlts
      for alt in midAlts, altInfo in info.altInfos do
        let numParams := altInfo.numFields + discrEqs + altInfo.hasUnitThunk.toNat
        newAlts := newAlts.push <| ← lambdaBoundedTelescope alt numParams fun params body => do
          mkLambdaFVars params body.headBeta
      let resType ← inferType lhs
      let resLvl ← getLevel resType
      let mid := mkAppN (mid.getBoundedAppFn info.numAlts) newAlts
      let eqProof := mkApp6 (.const ``congrArg [rhsLvl, resLvl])
        (mkAppN motive' discrs) resType (mkAppN lhsFn lhsArgs[0...(info.arity+1)].toArray) mid
        (.lam `g (mkAppN motive' discrs) (mkAppN (.bvar 0) overargs) .default) lifterApp
      let mid := mkAppN mid overargs
      let otherEq? ← proveEq ctx mid rhs (isDep := false) checkTypes
      match otherEq? with
      | none => return eqProof
      | some otherProof =>
        return mkApp6 (.const ``Eq.trans [resLvl]) resType lhs mid rhs eqProof otherProof
  | _, _ =>
    throwError "Failed to prove equality due to unknown pattern of{indentExpr lhs}\nand{indentExpr rhs}"

def mkProofFor (declName thmName : Name) (value : Expr) (recFns : NameSet) : MetaM Unit := do
  let defnInfo ← getConstInfoDefn declName
  lambdaTelescope value fun vars body => do
    let lparams := defnInfo.levelParams.map Level.param
    let constApp := mkAppN (.const declName lparams) vars
    let resType ← inferType constApp
    let resLvl ← getLevel resType
    let deltaValue := defnInfo.value.beta vars
    let (brecApp, projs) := peelProjs deltaValue
    let .const brecName brecLvls@(elimLvl :: inductLevels) := brecApp.getAppFn |
      throwError "Unexpected value for recursive definition, expected application of `brecOn`:{indentExpr brecApp}"
    unless isBRecOnRecursor (← getEnv) brecName do
      throwError "Unexpected value for recursive definition, expected application of `brecOn`:{indentExpr brecApp}"
    -- some inductive out of the mutual group, we only need it for `numParams` and `numTypeFormers`
    let indName := brecName.getPrefix
    let indInfo ← getConstInfoInduct indName
    unless indInfo.levelParams.length = inductLevels.length do
      throwError "Unexpected value for recursive definition, `{.ofConstName brecName}` does not eliminate into any universe"
    if elimLvl.isAlwaysZero then
      throwError "Can't derive an equation for a proof"
    let numParams := indInfo.numParams
    let numMotives := indInfo.numTypeFormers
    let (motiveIdx, numMajors) ← brecOnMotiveIdxAndNumMajors brecName numParams numMotives
    let fstMotiveIdx := numParams
    let fstMajorIdx := fstMotiveIdx + numMotives
    let fstAltIdx := fstMajorIdx + numMajors
    let arity := fstAltIdx + numMotives
    let (brecApp, transformations) := updateTransformationsWithOverargs brecApp projs arity
    let args := brecApp.getAppArgs
    unless args.size = arity do
      throwError "Unexpected value for recursive definition, insufficient arguments for `brecOn`:{indentExpr deltaValue}"
    let inductParams := args[0...fstMotiveIdx].toArray
    let motives := args[fstMotiveIdx...fstMajorIdx].toArray
    let majors := args[fstMajorIdx...fstAltIdx].toArray
    let alts := args[fstAltIdx...arity].toArray
    let goName := brecName.str "go"
    let eqName := brecName.str "eq"
    let generalGoApp := mkAppN (mkAppN (.const goName brecLvls) inductParams) motives
    let ourMotive := motives[motiveIdx]!
    let ourAlt := alts[motiveIdx]!
    withLetDecl `f (← inferType generalGoApp) generalGoApp fun belowFn => do
    let goApp := mkAppN (mkAppN belowFn majors) alts
    let eqApp := mkAppN (.const eqName brecLvls) args[0...arity].toArray
    let afterEq := (mkAppN ourAlt majors).app (.proj ``PProd 1 goApp)
    let res := reduceProjs <| transformations.instantiate1 afterEq
    let eqApp := mkApp6 (.const ``congrArg [elimLvl, resLvl])
      (mkAppN ourMotive majors) resType brecApp afterEq
      (.lam `g (mkAppN ourMotive majors) transformations .default) eqApp
    let .const functional functionalLvls := res.getAppFn |
      throwError "Unexpected value for recursive definition, expected functional constant application:{indentExpr res}"
    let resArgs := res.getAppArgs
    let defnInfo ← getConstInfo functional
    let delta ← instantiateValueLevelParams defnInfo functionalLvls
    let delta ← letToHave delta
    let delta := delta.beta resArgs
    let ctx := {
      belowVar := belowFn
      numInductParams := numParams
      numMajors, alts, recFns
    }
    let rproof? ← proveEq ctx delta body (isDep := false) (checkTypes := false)
    let rproof := rproof?.getD (mkApp2 (.const ``rfl [resLvl]) resType delta)
    let proof := mkApp6 (.const ``Eq.trans [resLvl]) resType deltaValue delta body eqApp rproof
    let proof := proof.replaceFVar belowFn generalGoApp
    let type := mkApp3 (.const ``Eq [resLvl]) resType constApp body
    addDecl <| .thmDecl {
      name := thmName
      levelParams := defnInfo.levelParams
      type := ← mkForallFVars vars type
      value := ← mkLambdaFVars vars proof
    }

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s =>
    let all := s.toArray
    -- Do not export for non-exposed defs at exported/server levels
    let exported := s.filter (fun n _ => env.hasExposedBody n) |>.toArray
    { exported, server := exported, «private» := all })

public def registerEqnsInfo (preDef : PreDefinition) (declNames : Array Name) (recArgPos : Nat)
    (fixedParamPerms : FixedParamPerms) : CoreM Unit := do
  ensureEqnReservedNamesAvailable preDef.declName
  modifyEnv fun env => eqnInfoExt.insert env preDef.declName
    { preDef with recArgPos, declNames, fixedParamPerms }

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := do
  let name := mkEqLikeNameFor (← getEnv) info.declName unfoldThmSuffix
  realizeConst info.declNames[0]! name (withEqnOptions declName (doRealize name))
  return name
where
  doRealize name :=
    withoutExporting do
      prependError m!"failed to generate equational theorem for `{.ofConstName declName}`" do
        mkProofFor declName name (← letToHave info.value) (.ofArray info.declNames)

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    return some (← mkUnfoldEq declName info)
  else
    return none

set_option compiler.ignoreBorrowAnnotation true in
@[export lean_get_structural_rec_arg_pos]
def getStructuralRecArgPosImp? (declName : Name) : CoreM (Option Nat) := do
  let some info := eqnInfoExt.find? (← getEnv) declName | return none
  return some info.recArgPos


builtin_initialize
  registerGetUnfoldEqnFn getUnfoldFor?
  registerTraceClass `Elab.definition.structural.eqns

end Structural
end Lean.Elab
