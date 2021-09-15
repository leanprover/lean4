/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Injection
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Subst

namespace Lean.Meta

private def throwInductiveTypeExpected (type : Expr) : MetaM α := do
  throwError "failed to compile pattern matching, inductive type expected{indentExpr type}"

def getInductiveUniverseAndParams (type : Expr) : MetaM (List Level × Array Expr) := do
  let type ← whnfD type
  matchConstInduct type.getAppFn (fun _ => throwInductiveTypeExpected type) fun val us =>
    let I      := type.getAppFn
    let Iargs  := type.getAppArgs
    let params := Iargs.extract 0 val.numParams
    pure (us, params)

private def mkEqAndProof (lhs rhs : Expr) : MetaM (Expr × Expr) := do
  let lhsType ← inferType lhs
  let rhsType ← inferType rhs
  let u       ← getLevel lhsType
  if (← isDefEq lhsType rhsType) then
    pure (mkApp3 (mkConst `Eq [u]) lhsType lhs rhs, mkApp2 (mkConst `Eq.refl [u]) lhsType lhs)
  else
    pure (mkApp4 (mkConst `HEq [u]) lhsType lhs rhsType rhs, mkApp2 (mkConst `HEq.refl [u]) lhsType lhs)

private partial def withNewEqs (targets targetsNew : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  let rec loop (i : Nat) (newEqs : Array Expr) (newRefls : Array Expr) := do
    if h : i < targets.size then
      let (newEqType, newRefl) ← mkEqAndProof targets[i] targetsNew[i]
      withLocalDeclD `h newEqType fun newEq => do
        loop (i+1) (newEqs.push newEq) (newRefls.push newRefl)
    else
      k newEqs newRefls
  loop 0 #[] #[]

def generalizeTargetsEq (mvarId : MVarId) (motiveType : Expr) (targets : Array Expr) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `generalizeTargets
    let (typeNew, eqRefls) ←
      forallTelescopeReducing motiveType fun targetsNew _ => do
        unless targetsNew.size == targets.size do
          throwError "invalid number of targets #{targets.size}, motive expects #{targetsNew.size}"
        withNewEqs targets targetsNew fun eqs eqRefls => do
          let type    ← getMVarType mvarId
          let typeNew ← mkForallFVars eqs type
          let typeNew ← mkForallFVars targetsNew typeNew
          pure (typeNew, eqRefls)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew (← getMVarTag mvarId)
    assignExprMVar mvarId (mkAppN (mkAppN mvarNew targets) eqRefls)
    pure mvarNew.mvarId!

structure GeneralizeIndicesSubgoal where
  mvarId         : MVarId
  indicesFVarIds : Array FVarId
  fvarId         : FVarId
  numEqs         : Nat

/--
  Similar to `generalizeTargets` but customized for the `casesOn` motive.
  Given a metavariable `mvarId` representing the
  ```
  Ctx, h : I A j, D |- T
  ```
  where `fvarId` is `h`s id, and the type `I A j` is an inductive datatype where `A` are parameters,
  and `j` the indices. Generate the goal
  ```
  Ctx, h : I A j, D, j' : J, h' : I A j' |- j == j' -> h == h' -> T
  ```
  Remark: `(j == j' -> h == h')` is a "telescopic" equality.
  Remark: `j` is sequence of terms, and `j'` a sequence of free variables.
  The result contains the fields
  - `mvarId`: the new goal
  - `indicesFVarIds`: `j'` ids
  - `fvarId`: `h'` id
  - `numEqs`: number of equations in the target -/
def generalizeIndices (mvarId : MVarId) (fvarId : FVarId) : MetaM GeneralizeIndicesSubgoal :=
  withMVarContext mvarId do
    let lctx       ← getLCtx
    let localInsts ← getLocalInstances
    checkNotAssigned mvarId `generalizeIndices
    let fvarDecl ← getLocalDecl fvarId
    let type ← whnf fvarDecl.type
    type.withApp fun f args => matchConstInduct f (fun _ => throwTacticEx `generalizeIndices mvarId "inductive type expected") fun val _ => do
      unless val.numIndices > 0 do throwTacticEx `generalizeIndices mvarId "indexed inductive type expected"
      unless args.size == val.numIndices + val.numParams do throwTacticEx `generalizeIndices mvarId "ill-formed inductive datatype"
      let indices := args.extract (args.size - val.numIndices) args.size
      let IA := mkAppN f (args.extract 0 val.numParams) -- `I A`
      let IAType ← inferType IA
      forallTelescopeReducing IAType fun newIndices _ => do
      let newType := mkAppN IA newIndices
      withLocalDeclD fvarDecl.userName newType fun h' =>
      withNewEqs indices newIndices fun newEqs newRefls => do
      let (newEqType, newRefl) ← mkEqAndProof fvarDecl.toExpr h'
      let newRefls := newRefls.push newRefl
      withLocalDeclD `h newEqType fun newEq => do
      let newEqs := newEqs.push newEq
      /- auxType `forall (j' : J) (h' : I A j'), j == j' -> h == h' -> target -/
      let target  ← getMVarType mvarId
      let tag     ← getMVarTag mvarId
      let auxType ← mkForallFVars newEqs target
      let auxType ← mkForallFVars #[h'] auxType
      let auxType ← mkForallFVars newIndices auxType
      let newMVar ← mkFreshExprMVarAt lctx localInsts auxType MetavarKind.syntheticOpaque tag
      /- assign mvarId := newMVar indices h refls -/
      assignExprMVar mvarId (mkAppN (mkApp (mkAppN newMVar indices) fvarDecl.toExpr) newRefls)
      let (indicesFVarIds, newMVarId) ← introNP newMVar.mvarId! newIndices.size
      let (fvarId, newMVarId) ← intro1P newMVarId
      pure {
        mvarId         := newMVarId,
        indicesFVarIds := indicesFVarIds,
        fvarId         := fvarId,
        numEqs         := newEqs.size
      }

structure CasesSubgoal extends InductionSubgoal where
  ctorName : Name

namespace Cases

structure Context where
  inductiveVal     : InductiveVal
  casesOnVal       : DefinitionVal
  nminors          : Nat := inductiveVal.ctors.length
  majorDecl        : LocalDecl
  majorTypeFn      : Expr
  majorTypeArgs    : Array Expr
  majorTypeIndices : Array Expr := majorTypeArgs.extract (majorTypeArgs.size - inductiveVal.numIndices) majorTypeArgs.size

private def mkCasesContext? (majorFVarId : FVarId) : MetaM (Option Context) := do
  let env ← getEnv
  if !env.contains `Eq || !env.contains `HEq then
    pure none
  else
    let majorDecl ← getLocalDecl majorFVarId
    let majorType ← whnf majorDecl.type
    majorType.withApp fun f args => matchConstInduct f (fun _ => pure none) fun ival _ =>
      if args.size != ival.numIndices + ival.numParams then pure none
      else match env.find? (Name.mkStr ival.name "casesOn") with
        | ConstantInfo.defnInfo cval =>
          return some {
            inductiveVal  := ival,
            casesOnVal    := cval,
            majorDecl     := majorDecl,
            majorTypeFn   := f,
            majorTypeArgs := args
          }
        | _ => pure none

/-
We say the major premise has independent indices IF
1- its type is *not* an indexed inductive family, OR
2- its type is an indexed inductive family, but all indices are distinct free variables, and
   all local declarations different from the major and its indices do not depend on the indices.
-/
private def hasIndepIndices (ctx : Context) : MetaM Bool := do
  if ctx.majorTypeIndices.isEmpty then
    pure true
  else if ctx.majorTypeIndices.any $ fun idx => !idx.isFVar then
    /- One of the indices is not a free variable. -/
    pure false
  else if ctx.majorTypeIndices.size.any fun i => i.any fun j => ctx.majorTypeIndices[i] == ctx.majorTypeIndices[j] then
    /- An index ocurrs more than once -/
    pure false
  else
    let lctx ← getLCtx
    let mctx ← getMCtx
    return lctx.all fun decl =>
      decl.fvarId == ctx.majorDecl.fvarId || -- decl is the major
      ctx.majorTypeIndices.any (fun index => decl.fvarId == index.fvarId!) || -- decl is one of the indices
      mctx.findLocalDeclDependsOn decl (fun fvarId => ctx.majorTypeIndices.all $ fun idx => idx.fvarId! != fvarId) -- or does not depend on any index

private def elimAuxIndices (s₁ : GeneralizeIndicesSubgoal) (s₂ : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  let indicesFVarIds := s₁.indicesFVarIds
  s₂.mapM fun s => do
    indicesFVarIds.foldlM (init := s) fun s indexFVarId =>
      match s.subst.get indexFVarId with
      | Expr.fvar indexFVarId' _ =>
        (do let mvarId ← clear s.mvarId indexFVarId'; pure { s with mvarId := mvarId, subst := s.subst.erase indexFVarId })
        <|>
        (pure s)
      | _ => pure s

/-
  Convert `s` into an array of `CasesSubgoal`, by attaching the corresponding constructor name,
  and adding the substitution `majorFVarId -> ctor_i us params fields` into each subgoal. -/
private def toCasesSubgoals (s : Array InductionSubgoal) (ctorNames : Array Name) (majorFVarId : FVarId) (us : List Level) (params : Array Expr)
    : Array CasesSubgoal :=
  s.mapIdx fun i s =>
    let ctorName := ctorNames[i]
    let ctorApp  := mkAppN (mkAppN (mkConst ctorName us) params) s.fields
    let s        := { s with subst := s.subst.insert majorFVarId ctorApp }
    { ctorName           := ctorName,
      toInductionSubgoal := s }

/- Convert heterogeneous equality into a homegeneous one -/
private def heqToEq (mvarId : MVarId) (eqDecl : LocalDecl) : MetaM MVarId := do
  /- Convert heterogeneous equality into a homegeneous one -/
  let prf    ← mkEqOfHEq (mkFVar eqDecl.fvarId)
  let aEqb   ← whnf (← inferType prf)
  let mvarId ← assert mvarId eqDecl.userName aEqb prf
  clear mvarId eqDecl.fvarId

partial def unifyEqs (numEqs : Nat) (mvarId : MVarId) (subst : FVarSubst) (caseName? : Option Name := none): MetaM (Option (MVarId × FVarSubst)) := do
  if numEqs == 0 then
    pure (some (mvarId, subst))
  else
    let (eqFVarId, mvarId) ← intro1 mvarId
    withMVarContext mvarId do
      let eqDecl ← getLocalDecl eqFVarId
      if eqDecl.type.isHEq then
        let mvarId ← heqToEq mvarId eqDecl
        unifyEqs numEqs mvarId subst caseName?
      else match eqDecl.type.eq? with
        | none => throwError "equality expected{indentExpr eqDecl.type}"
        | some (α, a, b) =>
          /-
            Remark: we do not check `isDefeq` here because we would fail to substitute equalities
            such as `x = t` and `t = x` when `x` and `t` are proofs (proof irrelanvance).
          -/
          /- Remark: we use `let rec` here because otherwise the compiler would generate an insane amount of code.
            We can remove the `rec` after we fix the eagerly inlining issue in the compiler. -/
          let rec substEq (symm : Bool) := do
            /- TODO: support for acyclicity (e.g., `xs ≠ x :: xs`) -/
            /- Remark: `substCore` fails if the equation is of the form `x = x` -/
            if let some (substNew, mvarId) ← observing? (substCore mvarId eqFVarId symm subst) then
              unifyEqs (numEqs - 1) mvarId substNew caseName?
            else if (← isDefEq a b) then
              /- Skip equality -/
              unifyEqs (numEqs - 1) (← clear mvarId eqFVarId) subst caseName?
            else
              throwError "dependent elimination failed, failed to solve equation{indentExpr eqDecl.type}"
          let rec injection (a b : Expr) := do
            let env ← getEnv
            if a.isConstructorApp env && b.isConstructorApp env then
              /- ctor_i ... = ctor_j ... -/
              match (← injectionCore mvarId eqFVarId) with
              | InjectionResultCore.solved                   => pure none -- this alternative has been solved
              | InjectionResultCore.subgoal mvarId numEqsNew => unifyEqs (numEqs - 1 + numEqsNew) mvarId subst caseName?
            else
              let a' ← whnf a
              let b' ← whnf b
              if a' != a || b' != b then
                /- Reduced lhs/rhs of current equality -/
                let prf := mkFVar eqFVarId
                let aEqb'  ← mkEq a' b'
                let mvarId ← assert mvarId eqDecl.userName aEqb' prf
                let mvarId ← clear mvarId eqFVarId
                unifyEqs numEqs mvarId subst caseName?
              else
                match caseName? with
                | none => throwError "dependent elimination failed, failed to solve equation{indentExpr eqDecl.type}"
                | some caseName => throwError "dependent elimination failed, failed to solve equation{indentExpr eqDecl.type}\nat case {mkConst caseName}"
          let a ← instantiateMVars a
          let b ← instantiateMVars b
          match a, b with
          | Expr.fvar aFVarId _, Expr.fvar bFVarId _ =>
            /- x = y -/
            let aDecl ← getLocalDecl aFVarId
            let bDecl ← getLocalDecl bFVarId
            substEq (aDecl.index < bDecl.index)
          | Expr.fvar .., _   => /- x = t -/ substEq (symm := false)
          | _, Expr.fvar ..   => /- t = x -/ substEq (symm := true)
          | a, b              =>
            if (← isDefEq a b) then
              /- Skip equality -/
              unifyEqs (numEqs - 1) (← clear mvarId eqFVarId) subst caseName?
            else
              injection a b

private def unifyCasesEqs (numEqs : Nat) (subgoals : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  subgoals.foldlM (init := #[]) fun subgoals s => do
    match (← unifyEqs numEqs s.mvarId s.subst s.ctorName) with
    | none                 => pure subgoals
    | some (mvarId, subst) =>
      return subgoals.push { s with
        mvarId := mvarId,
        subst  := subst,
        fields := s.fields.map (subst.apply ·)
      }

private def inductionCasesOn (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames) (ctx : Context)
    : MetaM (Array CasesSubgoal) := do
  withMVarContext mvarId do
  let majorType ← inferType (mkFVar majorFVarId)
  let (us, params) ← getInductiveUniverseAndParams majorType
  let casesOn := mkCasesOnName ctx.inductiveVal.name
  let ctors   := ctx.inductiveVal.ctors.toArray
  let s ← induction mvarId majorFVarId casesOn givenNames
  return toCasesSubgoals s ctors majorFVarId us params

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames := #[]) : MetaM (Array CasesSubgoal) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `cases
    let context? ← mkCasesContext? majorFVarId
    match context? with
    | none     => throwTacticEx `cases mvarId "not applicable to the given hypothesis"
    | some ctx =>
      /- Remark: if caller does not need a `FVarSubst` (variable substitution), and `hasIndepIndices ctx` is true,
         then we can also use the simple case. This is a minor optimization, and we currently do not even
         allow callers to specify whether they want the `FVarSubst` or not. -/
      if ctx.inductiveVal.numIndices == 0 then
        -- Simple case
        inductionCasesOn mvarId majorFVarId givenNames ctx
      else
        let s₁ ← generalizeIndices mvarId majorFVarId
        trace[Meta.Tactic.cases] "after generalizeIndices\n{MessageData.ofGoal s₁.mvarId}"
        let s₂ ← inductionCasesOn s₁.mvarId s₁.fvarId givenNames ctx
        let s₂ ← elimAuxIndices s₁ s₂
        unifyCasesEqs s₁.numEqs s₂

end Cases

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames := #[]) : MetaM (Array CasesSubgoal) :=
  Cases.cases mvarId majorFVarId givenNames

def casesRec (mvarId : MVarId) (p : LocalDecl → MetaM Bool) : MetaM (List MVarId) :=
  saturate mvarId fun mvarId =>
    withMVarContext mvarId do
      for localDecl in (← getLCtx) do
        if (← p localDecl) then
          let r? ← observing? do
            let r ← cases mvarId localDecl.fvarId
            return r.toList.map (·.mvarId)
          if r?.isSome then
            return r?
      return none

def casesAnd (mvarId : MVarId) : MetaM MVarId := do
  let mvarIds ← casesRec mvarId fun localDecl => return (← instantiateMVars localDecl.type).isAppOfArity ``And 2
  exactlyOne mvarIds

def substEqs (mvarId : MVarId) : MetaM MVarId := do
  let mvarIds ← casesRec mvarId fun localDecl => do
    let type ← instantiateMVars localDecl.type
    return type.isEq || type.isHEq
  exactlyOne mvarIds

structure ByCasesSubgoal where
  mvarId : MVarId
  fvarId : FVarId

def byCases (mvarId : MVarId) (p : Expr) (hName : Name := `h) : MetaM (ByCasesSubgoal × ByCasesSubgoal) := do
  let mvarId ← assert mvarId `hByCases (mkOr p (mkNot p)) (mkEM p)
  let (fvarId, mvarId) ← intro1 mvarId
  let #[s₁, s₂] ← cases mvarId fvarId #[{ varNames := [hName] }, { varNames := [hName] }] |
    throwError "'byCases' tactic failed, unexpected number of subgoals"
  return ((← toByCasesSubgoal s₁), (← toByCasesSubgoal s₂))
where
  toByCasesSubgoal (s : CasesSubgoal) : MetaM ByCasesSubgoal :=  do
    let #[Expr.fvar fvarId ..] ← pure s.fields | throwError "'byCases' tactic failed, unexpected new hypothesis"
    return { mvarId := s.mvarId, fvarId }

builtin_initialize registerTraceClass `Meta.Tactic.cases

end Lean.Meta
