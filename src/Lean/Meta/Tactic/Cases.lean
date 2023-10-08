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
import Lean.Meta.Tactic.Acyclic
import Lean.Meta.Tactic.UnifyEq

namespace Lean.Meta

private def throwInductiveTypeExpected (type : Expr) : MetaM α := do
  throwError "failed to compile pattern matching, inductive type expected{indentExpr type}"

def getInductiveUniverseAndParams (type : Expr) : MetaM (List Level × Array Expr) := do
  let type ← whnfD type
  matchConstInduct type.getAppFn (fun _ => throwInductiveTypeExpected type) fun val us =>
    let Iargs  := type.getAppArgs
    let params := Iargs.extract 0 val.numParams
    pure (us, params)

private def mkEqAndProof (lhs rhs : Expr) : MetaM (Expr × Expr) := do
  let lhsType ← inferType lhs
  let rhsType ← inferType rhs
  let u       ← getLevel lhsType
  if (← isDefEq lhsType rhsType) then
    pure (mkApp3 (mkConst ``Eq [u]) lhsType lhs rhs, mkApp2 (mkConst ``Eq.refl [u]) lhsType lhs)
  else
    pure (mkApp4 (mkConst ``HEq [u]) lhsType lhs rhsType rhs, mkApp2 (mkConst ``HEq.refl [u]) lhsType lhs)

private partial def withNewEqs (targets targetsNew : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  let rec loop (i : Nat) (newEqs : Array Expr) (newRefls : Array Expr) := do
    if i < targets.size then
      let (newEqType, newRefl) ← mkEqAndProof targets[i]! targetsNew[i]!
      withLocalDeclD `h newEqType fun newEq => do
        loop (i+1) (newEqs.push newEq) (newRefls.push newRefl)
    else
      k newEqs newRefls
  loop 0 #[] #[]

def generalizeTargetsEq (mvarId : MVarId) (motiveType : Expr) (targets : Array Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `generalizeTargets
    let (typeNew, eqRefls) ←
      forallTelescopeReducing motiveType fun targetsNew _ => do
        unless targetsNew.size == targets.size do
          throwError "invalid number of targets #{targets.size}, motive expects #{targetsNew.size}"
        withNewEqs targets targetsNew fun eqs eqRefls => do
          let type    ← mvarId.getType
          let typeNew ← mkForallFVars eqs type
          let typeNew ← mkForallFVars targetsNew typeNew
          pure (typeNew, eqRefls)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew (← mvarId.getTag)
    mvarId.assign (mkAppN (mkAppN mvarNew targets) eqRefls)
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
  mvarId.withContext do
    let lctx       ← getLCtx
    let localInsts ← getLocalInstances
    mvarId.checkNotAssigned `generalizeIndices
    let fvarDecl ← fvarId.getDecl
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
      let target  ← mvarId.getType
      let tag     ← mvarId.getTag
      let auxType ← mkForallFVars newEqs target
      let auxType ← mkForallFVars #[h'] auxType
      let auxType ← mkForallFVars newIndices auxType
      let newMVar ← mkFreshExprMVarAt lctx localInsts auxType MetavarKind.syntheticOpaque tag
      /- assign mvarId := newMVar indices h refls -/
      mvarId.assign (mkAppN (mkApp (mkAppN newMVar indices) fvarDecl.toExpr) newRefls)
      let (indicesFVarIds, newMVarId) ← newMVar.mvarId!.introNP newIndices.size
      let (fvarId, newMVarId) ← newMVarId.intro1P
      return {
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
    let majorDecl ← majorFVarId.getDecl
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

/--
We say the major premise has independent indices IF
1- its type is *not* an indexed inductive family, OR
2- its type is an indexed inductive family, but all indices are distinct free variables, and
   all local declarations different from the major and its indices do not depend on the indices.
-/
private def hasIndepIndices (ctx : Context) : MetaM Bool := do
  if ctx.majorTypeIndices.isEmpty then
    return true
  else if ctx.majorTypeIndices.any fun idx => !idx.isFVar then
    /- One of the indices is not a free variable. -/
    return false
  else if ctx.majorTypeIndices.size.any fun i => i.any fun j => ctx.majorTypeIndices[i]! == ctx.majorTypeIndices[j]! then
    /- An index occurs more than once -/
    return false
  else
    (← getLCtx).allM fun decl =>
      pure (decl.fvarId == ctx.majorDecl.fvarId) <||> -- decl is the major
      pure (ctx.majorTypeIndices.any (fun index => decl.fvarId == index.fvarId!)) <||> -- decl is one of the indices
     findLocalDeclDependsOn decl (fun fvarId => ctx.majorTypeIndices.all fun idx => idx.fvarId! != fvarId) -- or does not depend on any index

private def elimAuxIndices (s₁ : GeneralizeIndicesSubgoal) (s₂ : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  let indicesFVarIds := s₁.indicesFVarIds
  s₂.mapM fun s => do
    indicesFVarIds.foldlM (init := s) fun s indexFVarId =>
      match s.subst.get indexFVarId with
      | Expr.fvar indexFVarId' =>
        (do let mvarId ← s.mvarId.clear indexFVarId'; pure { s with mvarId := mvarId, subst := s.subst.erase indexFVarId })
        <|>
        (pure s)
      | _ => pure s

/--
  Convert `s` into an array of `CasesSubgoal`, by attaching the corresponding constructor name,
  and adding the substitution `majorFVarId -> ctor_i us params fields` into each subgoal. -/
private def toCasesSubgoals (s : Array InductionSubgoal) (ctorNames : Array Name) (majorFVarId : FVarId) (us : List Level) (params : Array Expr)
    : Array CasesSubgoal :=
  s.mapIdx fun i s =>
    let ctorName := ctorNames[i]!
    let ctorApp  := mkAppN (mkAppN (mkConst ctorName us) params) s.fields
    let s        := { s with subst := s.subst.insert majorFVarId ctorApp }
    { ctorName           := ctorName,
      toInductionSubgoal := s }

partial def unifyEqs? (numEqs : Nat) (mvarId : MVarId) (subst : FVarSubst) (caseName? : Option Name := none): MetaM (Option (MVarId × FVarSubst)) := do
  if numEqs == 0 then
    return some (mvarId, subst)
  else
    let (eqFVarId, mvarId) ← mvarId.intro1
    if let some { mvarId, subst, numNewEqs } ← unifyEq? mvarId eqFVarId subst MVarId.acyclic caseName? then
      unifyEqs? (numEqs - 1 + numNewEqs) mvarId subst caseName?
    else
      return none

private def unifyCasesEqs (numEqs : Nat) (subgoals : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  subgoals.foldlM (init := #[]) fun subgoals s => do
    match (← unifyEqs? numEqs s.mvarId s.subst s.ctorName) with
    | none                 => pure subgoals
    | some (mvarId, subst) =>
      return subgoals.push { s with
        mvarId := mvarId,
        subst  := subst,
        fields := s.fields.map (subst.apply ·)
      }

private def inductionCasesOn (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames) (ctx : Context)
    : MetaM (Array CasesSubgoal) := mvarId.withContext do
  let majorType ← inferType (mkFVar majorFVarId)
  let (us, params) ← getInductiveUniverseAndParams majorType
  let casesOn := mkCasesOnName ctx.inductiveVal.name
  let ctors   := ctx.inductiveVal.ctors.toArray
  let s ← mvarId.induction majorFVarId casesOn givenNames
  return toCasesSubgoals s ctors majorFVarId us params

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames := #[]) : MetaM (Array CasesSubgoal) := do
  try
    mvarId.withContext do
      mvarId.checkNotAssigned `cases
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
  catch ex =>
    throwNestedTacticEx `cases ex

end Cases

/--
Apply `casesOn` using the free variable `majorFVarId` as the major premise (aka discriminant).
`givenNames` contains user-facing names for each alternative.
-/
def _root_.Lean.MVarId.cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames := #[]) : MetaM (Array CasesSubgoal) :=
  Cases.cases mvarId majorFVarId givenNames

@[deprecated MVarId.cases]
def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array AltVarNames := #[]) : MetaM (Array CasesSubgoal) :=
  Cases.cases mvarId majorFVarId givenNames

/--
Keep applying `cases` on any hypothesis that satisfies `p`.
-/
def _root_.Lean.MVarId.casesRec (mvarId : MVarId) (p : LocalDecl → MetaM Bool) : MetaM (List MVarId) :=
  saturate mvarId fun mvarId =>
    mvarId.withContext do
      for localDecl in (← getLCtx) do
        if (← p localDecl) then
          let r? ← observing? do
            let r ← mvarId.cases localDecl.fvarId
            return r.toList.map (·.mvarId)
          if r?.isSome then
            return r?
      return none

/--
Applies `cases` (recursively) to any hypothesis of the form `h : p ∧ q`.
-/
def _root_.Lean.MVarId.casesAnd (mvarId : MVarId) : MetaM MVarId := do
  let mvarIds ← mvarId.casesRec fun localDecl => return (← instantiateMVars localDecl.type).isAppOfArity ``And 2
  exactlyOne mvarIds

/--
Applies `cases` to any hypothesis of the form `h : r = s`.
-/
def _root_.Lean.MVarId.substEqs (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarIds ← mvarId.casesRec fun localDecl => do
    let type ← instantiateMVars localDecl.type
    return type.isEq || type.isHEq
  ensureAtMostOne mvarIds

/-- Auxiliary structure for storing `byCases` tactic result. -/
structure ByCasesSubgoal where
  mvarId : MVarId
  fvarId : FVarId

private def toByCasesSubgoal (s : CasesSubgoal) : MetaM ByCasesSubgoal :=  do
    let #[Expr.fvar fvarId ..] ← pure s.fields | throwError "'byCases' tactic failed, unexpected new hypothesis"
    return { mvarId := s.mvarId, fvarId }

/--
Split the goal in two subgoals: one containing the hypothesis `h : p` and another containing `h : ¬ p`.
-/
def _root_.Lean.MVarId.byCases (mvarId : MVarId) (p : Expr) (hName : Name := `h) : MetaM (ByCasesSubgoal × ByCasesSubgoal) := do
  let mvarId ← mvarId.assert `hByCases (mkOr p (mkNot p)) (mkEM p)
  let (fvarId, mvarId) ← mvarId.intro1
  let #[s₁, s₂] ← mvarId.cases fvarId #[{ varNames := [hName] }, { varNames := [hName] }] |
    throwError "'byCases' tactic failed, unexpected number of subgoals"
  return ((← toByCasesSubgoal s₁), (← toByCasesSubgoal s₂))

builtin_initialize registerTraceClass `Meta.Tactic.cases

end Lean.Meta
