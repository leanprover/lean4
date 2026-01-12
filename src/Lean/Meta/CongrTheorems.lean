/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.AddDecl
public import Lean.ReservedNameAction
import Lean.Structure
import Lean.Meta.Tactic.Subst
import Lean.Meta.FunInfo
public section
namespace Lean.Meta

inductive CongrArgKind where
  /-- It is a parameter for the congruence theorem, the parameter occurs in the left and right hand sides. -/
  | fixed
  /--
  It is not a parameter for the congruence theorem, the theorem was specialized for this parameter.
  This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. -/
  | fixedNoParam
  /--
  The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `eq_i : a_i = b_i`.
  `a_i` and `b_i` represent the left and right hand sides, and `eq_i` is a proof for their equality. -/
  | eq
  /--
  The congr-simp theorems contains only one parameter for this kind of argument, and congr theorems contains two.
  They correspond to arguments that are subsingletons/propositions. -/
  | cast
  /--
  The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `eq_i : a_i ≍ b_i`.
  `a_i` and `b_i` represent the left and right hand sides, and `eq_i` is a proof for their heterogeneous equality. -/
  | heq
  /--
  For congr-simp theorems only.  Indicates a decidable instance argument.
  The lemma contains two arguments [a_i : Decidable ...] [b_i : Decidable ...] -/
  | subsingletonInst
  deriving Inhabited, Repr, BEq

structure CongrTheorem where
  type     : Expr
  proof    : Expr
  argKinds : Array CongrArgKind

private def addPrimeToFVarUserNames (ys : Array Expr) (lctx : LocalContext) : LocalContext := Id.run do
  let mut lctx := lctx
  for y in ys do
    let decl := lctx.getFVar! y
    lctx := lctx.setUserName decl.fvarId (decl.userName.appendAfter "'")
  return lctx

private def setBinderInfosD (ys : Array Expr) (lctx : LocalContext) : LocalContext := Id.run do
  let mut lctx := lctx
  for y in ys do
    let decl := lctx.getFVar! y
    lctx := lctx.setBinderInfo decl.fvarId BinderInfo.default
  return lctx

partial def mkHCongrWithArity (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let fType ← inferType f
  forallBoundedTelescope fType numArgs (cleanupAnnotations := true) fun xs _ =>
  forallBoundedTelescope fType numArgs (cleanupAnnotations := true) fun ys _ => do
    if xs.size != numArgs then
      throwError "failed to generate `hcongr` theorem: expected {numArgs} arguments, but got {xs.size} for{indentExpr f}"
    else
      let lctx := addPrimeToFVarUserNames ys (← getLCtx) |> setBinderInfosD ys |> setBinderInfosD xs
      withLCtx lctx (← getLocalInstances) do
      withNewEqs xs ys fun eqs argKinds => do
        let mut hs := #[]
        for x in xs, y in ys, eq in eqs do
          hs := hs.push x |>.push y |>.push eq
        let lhs := mkAppN f xs
        let rhs := mkAppN f ys
        let congrType ← mkForallFVars hs (← mkHEq lhs rhs)
        return {
          type  := congrType
          proof := (← mkProof congrType)
          argKinds
        }
where
  withNewEqs {α} (xs ys : Array Expr) (k : Array Expr → Array CongrArgKind → MetaM α) : MetaM α :=
    let rec loop (i : Nat) (eqs : Array Expr) (kinds : Array CongrArgKind) := do
      if i < xs.size then
        let x := xs[i]!
        let y := ys[i]!
        let xType := (← inferType x).cleanupAnnotations
        let yType := (← inferType y).cleanupAnnotations
        if xType == yType then
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkEq x y) fun h =>
            loop (i+1) (eqs.push h) (kinds.push .eq)
        else
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkHEq x y) fun h =>
            loop (i+1) (eqs.push h) (kinds.push .heq)
      else
        k eqs kinds
    loop 0 #[] #[]

  mkProof (type : Expr) : MetaM Expr := do
    if let some (_, lhs, _) := type.eq? then
      mkEqRefl lhs
    else if let some (_, lhs, _, _) := type.heq? then
      mkHEqRefl lhs
    else
      forallBoundedTelescope type (some 1) (cleanupAnnotations := true) fun a type =>
      let a := a[0]!
      forallBoundedTelescope type (some 1) (cleanupAnnotations := true) fun b motive =>
      let b := b[0]!
      let type := type.bindingBody!.instantiate1 a
      withLocalDeclD motive.bindingName! motive.bindingDomain! fun eqPr => do
      let type := type.bindingBody!
      let motive := motive.bindingBody!
      let minor ← mkProof type
      let mut major := eqPr
      if (← whnf (← inferType eqPr)).isHEq then
        major ← mkEqOfHEq major
      let motive ← mkLambdaFVars #[b] motive
      mkLambdaFVars #[a, b, eqPr] (← mkEqNDRec motive minor major)

def mkHCongr (f : Expr) : MetaM CongrTheorem := do
  mkHCongrWithArity f (← getFunInfo f).getArity

/--
Ensures all dependencies for `.eq` are `.fixed`.
-/
private def fixKindsForDependencies (info : FunInfo) (kinds : Array CongrArgKind) : Array CongrArgKind := Id.run do
  let mut kinds := kinds
  for i in *...info.paramInfo.size do
    for hj : j in (i+1)...info.paramInfo.size do
      if info.paramInfo[j].backDeps.contains i then
        if kinds[j]! matches .eq | .fixed then
          -- We must fix `i` because there is a `j` that depends on `i` and `j` is not cast-fixed.
          kinds := kinds.set! i .fixed
          break
  return kinds

/-- Returns `true` if `kinds` contains `.cast` or `.subsingletonInst` -/
private def hasCastLike (kinds : Array CongrArgKind) : Bool :=
  kinds.any fun kind => kind matches .cast | .subsingletonInst

private def withNext (type : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  forallBoundedTelescope type (some 1) (cleanupAnnotations := true) fun xs type => k xs[0]! type

/--
Tests whether we should use `subsingletonInst` kind for instances which depend on `eq`.
(Otherwise `fixKindsForDependencies`will downgrade them to Fixed
-/
private def shouldUseSubsingletonInst (info : FunInfo) (kinds : Array CongrArgKind) (i : Nat) : Bool := Id.run do
  if info.paramInfo[i]!.isDecInst then
    for j in info.paramInfo[i]!.backDeps do
      if kinds[j]! matches .eq then
        return true
  return false

/--
If `f` is a class constructor, return a bitmask `m` s.t. `m[i]` is true if the `i`-th parameter
corresponds to a subobject field.

We use this function to implement the special support for class constructors at `getCongrSimpKinds`.
See issue #1808
-/
private def getClassSubobjectMask? (f : Expr) : MetaM (Option (Array Bool)) := do
  let .const declName _ := f | return none
  let .ctorInfo val ← getConstInfo declName | return none
  unless isClass (← getEnv) val.induct do return none
  forallTelescopeReducing val.type (cleanupAnnotations := true) fun xs _ => do
    let env ← getEnv
    let mut mask := #[]
    for h : i in *...xs.size do
      if i < val.numParams then
        mask := mask.push false
      else
        let localDecl ← xs[i].fvarId!.getDecl
        mask := mask.push (isSubobjectField? env val.induct localDecl.userName).isSome
    return some mask

/-- Computes `CongrArgKind`s for a simp congruence theorem. -/
def getCongrSimpKinds (f : Expr) (info : FunInfo) : MetaM (Array CongrArgKind) := do
  /-
  The default `CongrArgKind` is `eq`, which allows `simp` to rewrite this
  argument. However, if there are references from `i` to `j`, we cannot
  rewrite both `i` and `j`. So we must change the `CongrArgKind` at
  either `i` or `j`. In principle, if there is a dependency with `i`
  appearing after `j`, then we set `j` to `fixed` (or `cast`). But there is
  an optimization: if `i` is a subsingleton, we can fix it instead of
  `j`, since all subsingletons are equal anyway. The fixing happens in
  two loops: one for the special cases, and one for the general case.

  This method has special support for class constructors.
  For this kind of function, we treat subobject fields as regular parameters instead of instance implicit ones.
  We added this feature because of issue #1808
  -/
  let mut result := #[]
  let mask? ← getClassSubobjectMask? f
  for h : i in *...info.paramInfo.size do
    if info.resultDeps.contains i then
      result := result.push .fixed
    else if info.paramInfo[i].isProp then
      result := result.push .cast
    else if info.paramInfo[i].isInstImplicit then
      if let some mask := mask? then
        if h2 : i < mask.size then
          if mask[i] then
            -- Parameter is a subobject field of a class constructor. See comment above.
            result := result.push .eq
            continue
      if shouldUseSubsingletonInst info result i then
        result := result.push .subsingletonInst
      else
        result := result.push .fixed
    else
      result := result.push .eq
  return fixKindsForDependencies info result

/--
Variant of `getCongrSimpKinds` for rewriting just argument 0.
If it is possible to rewrite, the 0th `CongrArgKind` is `.eq`,
and otherwise it is `.fixed`. This is used for the `arg` conv tactic.
-/
def getCongrSimpKindsForArgZero (info : FunInfo) : MetaM (Array CongrArgKind) := do
  let mut result := #[]
  for h : i in *...info.paramInfo.size do
    if info.resultDeps.contains i then
      result := result.push .fixed
    else if i == 0 then
      result := result.push .eq
    else if info.paramInfo[i].isProp then
      result := result.push .cast
    else if info.paramInfo[i].isInstImplicit then
      if shouldUseSubsingletonInst info result i then
        result := result.push .subsingletonInst
      else
        result := result.push .fixed
    else
      result := result.push .fixed
  return fixKindsForDependencies info result

/--
Auxiliary type for applying `mkCast` at `mkCongrSimpCore?`
-/
private inductive EqInfo where
  | /-- `fvarId` is an equality for "type casting." -/
    hyp (fvarId : FVarId)
  | /--
    `lhs` and `rhs` are `Decidable` instances which should have the same type after
    we have applied other type casting operations. We use the helper theorem `Decidable.eq`
    to perform the type cast operation.
    -/
    decSubsingleton (lhs rhs : FVarId)

/--
Helper function for applying the substitution `s`.
It assumes that all entries in `s` map free variables to free variables.
-/
private def getFVarId (s : FVarSubst) (fvarId : FVarId) : FVarId :=
  if let some h := s.find? fvarId then h.fvarId! else fvarId

/--
(Tries to) cast free variable `fvarId` to the given type using the equations `eqs`.
`deps` contains the indices of the relevant equalities.
Remark: deps is sorted.
-/
private partial def mkCast (fvarId : FVarId) (type : Expr) (deps : Array Nat) (eqs : Array (Option EqInfo)) : MetaM Expr := do
  -- Remark: we use the `subst` tactic to avoid re-implementing the `revert`/`intro` logic used there.
  let eqs := deps.filterMap fun idx => eqs[idx]!
  if eqs.isEmpty then return mkFVar fvarId
  let mvar ← mkFreshExprMVar type
  let mut mvarId := mvar.mvarId!
  let mut s : FVarSubst := {}
  for eq in eqs do
    match eq with
    | .hyp fvarId =>
      let fvarId := getFVarId s fvarId
      let (s', mvarId') ← substCore mvarId fvarId (symm := true) s
      s := s'
      mvarId := mvarId'
    | .decSubsingleton lhsFVarId rhsFVarId =>
      let lhsFVarId := getFVarId s lhsFVarId
      let rhsFVarId := getFVarId s rhsFVarId
      let lhs := mkFVar lhsFVarId
      let rhs := mkFVar rhsFVarId
      let eq ← mvarId.withContext <| mkEq lhs rhs
      let h ← mvarId.withContext <| mkAppM ``Subsingleton.elim #[lhs, rhs]
      mvarId ← mvarId.assert `h eq h
      let (fvarId', mvarId') ← mvarId.intro1
      let (s', mvarId') ← substCore mvarId' fvarId' (symm := true) s
      s := s'
      mvarId := mvarId'
  let fvarId := getFVarId s fvarId
  mvarId.assign (mkFVar fvarId)
  instantiateMVars mvar

/--
Creates a congruence theorem that is useful for the simplifier and `congr` tactic.
-/
partial def mkCongrSimpCore? (f : Expr) (info : FunInfo) (kinds : Array CongrArgKind) (subsingletonInstImplicitRhs : Bool := true) : MetaM (Option CongrTheorem) := do
  if let some result ← mk? f info kinds then
    return some result
  else if hasCastLike kinds then
    -- Simplify kinds and try again
    let kinds := kinds.map fun kind => if kind matches .cast | .subsingletonInst then .fixed else kind
    mk? f info kinds
  else
    return none
where
  /--
    Create a congruence theorem that is useful for the simplifier.
    In this kind of theorem, if the i-th argument is a `cast` argument, then the theorem
    contains an input `a_i` representing the i-th argument in the left-hand-side, and
    it appears with a cast (e.g., `Eq.rec ... a_i ...`) in the right-hand-side.
    The idea is that the right-hand-side of this theorem "tells" the simplifier
    how the resulting term looks like. -/
  mk? (f : Expr) (info : FunInfo) (kinds : Array CongrArgKind) : MetaM (Option CongrTheorem) := do
    try
      let fType ← inferType f
      forallBoundedTelescope fType kinds.size (cleanupAnnotations := true) fun lhss _ => do
        if lhss.size != kinds.size then return none
        let rec go (i : Nat) (rhss : Array Expr) (eqs : Array (Option EqInfo)) (hyps : Array Expr) : MetaM CongrTheorem := do
          if i == kinds.size then
            let lhs := mkAppN f lhss
            let rhs := mkAppN f rhss
            let type ← mkForallFVars hyps (← mkEq lhs rhs)
            let proof ← mkProof type kinds
            return { type, proof, argKinds := kinds }
          else
            let hyps := hyps.push lhss[i]!
            match kinds[i]! with
            | .heq | .fixedNoParam => unreachable!
            | .eq =>
              let localDecl ← lhss[i]!.fvarId!.getDecl
              withLocalDecl localDecl.userName localDecl.binderInfo localDecl.type fun rhs => do
              withLocalDeclD (localDecl.userName.appendBefore "e_") (← mkEq lhss[i]! rhs) fun eq => do
                go (i+1) (rhss.push rhs) (eqs.push <| some <| .hyp eq.fvarId!) (hyps.push rhs |>.push eq)
            | .fixed => go (i+1) (rhss.push lhss[i]!) (eqs.push none) hyps
            | .cast =>
              let rhsType := (← inferType lhss[i]!).replaceFVars (lhss[*...rhss.size]) rhss
              let rhs ← mkCast lhss[i]!.fvarId! rhsType info.paramInfo[i]!.backDeps eqs
              go (i+1) (rhss.push rhs) (eqs.push none) hyps
            | .subsingletonInst =>
              -- The `lhs` does not need to instance implicit since it can be inferred from the LHS
              withImplicitBinderInfos #[lhss[i]!] do
                let lhs := lhss[i]!
                let lhsType ← inferType lhs
                let rhsType := lhsType.replaceFVars (lhss[*...rhss.size]) rhss
                let rhsBi   := if subsingletonInstImplicitRhs then .instImplicit else .implicit
                withLocalDecl (← lhss[i]!.fvarId!.getDecl).userName rhsBi rhsType fun rhs => do
                  go (i+1) (rhss.push rhs) (eqs.push <| some <| .decSubsingleton lhs.fvarId! rhs.fvarId!) (hyps.push rhs)
        return some (← go 0 #[] #[] #[])
    catch _ =>
      return none

  mkProof (type : Expr) (kinds : Array CongrArgKind) : MetaM Expr := do
    let rec go (i : Nat) (type : Expr) : MetaM Expr := do
      if i == kinds.size then
        let some (_, lhs, _) := type.eq? | unreachable!
        mkEqRefl lhs
      else
        withNext type fun lhs type => do
        match kinds[i]! with
        | .heq | .fixedNoParam => unreachable!
        | .fixed => mkLambdaFVars #[lhs] (← go (i+1) type)
        | .cast => mkLambdaFVars #[lhs] (← go (i+1) type)
        | .eq =>
          let typeSub := type.bindingBody!.bindingBody!.instantiate #[(← mkEqRefl lhs), lhs]
          withNext type fun rhs type =>
          withNext type fun heq type => do
            let motive ← mkLambdaFVars #[rhs, heq] type
            let proofSub ← go (i+1) typeSub
            mkLambdaFVars #[lhs, rhs, heq] (← mkEqRec motive proofSub heq)
        | .subsingletonInst =>
          let typeSub := type.bindingBody!.instantiate #[lhs]
          withNext type fun rhs type => do
            let motive ← mkLambdaFVars #[rhs] type
            let proofSub ← go (i+1) typeSub
            let heq ← mkAppM ``Subsingleton.elim #[lhs, rhs]
            mkLambdaFVars #[lhs, rhs] (← mkEqNDRec motive proofSub heq)
     go 0 type

/--
Create a congruence theorem for `f`. The theorem is used in the simplifier.

If `subsingletonInstImplicitRhs = true`, the `rhs` corresponding to `[Decidable p]` parameters
is marked as instance implicit. It forces the simplifier to compute the new instance when applying
the congruence theorem.
For the `congr` tactic we set it to `false`.
-/
def mkCongrSimp? (f : Expr) (subsingletonInstImplicitRhs : Bool := true) (maxArgs? : Option Nat := none) : MetaM (Option CongrTheorem) := do
  let f := (← instantiateMVars f).cleanupAnnotations
  let info ← getFunInfo f (maxArgs? := maxArgs?)
  mkCongrSimpCore? f info (← getCongrSimpKinds f info) (subsingletonInstImplicitRhs := subsingletonInstImplicitRhs)

def hcongrThmSuffixBase := "hcongr"
def hcongrThmSuffixBasePrefix := hcongrThmSuffixBase ++ "_"

/-- Returns `true` if `s` is of the form `hcongr_<idx>` -/
def isHCongrReservedNameSuffix (s : String) : Bool :=
  hcongrThmSuffixBasePrefix.isPrefixOf s && (s.drop 7).isNat

def congrSimpSuffix := "congr_simp"

builtin_initialize registerTraceClass `congr.thm

builtin_initialize congrKindsExt : MapDeclarationExtension (Array CongrArgKind) ← mkMapDeclarationExtension

builtin_initialize registerReservedNamePredicate fun env n =>
  match n with
  | .str p s => (isHCongrReservedNameSuffix s || s == congrSimpSuffix) && env.contains p
  | _ => false

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless (← getEnv).contains p do return false
    if isHCongrReservedNameSuffix s then
      let numArgs := (s.drop 7).toNat!
      try MetaM.run' do
        let info ← getConstInfo p
        let f := mkConst p (info.levelParams.map mkLevelParam)
        let congrThm ← mkHCongrWithArity f numArgs
        realizeConst p name do
          addDecl <| ← mkThmOrUnsafeDef {
            name, type := congrThm.type, value := congrThm.proof
            levelParams := info.levelParams
          }
          trace[congr.thm] "declared `{name}`"
          modifyEnv fun env => congrKindsExt.insert env name congrThm.argKinds
        return true
      catch _ => return false
    else if s == congrSimpSuffix then
      try MetaM.run' do
        let cinfo ← getConstInfo p
        let f := mkConst p (cinfo.levelParams.map mkLevelParam)
        let info ← getFunInfo f
        let some congrThm ← mkCongrSimpCore? f info (← getCongrSimpKinds f info)
          | return false
        realizeConst p name do
          addDecl <| ← mkThmOrUnsafeDef {
            name, type := congrThm.type, value := congrThm.proof
            levelParams := cinfo.levelParams
          }
          trace[congr.thm] "declared `{name}`"
          modifyEnv fun env => congrKindsExt.insert env name congrThm.argKinds
        return true
      catch _ => return false
    else
      return false

/--
Similar to `mkHCongrWithArity`, but uses reserved names to ensure we don't keep creating the
same congruence theorem over and over again.
-/
def mkHCongrWithArityForConst? (declName : Name) (levels : List Level) (numArgs : Nat) : MetaM (Option CongrTheorem) := do
  try
    let suffix := hcongrThmSuffixBasePrefix ++ toString numArgs
    let thmName := Name.str declName suffix
    unless (← getEnv).containsOnBranch thmName do
      let _ ← executeReservedNameAction thmName
    let proof := mkConst thmName levels
    let type ← inferType proof
    let some argKinds := congrKindsExt.find? (← getEnv) thmName
      | unreachable!
    return some { proof, type, argKinds }
  catch _ =>
    return none

/--
Similar to `mkCongrSimp?`, but uses reserved names to ensure we don't keep creating the
same congruence theorem over and over again.
-/
def mkCongrSimpForConst? (declName : Name) (levels : List Level) : MetaM (Option CongrTheorem) := do
  let thmName := Name.str declName congrSimpSuffix
  try
    unless (← getEnv).containsOnBranch thmName do
      let _ ← executeReservedNameAction thmName
    let proof := mkConst thmName levels
    let type ← inferType proof
    let some argKinds := congrKindsExt.find? (← getEnv) thmName
      | unreachable!
    return some { proof, type, argKinds }
  catch ex =>
    trace[congr.thm] "failed to generate `{thmName}` {ex.toMessageData}"
    return none

end Lean.Meta
