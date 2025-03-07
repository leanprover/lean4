/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AddDecl
import Lean.ReservedNameAction
import Lean.ResolveName
import Lean.Meta.AppBuilder
import Lean.Class

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
  The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `eq_i : HEq a_i b_i`.
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
      throwError "failed to generate hcongr theorem, insufficient number of arguments"
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
            loop (i+1) (eqs.push h) (kinds.push CongrArgKind.eq)
        else
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkHEq x y) fun h =>
            loop (i+1) (eqs.push h) (kinds.push CongrArgKind.heq)
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
  Ensure that all dependencies for `congr_arg_kind::Eq` are `congr_arg_kind::Fixed`.
-/
private def fixKindsForDependencies (info : FunInfo) (kinds : Array CongrArgKind) : Array CongrArgKind := Id.run do
  let mut kinds := kinds
  for i in [:info.paramInfo.size] do
    for hj : j in [i+1:info.paramInfo.size] do
      if info.paramInfo[j].backDeps.contains i then
        if kinds[j]! matches CongrArgKind.eq || kinds[j]! matches CongrArgKind.fixed then
          -- We must fix `i` because there is a `j` that depends on `i` and `j` is not cast-fixed.
          kinds := kinds.set! i CongrArgKind.fixed
          break
  return kinds

/--
  (Try to) cast expression `e` to the given type using the equations `eqs`.
  `deps` contains the indices of the relevant equalities.
  Remark: deps is sorted. -/
private partial def mkCast (e : Expr) (type : Expr) (deps : Array Nat) (eqs : Array (Option Expr)) : MetaM Expr := do
  let rec go (i : Nat) (type : Expr) : MetaM Expr := do
     if i < deps.size then
       match eqs[deps[i]!]! with
       | none => go (i+1) type
       | some major =>
         let some (_, lhs, rhs) := (← inferType major).eq? | unreachable!
         if (← dependsOn type major.fvarId!) then
           let motive ← mkLambdaFVars #[rhs, major] type
           let typeNew := type.replaceFVar rhs lhs |>.replaceFVar major (← mkEqRefl lhs)
           let minor ← go (i+1) typeNew
           mkEqRec motive minor major
         else
           let motive ← mkLambdaFVars #[rhs] type
           let typeNew := type.replaceFVar rhs lhs
           let minor ← go (i+1) typeNew
           mkEqNDRec motive minor major
     else
       return e
  go 0 type

private def hasCastLike (kinds : Array CongrArgKind) : Bool :=
  kinds.any fun kind => kind matches CongrArgKind.cast || kind matches CongrArgKind.subsingletonInst

private def withNext (type : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  forallBoundedTelescope type (some 1) (cleanupAnnotations := true) fun xs type => k xs[0]! type

/--
  Test whether we should use `subsingletonInst` kind for instances which depend on `eq`.
  (Otherwise `fixKindsForDependencies`will downgrade them to Fixed -/
private def shouldUseSubsingletonInst (info : FunInfo) (kinds : Array CongrArgKind) (i : Nat) : Bool := Id.run do
  if info.paramInfo[i]!.isDecInst then
    for j in info.paramInfo[i]!.backDeps do
      if kinds[j]! matches CongrArgKind.eq then
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
    for h : i in [:xs.size] do
      if i < val.numParams then
        mask := mask.push false
      else
        let localDecl ← xs[i].fvarId!.getDecl
        mask := mask.push (isSubobjectField? env val.induct localDecl.userName).isSome
    return some mask

/-- Compute `CongrArgKind`s for a simp congruence theorem. -/
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
  for h : i in [:info.paramInfo.size] do
    if info.resultDeps.contains i then
      result := result.push .fixed
    else if info.paramInfo[i].isProp then
      result := result.push .cast
    else if info.paramInfo[i].isInstImplicit then
      if let some mask := mask? then
        if h2 : i < mask.size then
          if mask[i] then
            -- Parameter is a subobect field of a class constructor. See comment above.
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
If it is possible to rewrite, the 0th `CongrArgKind` is `CongrArgKind.eq`,
and otherwise it is `CongrArgKind.fixed`. This is used for the `arg` conv tactic.
-/
def getCongrSimpKindsForArgZero (info : FunInfo) : MetaM (Array CongrArgKind) := do
  let mut result := #[]
  for h : i in [:info.paramInfo.size] do
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
  Create a congruence theorem that is useful for the simplifier and `congr` tactic.
-/
partial def mkCongrSimpCore? (f : Expr) (info : FunInfo) (kinds : Array CongrArgKind) (subsingletonInstImplicitRhs : Bool := true) : MetaM (Option CongrTheorem) := do
  if let some result ← mk? f info kinds then
    return some result
  else if hasCastLike kinds then
    -- Simplify kinds and try again
    let kinds := kinds.map fun kind =>
      if kind matches CongrArgKind.cast || kind matches CongrArgKind.subsingletonInst then CongrArgKind.fixed else kind
    mk? f info kinds
  else
    return none
where
  /--
    Create a congruence theorem that is useful for the simplifier.
    In this kind of theorem, if the i-th argument is a `cast` argument, then the theorem
    contains an input `a_i` representing the i-th argument in the left-hand-side, and
    it appears with a cast (e.g., `Eq.drec ... a_i ...`) in the right-hand-side.
    The idea is that the right-hand-side of this theorem "tells" the simplifier
    how the resulting term looks like. -/
  mk? (f : Expr) (info : FunInfo) (kinds : Array CongrArgKind) : MetaM (Option CongrTheorem) := do
    try
      let fType ← inferType f
      forallBoundedTelescope fType kinds.size (cleanupAnnotations := true) fun lhss _ => do
        if lhss.size != kinds.size then return none
        let rec go (i : Nat) (rhss : Array Expr) (eqs : Array (Option Expr)) (hyps : Array Expr) : MetaM CongrTheorem := do
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
                go (i+1) (rhss.push rhs) (eqs.push eq) (hyps.push rhs |>.push eq)
            | .fixed => go (i+1) (rhss.push lhss[i]!) (eqs.push none) hyps
            | .cast =>
              let rhsType := (← inferType lhss[i]!).replaceFVars (lhss[:rhss.size]) rhss
              let rhs ← mkCast lhss[i]! rhsType info.paramInfo[i]!.backDeps eqs
              go (i+1) (rhss.push rhs) (eqs.push none) hyps
            | .subsingletonInst =>
              -- The `lhs` does not need to instance implicit since it can be inferred from the LHS
              withNewBinderInfos #[(lhss[i]!.fvarId!, .implicit)] do
                let rhsType := (← inferType lhss[i]!).replaceFVars (lhss[:rhss.size]) rhss
                let rhsBi   := if subsingletonInstImplicitRhs then .instImplicit else .implicit
                withLocalDecl (← lhss[i]!.fvarId!.getDecl).userName rhsBi rhsType fun rhs =>
                  go (i+1) (rhss.push rhs) (eqs.push none) (hyps.push rhs)
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
def mkCongrSimp? (f : Expr) (subsingletonInstImplicitRhs : Bool := true) : MetaM (Option CongrTheorem) := do
  let f := (← instantiateMVars f).cleanupAnnotations
  let info ← getFunInfo f
  mkCongrSimpCore? f info (← getCongrSimpKinds f info) (subsingletonInstImplicitRhs := subsingletonInstImplicitRhs)

def hcongrThmSuffixBase := "hcongr"
def hcongrThmSuffixBasePrefix := hcongrThmSuffixBase ++ "_"

/-- Returns `true` if `s` is of the form `hcongr_<idx>` -/
def isHCongrReservedNameSuffix (s : String) : Bool :=
  hcongrThmSuffixBasePrefix.isPrefixOf s && (s.drop 7).isNat

def congrSimpSuffix := "congr_simp"

builtin_initialize congrKindsExt : MapDeclarationExtension (Array CongrArgKind) ← mkMapDeclarationExtension

builtin_initialize registerReservedNamePredicate fun env n =>
  match n with
  | .str p s => (isHCongrReservedNameSuffix s || s == congrSimpSuffix) && env.isSafeDefinition p
  | _ => false

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless (← getEnv).isSafeDefinition p do return false
    if isHCongrReservedNameSuffix s then
      let numArgs := (s.drop 7).toNat!
      try MetaM.run' do
        let info ← getConstInfo p
        let f := mkConst p (info.levelParams.map mkLevelParam)
        let congrThm ← mkHCongrWithArity f numArgs
        addDecl <| Declaration.thmDecl {
           name, type := congrThm.type, value := congrThm.proof
           levelParams := info.levelParams
        }
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
        addDecl <| Declaration.thmDecl {
           name, type := congrThm.type, value := congrThm.proof
           levelParams := cinfo.levelParams
        }
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
    unless (← getEnv).contains thmName do
      executeReservedNameAction thmName
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
  try
    let thmName := Name.str declName congrSimpSuffix
    unless (← getEnv).contains thmName do
      executeReservedNameAction thmName
    let proof := mkConst thmName levels
    let type ← inferType proof
    let some argKinds := congrKindsExt.find? (← getEnv) thmName
      | unreachable!
    return some { proof, type, argKinds }
  catch _ =>
    return none

end Lean.Meta
