/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Basic
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Check
import Lean.Meta.Tactic.Subst
import Lean.Meta.Injective -- for elimOptParam
import Lean.Meta.ArgsPacker
import Lean.Meta.PProdN
import Lean.Meta.Tactic.Apply
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import Lean.Elab.Command
import Lean.Meta.Tactic.ElimInfo

namespace Lean.Elab.PartialFixpoint

open Lean Elab Meta

open Lean.Order

def mkAdmAnd (α instα adm₁ adm₂ : Expr) : MetaM Expr :=
  mkAppOptM ``admissible_and #[α, instα, none, none, adm₁, adm₂]

partial def mkAdmProj (packedInst : Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if let some inst ← whnfUntil packedInst ``instCCPOPProd then
    let_expr instCCPOPProd α β instα instβ := inst | throwError "mkAdmProj: unexpected instance {inst}"
    if i == 0 then
      mkAppOptM ``admissible_pprod_fst #[α, β, instα, instβ, none, e]
    else
      let e ← mkAdmProj instβ (i - 1) e
      mkAppOptM ``admissible_pprod_snd #[α, β, instα, instβ, none, e]
  else
    assert! i == 0
    return e

def CCPOProdProjs (n : Nat) (inst : Expr) : Array Expr := Id.run do
  let mut insts := #[inst]
  while insts.size < n do
    let inst := insts.back!
    let_expr Lean.Order.instCCPOPProd _ _ inst₁ inst₂ := inst
      | panic! s!"isOptionFixpoint: unexpected CCPO instance {inst}"
    insts := insts.pop
    insts := insts.push inst₁
    insts := insts.push inst₂
  return insts


/-- `maskArray mask xs` keeps those `x` where the corresponding entry in `mask` is `true` -/
-- Worth having in the standard libray?
private def maskArray {α} (mask : Array Bool) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for b in mask, x in xs do
    if b then ys := ys.push x
  return ys

/-- Appends `_1` etc to `base` unless `n == 1` -/
private def numberNames (n : Nat) (base : String) : Array Name :=
  .ofFn (n := n) fun ⟨i, _⟩ =>
    if n == 1 then .mkSimple base else .mkSimple s!"{base}_{i+1}"

def deriveInduction (name : Name) : MetaM Unit :=
  let inductName := name ++ `fixpoint_induct
  realizeConst name inductName do
  mapError (f := (m!"Cannot derive fixpoint induction principle (please report this issue)\n{indentD ·}")) do
    let some eqnInfo := eqnInfoExt.find? (← getEnv) name |
      throwError "{name} is not defined by partial_fixpoint"

    let infos ← eqnInfo.declNames.mapM getConstInfoDefn
    -- First open up the fixed parameters everywhere
    let e' ← eqnInfo.fixedParamPerms.perms[0]!.forallTelescope infos[0]!.type fun xs => do
      -- Now look at the body of an arbitrary of the functions (they are essentially the same
      -- up to the final projections)
      let body ← eqnInfo.fixedParamPerms.perms[0]!.instantiateLambda infos[0]!.value xs

      -- The body should now be of the form of the form (fix … ).2.2.1
      -- We strip the projections (if present)
      let body' := PProdN.stripProjs body.eta -- TODO: Eta more carefully?
      let some fixApp ← whnfUntil body' ``fix
        | throwError "Unexpected function body {body}, could not whnfUntil fix"
      let_expr fix α instCCPOα F hmono := fixApp
        | throwError "Unexpected function body {body'}, not an application of fix"

      let instCCPOs := CCPOProdProjs infos.size instCCPOα
      let types ← infos.mapIdxM (eqnInfo.fixedParamPerms.perms[·]!.instantiateForall ·.type xs)
      let packedType ← PProdN.pack 0 types
      let motiveTypes ← types.mapM (mkArrow · (.sort 0))
      let motiveNames := numberNames motiveTypes.size "motive"
      withLocalDeclsDND (motiveNames.zip motiveTypes) fun motives => do
        let packedMotive ←
          withLocalDeclD (← mkFreshUserName `x) packedType fun x => do
            mkLambdaFVars #[x] <| ← PProdN.pack 0 <|
              motives.mapIdx fun idx motive =>
                mkApp motive (PProdN.proj motives.size idx packedType x)

        let admTypes ← motives.mapIdxM fun i motive => do
          mkAppOptM ``admissible #[types[i]!, instCCPOs[i]!, some motive]
        let admNames := numberNames admTypes.size "adm"
        withLocalDeclsDND (admNames.zip admTypes) fun adms => do
          let adms' ← adms.mapIdxM fun i adm => mkAdmProj instCCPOα i adm
          let packedAdm ← PProdN.genMk (mkAdmAnd α instCCPOα) adms'
          let hNames := numberNames infos.size "h"
          let hTypes_hmask : Array (Expr × Array Bool) ← infos.mapIdxM fun i _info => do
            let approxNames := infos.map fun info =>
              match info.name with
                | .str _ n => .mkSimple n
                | _ => `f
            withLocalDeclsDND (approxNames.zip types) fun approxs => do
              let ihTypes := approxs.mapIdx fun j approx => mkApp motives[j]! approx
              withLocalDeclsDND (ihTypes.map (⟨`ih, ·⟩)) fun ihs => do
                let f ← PProdN.mk 0 approxs
                let Ff := F.beta #[f]
                let Ffi := PProdN.proj motives.size i packedType Ff
                let t := mkApp motives[i]! Ffi
                let t ← PProdN.reduceProjs t
                let mask := approxs.map fun approx => t.containsFVar approx.fvarId!
                let t ← mkForallFVars (maskArray mask approxs ++ maskArray mask ihs) t
                pure (t, mask)
          let (hTypes, masks) := hTypes_hmask.unzip
          withLocalDeclsDND (hNames.zip hTypes) fun hs => do
            let packedH ←
              withLocalDeclD `approx packedType fun approx =>
                let packedIHType := packedMotive.beta #[approx]
                withLocalDeclD `ih packedIHType fun ih => do
                  let approxs := PProdN.projs motives.size packedType approx
                  let ihs := PProdN.projs motives.size packedIHType ih
                  let e ← PProdN.mk 0 <| hs.mapIdx fun i h =>
                    let mask := masks[i]!
                    mkAppN h (maskArray mask approxs ++ maskArray mask ihs)
                  mkLambdaFVars #[approx, ih] e
            let e' ← mkAppOptM ``fix_induct #[α, instCCPOα, F, hmono, packedMotive, packedAdm, packedH]
            -- Should be the type of e', but with the function definitions folded
            let packedConclusion ← PProdN.pack 0 <| ←
              motives.mapIdxM fun i motive => do
                let f ← mkConstWithLevelParams infos[i]!.name
                let fEtaExpanded ← lambdaTelescope infos[i]!.value fun ys _ =>
                  mkLambdaFVars ys (mkAppN f ys)
                let fInst ← eqnInfo.fixedParamPerms.perms[i]!.instantiateLambda fEtaExpanded xs
                let fInst := fInst.eta
                return mkApp motive fInst
            let e' ← mkExpectedTypeHint e' packedConclusion
            let e' ← mkLambdaFVars hs e'
            let e' ← mkLambdaFVars adms e'
            let e' ← mkLambdaFVars motives e'
            let e' ← mkLambdaFVars (binderInfoForMVars := .default) (usedOnly := true) xs e'
            let e' ← instantiateMVars e'
            trace[Elab.definition.partialFixpoint.induction] "complete body of fixpoint induction principle:{indentExpr e'}"
            pure e'

    let eTyp ← inferType e'
    let eTyp ← elimOptParam eTyp
    -- logInfo m!"eTyp: {eTyp}"
    let params := (collectLevelParams {} eTyp).params
    -- Prune unused level parameters, preserving the original order
    let us := infos[0]!.levelParams.filter (params.contains ·)

    addDecl <| Declaration.thmDecl
      { name := inductName, levelParams := us, type := eTyp, value := e' }

def isInductName (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "fixpoint_induct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      return p == eqnInfo.declNames[0]!
    return false
  | _ => return false

builtin_initialize
  registerReservedNamePredicate isInductName

  registerReservedNameAction fun name => do
    if isInductName (← getEnv) name then
      let .str p _ := name | return false
      MetaM.run' <| deriveInduction p
      return true
    return false

/--
Returns true if `name` defined by `partial_fixpoint`, the first in its mutual group,
and all functions are defined using the `CCPO` instance for `Option`.
-/
def isOptionFixpoint (env : Environment) (name : Name) : Bool := Option.isSome do
  let eqnInfo ← eqnInfoExt.find? env name
  guard <| name == eqnInfo.declNames[0]!
  let defnInfo ← env.find? eqnInfo.declNameNonRec
  assert! defnInfo.hasValue
  let mut value := defnInfo.value!
  while value.isLambda do value := value.bindingBody!
  let_expr Lean.Order.fix _ inst _ _ := value | panic! s!"isOptionFixpoint: unexpected value {value}"
  let insts := CCPOProdProjs eqnInfo.declNames.size inst
  insts.forM fun inst => do
    let mut inst := inst
    while inst.isAppOfArity ``instCCPOPi 3 do
      guard inst.appArg!.isLambda
      inst := inst.appArg!.bindingBody!
    guard <| inst.isAppOfArity ``instCCPOOption 1

def isPartialCorrectnessName (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  unless s == "partial_correctness" do return false
  return isOptionFixpoint env p

/--
Given `motive : α → β → γ → Prop`, construct a proof of
`admissible (fun f => ∀ x y r, f x y = r → motive x y r)`
-/
def mkOptionAdm (motive : Expr) : MetaM Expr := do
  let type ← inferType motive
  forallTelescope type fun ysr _ => do
    let P := mkAppN motive ysr
    let ys := ysr.pop
    let r := ysr.back!
    let mut inst ← mkAppM ``Option.admissible_eq_some #[P, r]
    inst ← mkLambdaFVars #[r] inst
    inst ← mkAppOptM ``admissible_pi #[none, none, none, none, inst]
    for y in ys.reverse do
      inst ← mkLambdaFVars #[y] inst
      inst ← mkAppOptM ``admissible_pi_apply #[none, none, none, none, inst]
    pure inst

def derivePartialCorrectness (name : Name) : MetaM Unit := do
  let inductName := name ++ `partial_correctness
  realizeConst name inductName do
  let fixpointInductThm := name ++ `fixpoint_induct
  unless (← getEnv).contains fixpointInductThm do
    deriveInduction name

  mapError (f := (m!"Cannot derive partial correctness theorem (please report this issue)\n{indentD ·}")) do
    let some eqnInfo := eqnInfoExt.find? (← getEnv) name |
      throwError "{name} is not defined by partial_fixpoint"

    let infos ← eqnInfo.declNames.mapM getConstInfoDefn
    let fixedParamPerm0 := eqnInfo.fixedParamPerms.perms[0]!
    -- First open up the fixed parameters everywhere
    let e' ← fixedParamPerm0.forallTelescope infos[0]!.type fun xs => do
      let types ← infos.mapIdxM (eqnInfo.fixedParamPerms.perms[·]!.instantiateForall ·.type xs)

      -- for `f : α → β → Option γ`, we expect a `motive : α → β → γ → Prop`
      let motiveTypes ← types.mapM fun type =>
        forallTelescopeReducing type fun ys type => do
          let type ← whnf type
          let_expr Option γ := type | throwError "Expected `Option`, got:{indentExpr type}"
          withLocalDeclD (← mkFreshUserName `r) γ fun r =>
            mkForallFVars (ys.push r) (.sort 0)
      let motiveDecls ← motiveTypes.mapIdxM fun i motiveType => do
        let n := if infos.size = 1 then .mkSimple "motive"
                                   else .mkSimple s!"motive_{i+1}"
        pure (n, fun _ => pure motiveType)
      withLocalDeclsD motiveDecls fun motives => do
        -- the motives, as expected by `f.fixpoint_induct`:
        -- fun f => ∀ x y r, f x y = some r → motive x y r
        let motives' ← motives.mapIdxM fun i motive => do
          withLocalDeclD (← mkFreshUserName `f) types[i]! fun f => do
            forallTelescope (← inferType motive) fun ysr _ => do
              let ys := ysr.pop
              let r := ysr.back!
              let heq ← mkEq (mkAppN f ys) (← mkAppM ``some #[r])
              let motive' ← mkArrow heq (mkAppN motive ysr)
              let motive' ← mkForallFVars ysr motive'
              mkLambdaFVars #[f] motive'

        let e' ← mkAppOptM fixpointInductThm <| (xs ++ motives').map some
        let adms ← motives.mapM mkOptionAdm
        let e' := mkAppN e' adms
        let e' ← mkLambdaFVars motives e'
        let e' ← mkLambdaFVars (binderInfoForMVars := .default) (usedOnly := true) xs e'
        let e' ← instantiateMVars e'
        trace[Elab.definition.partialFixpoint.induction] "complete body of partial correctness principle:{indentExpr e'}"
        pure e'

    let eTyp ← inferType e'
    let eTyp ← elimOptParam eTyp
    let eTyp ← Core.betaReduce eTyp
    -- logInfo m!"eTyp: {eTyp}"
    let params := (collectLevelParams {} eTyp).params
    -- Prune unused level parameters, preserving the original order
    let us := infos[0]!.levelParams.filter (params.contains ·)

    addDecl <| Declaration.thmDecl
      { name := inductName, levelParams := us, type := eTyp, value := e' }

builtin_initialize
  registerReservedNamePredicate isPartialCorrectnessName

  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless s == "partial_correctness" do return false
    unless isOptionFixpoint (← getEnv) p do return false
    MetaM.run' <| derivePartialCorrectness p
    return false

end Lean.Elab.PartialFixpoint

builtin_initialize Lean.registerTraceClass `Elab.definition.partialFixpoint.induction
