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
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import Lean.Elab.Command
import Lean.Meta.Tactic.ElimInfo

namespace Lean.Elab.PartialFixpoint

open Lean Elab Meta

open Lean.Order

-- TODO: Move to PProdN, remove from FunIn
def stripPProdProjs (e : Expr) : Expr :=
  match e with
  | .proj ``PProd _ e' => stripPProdProjs e'
  | .proj ``And _ e' => stripPProdProjs e'
  | e => e

def mkAdmAnd (α instα adm₁ adm₂ : Expr) : MetaM Expr :=
  mkAppOptM ``admissible_and #[α, instα, none, none, adm₁, adm₂]

partial def mkAdmProj (packedInst : Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if let some inst ← whnfUntil packedInst ``instCCPOPProd then
    let_expr instCCPOPProd α β instα instβ := inst | throwError "mkAdmProj: unexpected instance {inst}"
    if i == 0 then
      mkAppOptM ``admissible_fst #[α, β, instα, instβ, none, e]
    else
      let e ← mkAdmProj instβ (i - 1) e
      mkAppOptM ``admissible_snd #[α, β, instα, instβ, none, e]
  else
    assert! i == 0
    return e

def reducePProdProj (e : Expr) : MetaM Expr := do
  transform e (post := fun e => do
    if e.isProj then
      if e.projExpr!.isAppOfArity ``PProd.mk 4 || e.projExpr!.isAppOfArity ``And.intro 2 then
        if e.projIdx! == 0 then
          return .continue e.projExpr!.appFn!.appArg!
        else
          return .continue e.projExpr!.appArg!
    return .continue
  )

def deriveInduction (name : Name) : MetaM Unit := do
  mapError (f := (m!"Cannot derive fixpoint induction principle (please report this issue)\n{indentD ·}")) do
    let some eqnInfo := eqnInfoExt.find? (← getEnv) name |
      throwError "{name} is not defined by partial_fixpoint"

    let infos ← eqnInfo.declNames.mapM getConstInfoDefn
    -- First open up the fixed parameters everywhere
    let e' ← lambdaBoundedTelescope infos[0]!.value eqnInfo.fixedPrefixSize fun xs _ => do
      -- Now look at the body of an arbitrary of the functions (they are essentially the same
      -- up to the final projections)
      let body ← instantiateLambda infos[0]!.value xs

      -- The body should now be of the form of the form (fix … ).2.2.1
      -- We strip the projections (if present)
      let body' := stripPProdProjs body
      let some fixApp ← whnfUntil body' ``fix
        | throwError "Unexpected function body {body}"
      let_expr fix α instCCPOα F hmono := fixApp
        | throwError "Unexpected function body {body'}"

      let mut instCCPOs := #[instCCPOα]
      while instCCPOs.size < infos.size do
        let inst := instCCPOs.back!
        let_expr Lean.Order.instCCPOPProd _ _ inst₁ inst₂ := inst
          | throwError "Unexpected CCPO instance {inst}"
        instCCPOs := instCCPOs.pop
        instCCPOs := instCCPOs.push inst₁
        instCCPOs := instCCPOs.push inst₂

      let types ← infos.mapM (instantiateForall ·.type xs)
      let packedType ← PProdN.pack 0 types
      let motiveTypes ← types.mapM (mkArrow · (.sort 0))
      let motiveDecls ← motiveTypes.mapIdxM fun i motiveType => do
        let n := if infos.size = 1 then .mkSimple "motive"
                                   else .mkSimple s!"motive_{i+1}"
        pure (n, fun _ => pure motiveType)
      withLocalDeclsD motiveDecls fun motives => do
        let packedMotive ←
          withLocalDeclD (← mkFreshUserName `x) packedType fun x => do
            mkLambdaFVars #[x] <| ← PProdN.pack 0 <|
              motives.mapIdx fun idx motive =>
                mkApp motive (PProdN.proj motives.size idx packedType x)

        let admDecls ← motives.mapIdxM fun i motive => do
          let n := if infos.size = 1 then .mkSimple "adm"
                                     else .mkSimple s!"adm_{i+1}"
          let t ← mkAppOptM ``admissible #[types[i]!, instCCPOs[i]!, some motive]
          pure (n, fun _ => pure t)
        withLocalDeclsD admDecls fun adms => do
          let adms' ← adms.mapIdxM fun i adm => mkAdmProj instCCPOα i adm
          let packedAdm ← adms'.pop.foldrM (mkAdmAnd α instCCPOα) adms'.back!

          let hDecls ← infos.mapIdxM fun i _info => do
            let n := if infos.size = 1 then .mkSimple "h"
                                      else .mkSimple s!"h_{i+1}"
            let approxDecls ← types.mapIdxM fun j type => do
              let n := match infos[j]!.name with
                | .str _ n => .mkSimple n
                | _ => `f
              pure (n, fun _ => pure type)
            let t ← withLocalDeclsD approxDecls fun approxs => do
              let ihDecls ← approxs.mapIdxM fun j approx => do
                let n := `ih
                pure (n, fun _ => pure (mkApp motives[j]! approx))
              withLocalDeclsD ihDecls fun ihs => do
                let f ← PProdN.mk 0 approxs
                let Ff := F.beta #[f]
                let Ffi := PProdN.proj motives.size i packedType Ff
                let t := mkApp motives[i]! Ffi
                let t ← reducePProdProj t
                mkForallFVars (approxs ++ ihs) t
            pure (n, fun _ => pure t)
          withLocalDeclsD hDecls fun hs => do

            let packedH ←
              withLocalDeclD `approx packedType fun approx =>
                let packedIHType := packedMotive.beta #[approx]
                withLocalDeclD `ih packedIHType fun ih => do
                  let approxs := Array.ofFn (n := motives.size) fun i =>
                    PProdN.proj motives.size i packedType approx
                  let ihs := Array.ofFn (n := motives.size) fun i =>
                    PProdN.proj motives.size i packedIHType ih
                  let e ← PProdN.mk 0 <| hs.map fun h => mkAppN h (approxs ++ ihs)
                  mkLambdaFVars #[approx, ih] e
            let e' ← mkAppOptM ``fix_induct #[α, instCCPOα, F, hmono, packedMotive, packedAdm, packedH]
            -- Should be the type of e', but with the function definitions folded
            let packedConclusion ← PProdN.pack 0 <| ←
              motives.mapIdxM fun i motive => do
                let f ← mkConstWithLevelParams infos[i]!.name
                return mkApp motive (mkAppN f xs)
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

    let inductName := name ++ `fixpoint_induct
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

end Lean.Elab.PartialFixpoint

builtin_initialize Lean.registerTraceClass `Elab.definition.partialFixpoint.induction
