/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Robin Arnez
-/
module

prelude
public import Lean.Meta.Constructions.CasesOn

public section

namespace Lean.Meta.IndPredBelow

structure Context where
  /-- Any inductive in the mutual group -/
  indVal : InductiveVal
  /-- Inductive eliminates into any universe -/
  largeElim : Bool
  /-- Parameters of the mutual inductive -/
  params : Array Expr
  /-- The motives (fvar ids) -/
  motives : Array Expr
  /-- Map from motive to motive index (opposite of `motives[·]`) -/
  motiveToIdx : FVarIdMap Nat
  /-- The minor premises (fvar ids) -/
  minors : Array Expr
  /-- Recursor names (corresponding to the motives) -/
  recNames : Array Name
  /-- Names of below declarations (corresponding to the motives) -/
  belowNames : Array Name
  /-- Names of brecOn declarations (corresponding to the motives) -/
  brecOnNames : Array Name

/-- Is `type` a motive nested in foralls and applications? -/
def isIH (type : Expr) (ctx : Context) : MetaM (Option Nat) := do
  let .fvar f := type.getForallBody.getAppFn | return none
  return ctx.motiveToIdx.get? f

/-- Returns `@XYZ.below params... motives...` -/
def mkBelowAppOfIdx (i : Nat) (ctx : Context) : Expr :=
  let const := .const (ctx.belowNames[i]!) (ctx.indVal.levelParams.map Level.param)
  mkAppN (mkAppN const ctx.params) ctx.motives

/-- Replaces the application of the motive with the corresponding below name. -/
def ihTypeToBelowType : Expr → Context → Expr
  | .fvar f, ctx => mkBelowAppOfIdx (ctx.motiveToIdx.get! f) ctx
  | .app f a, ctx => .app (ihTypeToBelowType f ctx) a
  | .forallE nm t b bi, ctx => .forallE nm t (ihTypeToBelowType b ctx) bi
  | _, _=> unreachable!

def toImplicit (e : Expr) : Expr :=
  match e with
  | .forallE _ t b@(.forallE ..) _ => e.updateForall! .implicit t (toImplicit b)
  | e => e

/-- Generate `belowNames[motiveIdx]` -/
def recToBelow (motiveIdx minorIdx : Nat) (ctx : Context) : MetaM (Nat × InductiveType) := do
  let motive := ctx.motives[motiveIdx]!
  let motiveType ← inferType motive
  let name := ctx.belowNames[motiveIdx]!
  let paramsAndMotives := ctx.params ++ ctx.motives
  let type ← mkForallFVars paramsAndMotives (toImplicit motiveType)
  let mut minorIdx := minorIdx
  let mut ctors := #[]
  while minorIdx < ctx.minors.size do
    let minor := ctx.minors[minorIdx]!
    let minorName ← minor.fvarId!.getUserName
    let minorType ← inferType minor
    if minorType.getForallBody.getAppFn != motive then
      break
    let ctorName := name ++ minorName
    let ctorType ← forallTelescope minorType fun minorArgs body => do
      let rec go (i : Nat) (vars : Array Expr) : MetaM Expr := do
        if h : i < minorArgs.size then
          let type ← inferType minorArgs[i]
          if let some _ ← isIH type ctx then
            withLocalDeclD (← mkFreshUserName `ih) (ihTypeToBelowType type ctx) fun below =>
              go (i + 1) ((vars.push below).push minorArgs[i])
          else
            go (i + 1) (vars.push minorArgs[i])
        else
          mkForallFVars vars (ihTypeToBelowType body ctx)
      termination_by minorArgs.size - i
      go 0 paramsAndMotives
    ctors := ctors.push {
      name := ctorName
      type := ctorType
    }
    minorIdx := minorIdx + 1
  let induct : InductiveType := { name, type, ctors := ctors.toList }
  return (minorIdx, induct)

def mkBelowInductives (ctx : Context) : MetaM Unit := do
  let nmotives := ctx.motives.size
  let mut minorIdx := 0
  let mut inducts := #[]
  for i in *...nmotives do
    let (newIdx, ind) ← recToBelow i minorIdx ctx
    inducts := inducts.push ind
    minorIdx := newIdx
  let nparams := ctx.params.size + ctx.motives.size
  Lean.addDecl <| .inductDecl ctx.indVal.levelParams nparams inducts.toList ctx.indVal.isUnsafe
  for b in ctx.belowNames do
    Lean.mkCasesOn b

def withBRecOnArgs (k : (newMinors : Array Expr) → (proofArgs : Array Expr) → MetaM Unit) (ctx : Context) : MetaM Unit := do
  let rec go (i : Nat) (newMinors : Array Expr) : MetaM Unit := do
    if h : i < ctx.motives.size then
      let motive := ctx.motives[i]
      let motiveType ← inferType motive
      let type ← forallTelescope motiveType fun majors _ => do
        let type ← mkArrow (mkAppN (mkBelowAppOfIdx i ctx) majors) (mkAppN motive majors)
        mkForallFVars majors type
      withLocalDeclD ((`F).appendIndexAfter (i + 1)) type fun minor =>
        go (i + 1) (newMinors.push minor)
    else
      let recMotives := (Array.range ctx.motives.size).map (mkBelowAppOfIdx · ctx)
      let mut recMinors := #[]
      for minor in ctx.minors do
        let minorType ← inferType minor
        let i := ctx.motiveToIdx.get! minorType.getForallBody.getAppFn.fvarId!
        let name ← minor.fvarId!.getUserName
        let belowCtorName := ctx.belowNames[i]! ++ name
        let expr ← forallTelescope minorType fun minorArgs res => do
          let rec go2 (j : Nat) (vars args : Array Expr) : MetaM Expr := do
            if h : j < minorArgs.size then
              let type ← inferType minorArgs[j]
              if let some i' ← isIH type ctx then
                withLocalDeclD (← mkFreshUserName `ih) (ihTypeToBelowType type ctx) fun newArg => do
                  let proof ← forallTelescope type fun args body => do
                    let proof := .app (body.updateFn newMinors[i']!) (mkAppN newArg args)
                    mkLambdaFVars args proof
                  go2 (j + 1) (vars.push newArg) ((args.push newArg).push proof)
              else
                go2 (j + 1) (vars.push minorArgs[j]) (args.push minorArgs[j])
            else
              let belowCtor := .const belowCtorName (ctx.indVal.levelParams.map Level.param)
              let proof := mkAppN (mkAppN (mkAppN belowCtor ctx.params) ctx.motives) args
              mkLambdaFVars vars proof
          termination_by minorArgs.size - j
          go2 0 #[] #[]
        recMinors := recMinors.push expr
      Lean.logInfo recMinors
      k newMinors (ctx.params ++ recMotives ++ recMinors)
  termination_by ctx.motives.size - i
  go 0 #[]

def mkBRecOn (ctx : Context) : MetaM Unit := do
  withBRecOnArgs (ctx := ctx) fun newMinors proofArgs => do
    let nmotives := ctx.motives.size
    let lparams := ctx.indVal.levelParams.map Level.param
    let lparams := if ctx.largeElim then levelZero :: lparams else lparams
    for i in *...nmotives do
      let motive := ctx.motives[i]!
      let motiveType ← inferType motive
      forallTelescope motiveType fun majors _ => do
        let lctx := majors.foldl (fun lctx var => lctx.setBinderInfo var.fvarId! .implicit)
          (← getLCtx) 0 (majors.size - 1)
        withLCtx' lctx do
          let recApp := mkAppN (mkAppN (.const ctx.recNames[i]! lparams) proofArgs) majors
          let proof := .app (mkAppN newMinors[i]! majors) recApp
          let type := mkAppN motive majors
          let vars := ctx.params ++ ctx.motives ++ majors ++ newMinors
          let proof ← mkLambdaFVars vars proof
          let type ← mkForallFVars vars type
          addDecl <| .thmDecl {
            name := ctx.brecOnNames[i]!
            levelParams := ctx.indVal.levelParams
            type := type
            value := proof
          }

/-- Generates the auxiliary lemmas `below` and `brecOn` for a recursive inductive predicate. -/
def mkBelow (indName : Name) : MetaM Unit :=
  withTraceNode `Meta.IndPredBelow (fun _ => return m!"{indName}") do
  let indVal ← getConstInfoInduct indName
  let recVal ← getConstInfoRec (indName ++ `rec)
  let largeElim := recVal.levelParams.length > indVal.levelParams.length
  let t := if largeElim then recVal.instantiateTypeLevelParams [.zero] else recVal.type
  let n := recVal.numParams + recVal.numMotives + recVal.numMinors
  forallBoundedTelescope t (some n) fun as _ => do
    let params := as.extract 0 recVal.numParams
    let motives := as.extract recVal.numParams (recVal.numParams + recVal.numMotives)
    let minors := as.extract (recVal.numParams + recVal.numMotives)
    let motiveToIdx := motives.zipIdx.foldl (init := ∅) fun a (e, n) => a.insert e.fvarId! n
    let recNames := indVal.all.toArray.map (· ++ `rec) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `rec).appendIndexAfter
    let belowNames := indVal.all.toArray.map (· ++ `below) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `below).appendIndexAfter
    let brecOnNames := indVal.all.toArray.map (· ++ `brecOn) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `brecOn).appendIndexAfter
    let ctx := { indVal, largeElim, params, motives, motiveToIdx, minors, recNames, belowNames, brecOnNames }
    mkBelowInductives ctx
    mkBRecOn ctx

builtin_initialize
  registerTraceClass `Meta.IndPredBelow

end Lean.Meta.IndPredBelow
