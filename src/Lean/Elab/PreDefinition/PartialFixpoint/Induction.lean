/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
import Lean.Meta.Injective -- for elimOptParam
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import Init.Internal.Order.Basic
import Lean.Meta.PProdN

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

/--
Unfolds an appropriate `PartialOrder` instance on predicates to quantifications and implications.
I.e. `ImplicationOrder.instPartialOrder.rel P Q` becomes
`∀ x y, P x y → Q x y`.
In the premise of the Park induction principle (`lfp_le_of_le_monotone`) we use a monotone map defining the predicate in the eta expanded form. In such a case, besides desugaring the predicate, we need to perform a weak head reduction.
The optional parameter `reducePremise` (false by default) indicates whether we need to perform this reduction.
-/
def unfoldPredRel (predType : Expr) (lhs rhs : Expr) (fixpointType : PartialFixpointType) (reducePremise : Bool := false) : MetaM Expr := do
  guard <| isLatticeTheoretic fixpointType
  forallTelescopeReducing predType fun ts _ => do
    let mut lhs : Expr := mkAppN lhs ts
    let rhs : Expr := mkAppN rhs ts
    if reducePremise then
        lhs ← whnf lhs
    match fixpointType with
    | .inductiveFixpoint =>
      mkForallFVars ts (←mkArrow lhs rhs)
    | .coinductiveFixpoint =>
      mkForallFVars ts (←mkArrow rhs lhs)
    | .partialFixpoint => throwError "Cannot apply lattice induction to a non-lattice fixpoint"
/--
Unfolds a PartialOrder relation between tuples of predicates into an array of quantified implications.

This function handles mutual recursion cases where we have a tuple of predicates being compared. For each predicate in the tuple it projects out the corresponding components from both sides of the relation and unfolds the partial order relation into quantified implications using `unfoldPredRel`

Parameters:
- `eqnInfo`: Equation information containing declaration names and fixpoint types for each predicate in the mutual block
- `body`: The partial order relation expression to unfold
- `reduceConclusion`: Optional parameter (defaults to false) that determines whether to perform weak head normalization on the conclusion

Returns:
An array of expressions, where each element represents the unfolded implication for the corresponding predicate in the mutual block.
-/
def unfoldPredRelMutual (eqnInfo : EqnInfo) (body : Expr) (reduceConclusion : Bool := false) : MetaM (Array Expr) := do
  let_expr Lean.Order.PartialOrder.rel α _ lhs rhs := body
    | throwError "{body} is not an application of partial order"
  let infos ← eqnInfo.declNames.mapM getConstInfoDefn
  -- We get types of each of the predicates in the tuple
  let predTypes ← PProdN.unpack α infos.size
  trace[Elab.definition.partialFixpoint.induction] "predTypes: {predTypes}"
  -- We unfold the order for each of the elements of the tuple independently
  infos.mapIdxM fun i _ => do
    let lhs ← PProdN.reduceProjs (←PProdN.projM infos.size i lhs)
    unfoldPredRel predTypes[i]! lhs (← PProdN.projM infos.size i rhs) eqnInfo.fixpointType[i]! reduceConclusion

/-- `maskArray mask xs` keeps those `x` where the corresponding entry in `mask` is `true` -/
-- Worth having in the standard library?
private def maskArray {α} (mask : Array Bool) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for b in mask, x in xs do
    if b then ys := ys.push x
  return ys

/-- Appends `_1` etc to `base` unless `n == 1` -/
private def numberNames (n : Nat) (base : String) : Array Name :=
  .ofFn (n := n) fun ⟨i, _⟩ =>
    if n == 1 then .mkSimple base else .mkSimple s!"{base}_{i+1}"

def getInductionPrinciplePostfix (name : Name) (isMutual : Bool) : MetaM Name := do
  let some eqnInfo := eqnInfoExt.find? (← getEnv) name | throwError "{name} is not defined by partial_fixpoint, inductive_fixpoint, nor coinductive_fixpoint"
  let idx := eqnInfo.declNames.idxOf name
  let some res := eqnInfo.fixpointType[idx]? | throwError "Cannot get fixpoint type for {name}"
  match res, isMutual with
  | .partialFixpoint, false => return `fixpoint_induct
  | .inductiveFixpoint, false => return `induct
  | .coinductiveFixpoint, false => return `coinduct
  | .partialFixpoint, true => return `mutual_fixpoint_induct
  | _, true => return `mutual_induct

def deriveInduction (name : Name) (isMutual : Bool) : MetaM Unit := do
  let postFix ← getInductionPrinciplePostfix name isMutual
  let inductName := name ++ postFix
  realizeConst name inductName do
  trace[Elab.definition.partialFixpoint] "Called deriveInduction for {inductName}"
  prependError m!"Cannot derive fixpoint induction principle (please report this issue)" do
    let some eqnInfo := eqnInfoExt.find? (← getEnv) name |
      throwError "{name} is not defined by partial_fixpoint"
    let infos ← eqnInfo.declNames.mapM getConstInfoDefn
    let e' ← eqnInfo.fixedParamPerms.perms[0]!.forallTelescope infos[0]!.type fun xs => do
      -- Now look at the body of an arbitrary of the functions (they are essentially the same
      -- up to the final projections)
      let body ← eqnInfo.fixedParamPerms.perms[0]!.instantiateLambda infos[0]!.value xs
      -- The body should now be of the form of the form (fix … ).2.2.1
      -- We strip the projections (if present)
      let body' := PProdN.stripProjs body.eta -- TODO: Eta more carefully?
      if eqnInfo.fixpointType.all isLatticeTheoretic then
        -- We strip it until we reach an application of `lfp_montotone`
        let some fixApp ← whnfUntil body' ``lfp_monotone
          | throwError "Unexpected function body {body}, could not whnfUntil lfp_monotone"
        let_expr lfp_monotone α instcomplete_lattice F hmono := fixApp
          | throwError "Unexpected function body {body}, not an application of lfp_monotone"
        let e' ← mkAppOptM ``lfp_le_of_le_monotone #[α, instcomplete_lattice, F, hmono]
        -- All definitions from `mutual` block as PProdN
        let packedConclusion ← PProdN.mk 1 <| ← infos.mapIdxM fun i defVal => do
          let f ← mkConstWithLevelParams defVal.name
          let fEtaExpanded ← lambdaTelescope defVal.value fun ys _ =>
            mkLambdaFVars ys (mkAppN f ys)
            let fInst ← eqnInfo.fixedParamPerms.perms[i]!.instantiateLambda fEtaExpanded xs
            return fInst.eta
        -- We get the type of the induction principle
        let eTyp ← inferType e'
        -- And unfold the conclusion, upon replacing references to the fixpoint theorem with the defined functions
        let eTyp ← forallTelescope eTyp fun args body => do
          let_expr PartialOrder.rel α pord _ pred := body
            | throwError "Unexpected function type {body}, not an application of PartialOrder.rel"
          let newBody ← mkAppOptM ``PartialOrder.rel #[α, pord, packedConclusion, pred]
          let unfolded ← unfoldPredRelMutual eqnInfo newBody
          let newBody ← PProdN.pack 0 unfolded
          mkForallFVars args newBody
        let e' ← mkExpectedTypeHint e' eTyp
        -- We obtain the premises of (co)induction proof principle
        let motives ← forallTelescope eTyp fun args _ => do
          let motives ← unfoldPredRelMutual eqnInfo (←inferType args[1]!) (reduceConclusion := true)
          motives.mapM (fun x => mkForallFVars #[args[0]!] x)
        -- For each predicate in the mutual group we generate an appropriate candidate predicate
        let predicates := (numberNames infos.size "pred").zip <| ← PProdN.unpack α infos.size
        -- Then we make the induction principle more readable, by currying the hypotheses and projecting the conclusion
        withLocalDeclsDND predicates fun predVars => do
          -- A joint approximation to the fixpoint
          let predVar ← PProdN.mk 0 predVars
          -- All motives get instantiated with the newly created variables
          let newMotives ← motives.mapM (instantiateForall · #[predVar])
          let newMotives ← newMotives.mapM (PProdN.reduceProjs ·)
          -- Then, we introduce hypotheses
          withLocalDeclsDND ((numberNames infos.size "hyp").zip newMotives) fun motiveVars => do
            let e' := mkApp e' predVar
            let eTyp ← inferType e'
            -- Conclusion gets cleaned up from `PProd` projections
            let e' ← mkExpectedTypeHint e' (← PProdN.reduceProjs eTyp)
            -- We apply all the premises
            let packedPremise ← PProdN.mk 0 motiveVars
            let e' := mkApp e' packedPremise
            -- For the `mutual_induct` variant, we are done.
            -- Else, project out the appropriate element
            let e' ← if isMutual then
                pure e'
              else
                PProdN.projM infos.size (eqnInfo.declNames.idxOf name) e'
            -- Finally, we bind all the free variables with lambdas
            let e' ← mkLambdaFVars motiveVars e'
            let e' ← mkLambdaFVars predVars e'
            let e' ← mkLambdaFVars (binderInfoForMVars := .default) (usedOnly := true) xs e'
            let e' ← instantiateMVars e'
            trace[Elab.definition.partialFixpoint.induction] "Complete body of fixpoint induction principle:{indentExpr e'}"
            pure e'
      else
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
              trace[Elab.definition.partialFixpoint.induction] "packedConclusion: {packedConclusion}, index is: {(eqnInfo.declNames.idxOf name)}"
              let e' ← mkExpectedTypeHint e' packedConclusion
              let e' ← if isMutual then
                pure e'
              else
                PProdN.projM infos.size (eqnInfo.declNames.idxOf name) e'
              let e' ← mkLambdaFVars hs e'
              let e' ← mkLambdaFVars adms e'
              let e' ← mkLambdaFVars motives e'
              let e' ← mkLambdaFVars (binderInfoForMVars := .default) (usedOnly := true) xs e'
              let e' ← instantiateMVars e'
              trace[Elab.definition.partialFixpoint.induction] "Complete body of fixpoint induction principle:{indentExpr e'}"
              pure e'
    let eTyp ← inferType e'
    trace[Elab.definition.partialFixpoint.induction] "eTyp last: {eTyp}"
    let eTyp ← elimOptParam eTyp
    -- logInfo m!"eTyp: {eTyp}"
    let params := (collectLevelParams {} eTyp).params
    -- Prune unused level parameters, preserving the original order
    let us := infos[0]!.levelParams.filter (params.contains ·)

    addDecl <| (←mkThmOrUnsafeDef { name := inductName, levelParams := us, type := eTyp, value := e' })

def isInductName (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "fixpoint_induct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      return eqnInfo.fixpointType.all isPartialFixpoint
    return false
  | "coinduct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      let idx := eqnInfo.declNames.idxOf p
      return isCoinductiveFixpoint eqnInfo.fixpointType[idx]!
    return false
  | "induct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      let idx := eqnInfo.declNames.idxOf p
      return isInductiveFixpoint eqnInfo.fixpointType[idx]!
    return false
  | "mutual_induct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      return eqnInfo.declNames[0]! == p && eqnInfo.declNames.size > 1 && eqnInfo.fixpointType.all isLatticeTheoretic
    return false
  | "mutual_fixpoint_induct" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      return eqnInfo.declNames[0]! == p && eqnInfo.declNames.size > 1 && eqnInfo.fixpointType.all isPartialFixpoint
    return false
  | _ => return false

builtin_initialize
  registerReservedNamePredicate isInductName

  registerReservedNameAction fun name => do
    if isInductName (← getEnv) name then
      let .str p s := name | return false
      let isMutual := s.endsWith "mutual_induct" || s.endsWith "mutual_fixpoint_induct"
      MetaM.run' <| deriveInduction p isMutual
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
  match s with
  | "partial_correctness" => return isOptionFixpoint env p
  | "mutual_partial_correctness" =>
    if let some eqnInfo := eqnInfoExt.find? env p then
      return eqnInfo.declNames[0]! == p && isOptionFixpoint env p && eqnInfo.declNames.size > 1
    return false
  | _ => return false

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
      inst ← mkAppOptM ``Order.admissible_pi_apply #[none, none, none, none, inst]
    pure inst

def derivePartialCorrectness (name : Name) (isConclusionMutual : Bool) : MetaM Unit := do
  let inductName := name ++ if isConclusionMutual then `mutual_partial_correctness else `partial_correctness
  realizeConst name inductName do
  let fixpointInductThm := name ++ if isConclusionMutual then `mutual_fixpoint_induct else `fixpoint_induct
  unless (← getEnv).contains fixpointInductThm do
    deriveInduction name isConclusionMutual

  prependError m!"Cannot derive partial correctness theorem (please report this issue)" do
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
        -- the motives, as expected by `f.mutual_induct`:
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
    unless s == "partial_correctness" || s == "mutual_partial_correctness" do return false
    unless isOptionFixpoint (← getEnv) p do return false
    MetaM.run' <| derivePartialCorrectness p (s.startsWith "mutual")
    return false

end Lean.Elab.PartialFixpoint

builtin_initialize Lean.registerTraceClass `Elab.definition.partialFixpoint.induction
