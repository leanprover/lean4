/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Robin Arnez
-/
module

prelude
public import Lean.Meta.Constructions.CasesOn
public import Lean.Meta.Match.Match
public import Lean.Meta.Tactic.SolveByElim

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

open Match

/-- Given a constructor name, find the indices of the corresponding `below` version thereof. -/
partial def getBelowIndices (ctorName : Name) : MetaM $ Array Nat := do
  let ctorInfo ← getConstInfoCtor ctorName
  let belowCtorInfo ← getConstInfoCtor (ctorName.updatePrefix $ ctorInfo.induct ++ `below)
  forallTelescopeReducing ctorInfo.type fun xs _ => do
  loop xs belowCtorInfo.type #[] 0 0

where
  loop
      (xs : Array Expr)
      (rest : Expr)
      (belowIndices : Array Nat)
      (xIdx yIdx : Nat) : MetaM $ Array Nat := do
    if h : xIdx ≥ xs.size then return belowIndices else
    let x := xs[xIdx]
    let xTy ← inferType x
    let yTy := rest.bindingDomain!
    if (← isDefEq xTy yTy) then
      let rest ← instantiateForall rest #[x]
      loop xs rest (belowIndices.push yIdx) (xIdx + 1) (yIdx + 1)
    else
      forallBoundedTelescope rest (some 1) fun _ rest =>
      loop xs rest belowIndices xIdx (yIdx + 1)

private def belowType (motive : Expr) (xs : Array Expr) (idx : Nat) : MetaM $ Name × Expr := do
  (← whnf (← inferType xs[idx]!)).withApp fun type args => do
    let indName := type.constName!
    let indInfo ← getConstInfoInduct indName
    let belowArgs := args[*...indInfo.numParams] ++ #[motive] ++ args[indInfo.numParams...*] ++ #[xs[idx]!]
    let belowType := mkAppN (mkConst (indName ++ `below) type.constLevels!) belowArgs
    return (indName, belowType)

/-- This function adds an additional `below` discriminant to a matcher application.
    It is used for modifying the patterns, such that the structural recursion can use the new
    `below` predicate instead of the original one and thus be used prove structural recursion.

    It takes as parameters:
    - matcherApp: a matcher application
    - belowMotive: the motive, that the `below` type should carry
    - below: an expression from the local context that is the `below` version of a predicate
             and can be used for structural recursion
    - idx: the index of the original predicate discriminant.

    It returns:
    - A matcher application as an expression
    - A side-effect for adding the matcher to the environment -/
partial def mkBelowMatcher
    (matcherApp : MatcherApp)
    (belowMotive : Expr)
    (below : Expr)
    (idx : Nat) : MetaM $ Expr × MetaM Unit := do
  let mkMatcherInput ← getMkMatcherInputInContext matcherApp
  let (indName, _, motive, matchType) ←
    forallBoundedTelescope mkMatcherInput.matchType mkMatcherInput.numDiscrs fun xs t => do
    let (indName, belowType) ← belowType belowMotive xs idx
    let matchType ←
      withLocalDeclD (←mkFreshUserName `h_below) belowType fun h_below => do
      mkForallFVars (xs.push h_below) t
    let motive ← newMotive belowType xs
    pure (indName, belowType.replaceFVars xs matcherApp.discrs, motive, matchType)

  let lhss ← mkMatcherInput.lhss.mapM <| addBelowPattern indName
  let alts ← mkMatcherInput.lhss.zip lhss |>.toArray.zip matcherApp.alts |>.mapIdxM fun idx ((oldLhs, lhs), alt) => do
    withExistingLocalDecls (oldLhs.fvarDecls ++ lhs.fvarDecls) do
    lambdaTelescope alt fun xs t => do
    let oldFVars := oldLhs.fvarDecls.toArray
    let fvars := lhs.fvarDecls.toArray.map (·.toExpr)
    let xs : Array Expr :=
      -- special case: if we had no free vars, i.e. there was a unit added and no we do have free vars, we get rid of the unit.
      match oldFVars.size, fvars.size with
      | 0, _+1 => xs[1...*].toArray
      | _, _ => xs
    let t := t.replaceFVars xs[*...oldFVars.size] fvars[*...oldFVars.size]
    trace[Meta.IndPredBelow.match] "xs = {xs}; oldFVars = {oldFVars.map (·.toExpr)}; fvars = {fvars}; new = {fvars[*...oldFVars.size] ++ xs[oldFVars.size...*] ++ fvars[oldFVars.size...*]}"
    let newAlt ← mkLambdaFVars (fvars[*...oldFVars.size] ++ xs[oldFVars.size...*] ++ fvars[oldFVars.size...*]) t
    trace[Meta.IndPredBelow.match] "alt {idx}:\n{alt} ↦ {newAlt}"
    pure newAlt

  let matcherName ← mkFreshUserName mkMatcherInput.matcherName
  withExistingLocalDecls (lhss.foldl (init := []) fun s v => s ++ v.fvarDecls) do
    for lhs in lhss do
      trace[Meta.IndPredBelow.match] "{lhs.patterns.map (·.toMessageData)}"
  let res ← Match.mkMatcher (exceptionIfContainsSorry := true) { matcherName, matchType, discrInfos := .replicate (mkMatcherInput.numDiscrs + 1) {}, lhss }
  res.addMatcher
  -- if a wrong index is picked, the resulting matcher can be type-incorrect.
  -- we check here, so that errors can propagate higher up the call stack.
  check res.matcher
  let newApp := mkApp res.matcher motive
  let newApp := mkAppN newApp <| matcherApp.discrs.push below
  let newApp := mkAppN newApp alts
  return (newApp, res.addMatcher)

where
  addBelowPattern (indName : Name) (lhs : AltLHS) : MetaM AltLHS := do
    withExistingLocalDecls lhs.fvarDecls do
    let patterns := lhs.patterns.toArray
    let originalPattern := patterns[idx]!
    let (fVars, belowPattern) ← convertToBelow indName patterns[idx]!
    withExistingLocalDecls fVars.toList do
    let patterns := patterns.push belowPattern
    let patterns := patterns.set! idx (←toInaccessible originalPattern)
    return { lhs with patterns := patterns.toList, fvarDecls := lhs.fvarDecls ++ fVars.toList }

  /--
    this function changes the type of the pattern from the original type to the `below` version thereof.
    Most of the cases don't apply. In order to change the type and the pattern to be type correct, we don't
    simply recursively change all occurrences, but rather, we recursively change occurrences of the constructor.
    As such there are only a few cases:
    - the pattern is a constructor from the original type. Here we need to:
      - replace the constructor
      - copy original recursive patterns and convert them to below and reintroduce them in the correct position
      - turn original recursive patterns inaccessible
      - introduce free variables as needed.
    - it is an `as` pattern. Here the constructor could be hidden inside of it.
    - it is a variable. Here you we need to introduce a fresh variable of a different type.
  -/
  convertToBelow (indName : Name)
      (originalPattern : Pattern) : MetaM $ Array LocalDecl × Pattern := do
    match originalPattern with
    | Pattern.ctor ctorName us params fields =>
      let ctorInfo ← getConstInfoCtor ctorName

      let belowCtor ← getConstInfoCtor $ ctorName.updatePrefix $ ctorInfo.induct ++ `below
      let belowIndices ← IndPredBelow.getBelowIndices ctorName
      let belowIndices := belowIndices[ctorInfo.numParams...*].toArray.map (· - belowCtor.numParams)

      -- belowFieldOpts starts off with an array of empty fields.
      -- We then go over pattern's fields and set the appropriate fields to values.
      -- In general, there are fewer `fields` than `belowFieldOpts`, because the
      -- `belowCtor` carries a `below`, a non-`below` and a `motive` version of each
      -- field that occurs in a recursive application of the inductive predicate.
      -- `belowIndices` is a mapping from non-`below` to the `below` version of each field.
      let mut belowFieldOpts := .replicate belowCtor.numFields none
      let fields := fields.toArray
      for fieldIdx in *...fields.size do
        belowFieldOpts := belowFieldOpts.set! belowIndices[fieldIdx]! (some fields[fieldIdx]!)

      let belowParams := params.toArray.push belowMotive
      let belowCtorExpr := mkAppN (mkConst belowCtor.name us) belowParams
      let (additionalFVars, belowFields) ← transformFields belowCtorExpr indName belowFieldOpts

      withExistingLocalDecls additionalFVars.toList do
      let ctor := Pattern.ctor belowCtor.name us belowParams.toList belowFields.toList
      trace[Meta.IndPredBelow.match] "{originalPattern.toMessageData} ↦ {ctor.toMessageData}"
      return (additionalFVars, ctor)
    | Pattern.as varId p hId =>
      let (additionalFVars, p) ← convertToBelow indName p
      return (additionalFVars, Pattern.as varId p hId)
    | Pattern.var varId =>
      let var := mkFVar varId
      let (_, tgtType) ← belowType belowMotive #[var] 0
      withLocalDeclD (←mkFreshUserName `h) tgtType fun h => do
      let localDecl ← getFVarLocalDecl h
      return (#[localDecl], Pattern.var h.fvarId!)
    | p => return (#[], p)

  transformFields belowCtor indName belowFieldOpts :=
    let rec loop
      (belowCtor : Expr)
      (belowFieldOpts : Array $ Option Pattern)
      (belowFields : Array Pattern)
      (additionalFVars : Array LocalDecl) : MetaM (Array LocalDecl × Array Pattern) := do
      if belowFields.size ≥ belowFieldOpts.size then pure (additionalFVars, belowFields) else
      if let some belowField := belowFieldOpts[belowFields.size]! then
        let belowFieldExpr ← belowField.toExpr
        let belowCtor := mkApp belowCtor belowFieldExpr
        let patTy ← inferType belowFieldExpr
        patTy.withApp fun f _ => do
        let constName := f.constName?
        if constName == indName then
          let (fvars, transformedField) ← convertToBelow indName belowField
          withExistingLocalDecls fvars.toList do
          let belowFieldOpts := belowFieldOpts.set! (belowFields.size + 1) transformedField
          let belowField :=
            match belowField with
            | Pattern.ctor .. => Pattern.inaccessible belowFieldExpr
            | _ => belowField
          loop belowCtor belowFieldOpts (belowFields.push belowField) (additionalFVars ++ fvars)
        else
          loop belowCtor belowFieldOpts (belowFields.push belowField) additionalFVars
      else
        let ctorType ← inferType belowCtor
        withLocalDeclD (←mkFreshUserName `a) ctorType.bindingDomain! fun a => do
        let localDecl ← getFVarLocalDecl a
        loop (mkApp belowCtor a) belowFieldOpts (belowFields.push $ Pattern.var a.fvarId!) (additionalFVars.push localDecl)
    loop belowCtor belowFieldOpts #[] #[]

  toInaccessible : Pattern → MetaM Pattern
  | Pattern.inaccessible p => return Pattern.inaccessible p
  | Pattern.var v => return Pattern.var v
  | p => return Pattern.inaccessible $ ←p.toExpr

  newMotive (belowType : Expr) (ys : Array Expr) : MetaM Expr :=
    lambdaTelescope matcherApp.motive fun xs t => do
    let numDiscrs := matcherApp.discrs.size
    withLocalDeclD (←mkFreshUserName `h_below) (belowType.replaceFVars ys xs) fun h_below => do
    let motive ← mkLambdaFVars (xs[*...numDiscrs] ++ #[h_below] ++ xs[numDiscrs...*]) t
    trace[Meta.IndPredBelow.match] "motive := {motive}"
    return motive

def findBelowIdx (xs : Array Expr) (motive : Expr) : MetaM $ Option (Expr × Nat) := do
  xs.findSomeM? fun x => do
  (← whnf (← inferType x)).withApp fun f _ =>
  match f.constName?, xs.idxOf? x with
  | some name, some idx => do
    if (← getEnv).contains (name ++ `below) && (← isInductivePredicate name) then
      let (_, belowTy) ← belowType motive xs idx
      let below ← mkFreshExprSyntheticOpaqueMVar belowTy
      try
        trace[Meta.IndPredBelow.match] "{below.mvarId!}"
        if (← below.mvarId!.applyRules { backtracking := false, maxDepth := 1 } []).isEmpty then
          trace[Meta.IndPredBelow.match] "Found below term in the local context: {below}"
          if (← xs.anyM (isDefEq below)) then pure none else pure (below, idx)
        else
          trace[Meta.IndPredBelow.match] "could not find below term in the local context"
          pure none
      catch _ => pure none
    else pure none
  | _, _ => pure none

/-- Generates the auxiliary lemmas `below` and `brecOn` for a recursive inductive predicate. -/
def mkBelow (indName : Name) : MetaM Unit :=
  withTraceNode `Meta.IndPredBelow (fun _ => return m!"{indName}") do
  unless (← isInductivePredicate indName) do return
  let indVal ← getConstInfoInduct indName
  unless indVal.isRec do return
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
