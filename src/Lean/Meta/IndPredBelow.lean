/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

import Lean.Meta.Constructions
import Lean.Meta.Transform
import Lean.Meta.Tactic
import Lean.Meta.Match.Match
import Lean.Meta.Reduce

namespace Lean.Meta.IndPredBelow
open Match

register_builtin_option maxBackwardChainingDepth : Nat := {
    defValue := 10
    descr    := "The maximum search depth used in the backwards chaining part of the proof of `brecOn` for inductive predicates."
  }

/--
  The context used in the creation of the `below` scheme for inductive predicates.
-/
structure Context where
  motives : Array (Name × Expr)
  typeInfos : Array InductiveVal
  belowNames : Array Name
  headers : Array Expr
  numParams : Nat

/--
  Collection of variables used to keep track of the positions of binders in the construction
  of `below` motives and constructors.
-/
structure Variables where
  target : Array Expr
  indVal : Array Expr
  params : Array Expr
  args : Array Expr
  motives : Array Expr
  innerType : Expr
  deriving Inhabited

/--
  Collection of variables used to keep track of the local context used in the `brecOn` proof.
-/
structure BrecOnVariables where
  params : Array FVarId
  motives : Array FVarId
  indices : Array FVarId
  witness : FVarId
  indHyps : Array FVarId

def mkContext (declName : Name) : MetaM Context := do
  let indVal ← getConstInfoInduct declName
  let typeInfos ← indVal.all.toArray.mapM getConstInfoInduct
  let motiveTypes ← typeInfos.mapM motiveType
  let motives ←motiveTypes.mapIdxM fun j motive => do
    (←motiveName motiveTypes j.val, motive)
  let headers := typeInfos.mapM $ mkHeader motives indVal.numParams
  return {
    motives := motives
    typeInfos := typeInfos
    numParams := indVal.numParams
    headers := ←headers
    belowNames := ←indVal.all.toArray.map (· ++ `below) }
where
  motiveName (motiveTypes : Array Expr) (i : Nat) : MetaM Name :=
    if motiveTypes.size > 1
    then mkFreshUserName s!"motive_{i.succ}"
    else mkFreshUserName "motive"

  mkHeader
      (motives : Array (Name × Expr))
      (numParams : Nat)
      (indVal : InductiveVal) : MetaM Expr := do
    let header ← forallTelescope indVal.type fun xs t => do
      withNewBinderInfos (xs.map fun x => (x.fvarId!, BinderInfo.implicit)) $
      mkForallFVars xs $ ←mkArrow (mkAppN (mkIndValConst indVal) xs) t
    addMotives motives numParams header

  addMotives (motives : Array (Name × Expr)) (numParams : Nat) : Expr → MetaM Expr :=
    motives.foldrM (fun (motiveName, motive) t =>
      forallTelescope t fun xs s => do
        let motiveType ← instantiateForall motive xs[:numParams]
        withLocalDecl motiveName BinderInfo.implicit motiveType fun motive => do
          mkForallFVars (xs.insertAt numParams motive) s)

  motiveType (indVal : InductiveVal) : MetaM Expr :=
    forallTelescope indVal.type fun xs t => do
      mkForallFVars xs $ ←mkArrow (mkAppN (mkIndValConst indVal) xs) (mkSort levelZero)

  mkIndValConst (indVal : InductiveVal) : Expr :=
    mkConst indVal.name $ indVal.levelParams.map mkLevelParam

partial def mkCtorType
    (ctx : Context)
    (belowIdx : Nat)
    (originalCtor : ConstructorVal) : MetaM Expr :=
  forallTelescope originalCtor.type fun xs t => addHeaderVars
    { innerType := t
      indVal := #[]
      motives := #[]
      params := xs[:ctx.numParams]
      args := xs[ctx.numParams:]
      target := xs[:ctx.numParams] }
where
  addHeaderVars (vars : Variables) := do
    let headersWithNames ← ctx.headers.mapIdxM fun idx header =>
      (ctx.belowNames[idx], fun _ : Array Expr => pure header)

    withLocalDeclsD headersWithNames fun xs =>
      addMotives { vars with indVal := xs }

  addMotives (vars : Variables) := do
    let motiveBuilders ← ctx.motives.mapM fun (motiveName, motiveType) =>
      (motiveName, BinderInfo.implicit, fun _ : Array Expr =>
        instantiateForall motiveType vars.params)
    withLocalDecls motiveBuilders fun xs =>
      modifyBinders { vars with target := vars.target ++ xs, motives := xs } 0

  modifyBinders (vars : Variables) (i : Nat) := do
    if i < vars.args.size then
      let binder := vars.args[i]
      let binderType ←inferType binder
      if ←checkCount binderType then
        mkBelowBinder vars binder binderType fun indValIdx x =>
          mkMotiveBinder vars indValIdx binder binderType fun y =>
            withNewBinderInfos #[(binder.fvarId!, BinderInfo.implicit)] do
            modifyBinders { vars with target := vars.target ++ #[binder, x, y]} i.succ
      else modifyBinders { vars with target := vars.target.push binder } i.succ
    else rebuild vars

  rebuild (vars : Variables) :=
    vars.innerType.withApp fun f args => do
      let hApp :=
        mkAppN
          (mkConst originalCtor.name $ ctx.typeInfos[0].levelParams.map mkLevelParam)
          (vars.params ++ vars.args)
      let innerType := mkAppN vars.indVal[belowIdx] $
        vars.params ++ vars.motives ++ args[ctx.numParams:] ++ #[hApp]
      let x ← mkForallFVars vars.target innerType
      replaceTempVars vars x

  replaceTempVars (vars : Variables) (ctor : Expr) :=
    let levelParams :=
      ctx.typeInfos[0].levelParams.map mkLevelParam

    ctor.replaceFVars vars.indVal $ ctx.belowNames.map fun indVal =>
      mkConst indVal levelParams

  checkCount (domain : Expr) : MetaM Bool := do
    let run (x : StateRefT Nat MetaM Expr) : MetaM (Expr × Nat) := StateRefT'.run x 0
    let (_, cnt) ←run $ transform domain fun e => do
      if let some name := e.constName? then
        if let some idx := ctx.typeInfos.findIdx? fun indVal => indVal.name == name then
          let cnt ←get
          set $ cnt + 1
      TransformStep.visit e

    if cnt > 1 then
      throwError "only arrows are allowed as premises. Multiple recursive occurrences detected:{indentExpr domain}"

    return cnt == 1

  mkBelowBinder
      (vars : Variables)
      (binder : Expr)
      (domain : Expr)
      {α : Type} (k : Nat → Expr → MetaM α) : MetaM α := do
    forallTelescope domain fun xs t => do
      let fail _ := do
        throwError "only trivial inductive applications supported in premises:{indentExpr t}"

      t.withApp fun f args => do
        if let some name := f.constName? then
          if let some idx := ctx.typeInfos.findIdx?
            fun indVal => indVal.name == name then
            let indVal := ctx.typeInfos[idx]
            let hApp := mkAppN binder xs
            let t :=
              mkAppN vars.indVal[idx] $
                vars.params ++ vars.motives ++ args[ctx.numParams:] ++ #[hApp]
            let newDomain ← mkForallFVars xs t

            withLocalDecl (←copyVarName binder.fvarId!) binder.binderInfo newDomain (k idx)
          else fail ()
        else fail ()

  mkMotiveBinder
      (vars : Variables)
      (indValIdx : Nat)
      (binder : Expr)
      (domain : Expr)
      {α : Type} (k : Expr → MetaM α) : MetaM α := do
    forallTelescope domain fun xs t => do
      t.withApp fun f args => do
        let hApp := mkAppN binder xs
        let t := mkAppN vars.motives[indValIdx] $ args[ctx.numParams:] ++ #[hApp]
        let newDomain ← mkForallFVars xs t

        withLocalDecl (←copyVarName binder.fvarId!) binder.binderInfo newDomain k

  copyVarName (oldName : FVarId) : MetaM Name := do
    let binderDecl ← getLocalDecl oldName
    mkFreshUserName binderDecl.userName

def mkConstructor (ctx : Context) (i : Nat) (ctor : Name) : MetaM Constructor := do
  let ctorInfo ← getConstInfoCtor ctor
  let name := ctor.updatePrefix ctx.belowNames[i]
  let type ← mkCtorType ctx i ctorInfo
  return {
    name := name
    type := type }

def mkInductiveType
    (ctx : Context)
    (i : Fin ctx.typeInfos.size)
    (indVal : InductiveVal) : MetaM InductiveType := do
  return {
    name := ctx.belowNames[i]
    type := ctx.headers[i]
    ctors := ←indVal.ctors.mapM (mkConstructor ctx i) }

def mkBelowDecl (ctx : Context) : MetaM Declaration := do
  let lparams := ctx.typeInfos[0].levelParams
  Declaration.inductDecl
    lparams
    (ctx.numParams + ctx.motives.size)
    (←ctx.typeInfos.mapIdxM $ mkInductiveType ctx).toList
    ctx.typeInfos[0].isUnsafe

partial def backwardsChaining (m : MVarId) (depth : Nat) : MetaM Bool := do
  if depth = 0 then false
  else
    withMVarContext m do
    let lctx ← getLCtx
    let mTy ← getMVarType m
    lctx.anyM fun localDecl =>
      if localDecl.isAuxDecl then
        false
      else
        commitWhen do
        let (mvars, _, t) ← forallMetaTelescope localDecl.type
        if ←isDefEq mTy t then
          assignExprMVar m (mkAppN localDecl.toExpr mvars)
          mvars.allM fun v =>
            isExprMVarAssigned v.mvarId! <||> backwardsChaining v.mvarId! (depth - 1)
        else false

partial def proveBrecOn (ctx : Context) (indVal : InductiveVal) (type : Expr) : MetaM Expr := do
  let main ← mkFreshExprSyntheticOpaqueMVar type
  let (m, vars) ← intros main.mvarId!
  let [m] ← applyIH m vars |
    throwError "applying the induction hypothesis should only return one goal"
  let ms ← induction m vars
  let ms ← applyCtors ms
  let maxDepth := maxBackwardChainingDepth.get $ ←getOptions
  ms.forM (closeGoal vars maxDepth)
  instantiateMVars main
where
  intros (m : MVarId) : MetaM (MVarId × BrecOnVariables) := do
    let (params, m) ← introNP m indVal.numParams
    let (motives, m) ← introNP m ctx.motives.size
    let (indices, m) ← introNP m indVal.numIndices
    let (witness, m) ← intro1P m
    let (indHyps, m) ← introNP m ctx.motives.size
    return (m, ⟨params, motives, indices, witness, indHyps⟩)

  applyIH (m : MVarId) (vars : BrecOnVariables) : MetaM (List MVarId) := do
    match ←vars.indHyps.findSomeM?
      (fun ih => do try some $ (←apply m $ mkFVar ih) catch ex => none) with
    | some goals => goals
    | none => throwError "cannot apply induction hypothesis: {MessageData.ofGoal m}"

  induction (m : MVarId) (vars : BrecOnVariables) : MetaM (List MVarId) := do
    let params := vars.params.map mkFVar
    let motives := vars.motives.map mkFVar
    let levelParams := indVal.levelParams.map mkLevelParam
    let motives ← ctx.motives.mapIdxM fun idx (_, motive) => do
      let motive ← instantiateForall motive params
      forallTelescope motive fun xs _ => do
      mkLambdaFVars xs $ mkAppN (mkConst ctx.belowNames[idx] levelParams) $ (params ++ motives ++ xs)
    let recursorInfo ← getConstInfo $ mkRecName indVal.name
    let recLevels :=
      if recursorInfo.numLevelParams > levelParams.length
      then levelZero::levelParams
      else levelParams
    let recursor ← mkAppN (mkConst recursorInfo.name $ recLevels) $ params ++ motives
    apply m recursor

  applyCtors (ms : List MVarId) : MetaM $ List MVarId := do
    let mss ← ms.toArray.mapIdxM fun idx m => do
      let m ← introNPRec m
      (←getMVarType m).withApp fun below args =>
      withMVarContext m do
      args.back.withApp fun ctor ctorArgs => do
      let ctorName := ctor.constName!.updatePrefix below.constName!
      let ctor := mkConst ctorName below.constLevels!
      let ctorInfo ← getConstInfoCtor ctorName
      let (mvars, _, t) ← forallMetaTelescope ctorInfo.type
      let ctor := mkAppN ctor mvars
      apply m ctor
    return mss.foldr List.append []

  introNPRec (m : MVarId) : MetaM MVarId := do
    if (←getMVarType m).isForall then introNPRec (←intro1P m).2 else m

  closeGoal (vars : BrecOnVariables) (maxDepth : Nat) (m : MVarId) : MetaM Unit := do
    unless ←isExprMVarAssigned m do
      let m ← introNPRec m
      unless ←backwardsChaining m maxDepth do
        withMVarContext m do
        throwError "couldn't solve by backwards chaining ({``maxBackwardChainingDepth} = {maxDepth}): {MessageData.ofGoal m}"

def mkBrecOnDecl (ctx : Context) (idx : Nat) : MetaM Declaration := do
  let type ← mkType
  let indVal := ctx.typeInfos[idx]
  let name := indVal.name ++ brecOnSuffix
  Declaration.thmDecl {
    name := name
    levelParams := indVal.levelParams
    type := type
    value := ←proveBrecOn ctx indVal type }
where
  mkType : MetaM Expr :=
    forallTelescope ctx.headers[idx] fun xs t => do
    let params := xs[:ctx.numParams]
    let motives := xs[ctx.numParams:ctx.numParams + ctx.motives.size].toArray
    let indices := xs[ctx.numParams + ctx.motives.size:]
    let motiveBinders ← ctx.motives.mapIdxM $ mkIH params motives
    withLocalDeclsD motiveBinders fun ys => do
    mkForallFVars (xs ++ ys) (mkAppN motives[idx] indices)
  mkIH
      (params : Array Expr)
      (motives : Array Expr)
      (idx : Fin ctx.motives.size)
      (motive : Name × Expr) : MetaM $ Name × (Array Expr → MetaM Expr) := do
    let name :=
      if ctx.motives.size > 1
      then mkFreshUserName s!"ih_{idx.val.succ}"
      else mkFreshUserName "ih"
    let ih ← instantiateForall motive.2 params
    let mkDomain (_ : Array Expr) : MetaM Expr :=
      forallTelescope ih fun ys t => do
        let levels := ctx.typeInfos[idx].levelParams.map mkLevelParam
        let args := params ++ motives ++ ys
        let premise :=
          mkAppN
            (mkConst ctx.belowNames[idx.val] levels) args
        let conclusion :=
          mkAppN motives[idx] ys
        mkForallFVars ys (←mkArrow premise conclusion)
    (←name, mkDomain)

/-- Given a constructor name, find the indices of the corresponding `below` version thereof. -/
partial def getBelowIndices (ctorName : Name) : MetaM $ Array Nat := do
  let ctorInfo ← getConstInfoCtor ctorName
  let belowCtorInfo ← getConstInfoCtor (ctorName.updatePrefix $ ctorInfo.induct ++ `below)
  let belowInductInfo ← getConstInfoInduct belowCtorInfo.induct
  forallTelescope ctorInfo.type fun xs t => do
  loop xs belowCtorInfo.type #[] 0 0

where
  loop
      (xs : Array Expr)
      (rest : Expr)
      (belowIndices : Array Nat)
      (xIdx yIdx : Nat) : MetaM $ Array Nat := do
    if xIdx ≥ xs.size then belowIndices else
    let x := xs[xIdx]
    let xTy ← inferType x
    let yTy := rest.bindingDomain!
    if ←isDefEq xTy yTy then
      let rest ← instantiateForall rest #[x]
      loop xs rest (belowIndices.push yIdx) (xIdx + 1) (yIdx + 1)
    else
      forallBoundedTelescope rest (some 1) fun ys rest =>
      loop xs rest belowIndices xIdx (yIdx + 1)

private def belowType (motive : Expr) (xs : Array Expr) (idx : Nat) : MetaM $ Name × Expr := do
  (←inferType xs[idx]).withApp fun type args => do
  let indName := type.constName!
  let indInfo ← getConstInfoInduct indName
  let belowArgs := args[:indInfo.numParams] ++ #[motive] ++ args[indInfo.numParams:] ++ #[xs[idx]]
  let belowType := mkAppN (mkConst (indName ++ `below) type.constLevels!) belowArgs
  (indName, belowType)

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
  let (indName, belowType, motive, matchType) ←
    forallBoundedTelescope mkMatcherInput.matchType mkMatcherInput.numDiscrs fun xs t => do
    let (indName, belowType) ← belowType belowMotive xs idx
    let matchType ←
      withLocalDeclD (←mkFreshUserName `h_below) belowType fun h_below => do
      mkForallFVars (xs.push h_below) t
    let motive ← newMotive belowType xs
    (indName, belowType.replaceFVars xs matcherApp.discrs, motive, matchType)

  let lhss ← mkMatcherInput.lhss.mapM $ addBelowPattern indName
  let alts ← mkMatcherInput.lhss.zip lhss |>.toArray.zip matcherApp.alts |>.mapIdxM fun idx ((oldLhs, lhs), alt) => do
    withExistingLocalDecls (oldLhs.fvarDecls ++ lhs.fvarDecls) do
    lambdaTelescope alt fun xs t => do
    let oldFVars := oldLhs.fvarDecls.toArray
    let fvars := lhs.fvarDecls.toArray.map (·.toExpr)
    let xs :=
      -- special case: if we had no free vars, i.e. there was a unit added and no we do have free vars, we get rid of the unit.
      match oldFVars.size, fvars.size with
      | 0, n+1 => xs[1:]
      | _, _ => xs
    let t := t.replaceFVars xs[:oldFVars.size] fvars[:oldFVars.size]
    trace[Meta.IndPredBelow.match] "xs = {xs}; oldFVars = {oldFVars.map (·.toExpr)}; fvars = {fvars}; new = {fvars[:oldFVars.size] ++ xs[oldFVars.size:] ++ fvars[oldFVars.size:]}"
    let newAlt ← mkLambdaFVars (fvars[:oldFVars.size] ++ xs[oldFVars.size:] ++ fvars[oldFVars.size:]) t
    trace[Meta.IndPredBelow.match] "alt {idx}:\n{alt} ↦ {newAlt}"
    newAlt

  let matcherName ← mkFreshUserName mkMatcherInput.matcherName
  withExistingLocalDecls (lhss.foldl (init := []) fun s v => s ++ v.fvarDecls) do
    for lhs in lhss do
      trace[Meta.IndPredBelow.match] "{←lhs.patterns.mapM (·.toMessageData)}"
  let res ← Match.mkMatcher { matcherName, matchType, numDiscrs := (mkMatcherInput.numDiscrs + 1), lhss }
  res.addMatcher
  -- if a wrong index is picked, the resulting matcher can be type-incorrect.
  -- we check here, so that errors can propagate higher up the call stack.
  check res.matcher
  let args := #[motive] ++ matcherApp.discrs.push below ++ alts
  let newApp := mkApp res.matcher motive
  let newApp := mkAppN newApp $ matcherApp.discrs.push below
  let newApp := mkAppN newApp alts
  (newApp, res.addMatcher)

where
  addBelowPattern (indName : Name) (lhs : AltLHS) : MetaM AltLHS := do
    withExistingLocalDecls lhs.fvarDecls do
    let patterns := lhs.patterns.toArray
    let originalPattern := patterns[idx]
    let (fVars, belowPattern) ← convertToBelow indName patterns[idx]
    withExistingLocalDecls fVars.toList do
    let patterns := patterns.push belowPattern
    let patterns := patterns.set! idx (←toInaccessible originalPattern)
    { lhs with patterns := patterns.toList, fvarDecls := lhs.fvarDecls ++ fVars.toList }

  /--
    this function changes the type of the pattern from the original type to the `below` version thereof.
    Most of the cases don't apply. In order to change the type and the pattern to be type correct, we don't
    simply recursively change all occurrences, but rather, we recursively change occurences of the constructor.
    As such there are only a few cases:
    - the pattern is a constructor from the original type. Here we need to:
      - replace the constructor
      - copy original recursive patterns and convert them to below and reintroduce them in the correct position
      - turn original recursive patterns inaccessible
      - introduce free variables as needed.
    - it is an `as` pattern. Here the contstructor could be hidden inside of it.
    - it is a variable. Here you we need to introduce a fresh variable of a different type.
  -/
  convertToBelow (indName : Name)
      (originalPattern : Pattern) : MetaM $ Array LocalDecl × Pattern := do
    match originalPattern with
    | Pattern.ctor ctorName us params fields =>
      let ctorInfo ← getConstInfoCtor ctorName

      let belowCtor ← getConstInfoCtor $ ctorName.updatePrefix $ ctorInfo.induct ++ `below
      let belowIndices ← IndPredBelow.getBelowIndices ctorName
      let belowIndices := belowIndices[ctorInfo.numParams:].toArray.map (· - belowCtor.numParams)

      -- belowFieldOpts starts off with an array of empty fields.
      -- We then go over pattern's fields and set the appropriate fields to values.
      -- In general, there are fewer `fields` than `belowFieldOpts`, because the
      -- `belowCtor` carries a `below`, a non-`below` and a `motive` version of each
      -- field that occurs in a recursive application of the inductive predicate.
      -- `belowIndices` is a mapping from non-`below` to the `below` version of each field.
      let mut belowFieldOpts := mkArray belowCtor.numFields none
      let fields := fields.toArray
      for fieldIdx in [:fields.size] do
        belowFieldOpts := belowFieldOpts.set! belowIndices[fieldIdx] (some fields[fieldIdx])

      let belowParams := params.toArray.push belowMotive
      let belowCtorExpr := mkAppN (mkConst belowCtor.name us) belowParams
      let (additionalFVars, belowFields) ← transformFields belowCtorExpr indName belowFieldOpts

      withExistingLocalDecls additionalFVars.toList do
      let ctor := Pattern.ctor belowCtor.name us belowParams.toList belowFields.toList
      trace[Meta.IndPredBelow.match] "{originalPattern.toMessageData} ↦ {ctor.toMessageData}"
      (additionalFVars, ctor)
    | Pattern.as varId p =>
      let (additionalFVars, p) ← convertToBelow indName p
      (additionalFVars, Pattern.as varId p)
    | Pattern.var varId =>
      let var := mkFVar varId
      (←inferType var).withApp fun ind args => do
      let (_, tgtType) ← belowType belowMotive #[var] 0
      withLocalDeclD (←mkFreshUserName `h) tgtType fun h => do
      let localDecl ← getFVarLocalDecl h
      (#[localDecl], Pattern.var h.fvarId!)
    | p => (#[], p)

  transformFields belowCtor indName belowFieldOpts :=
    let rec loop
      (belowCtor : Expr)
      (belowFieldOpts : Array $ Option Pattern)
      (belowFields : Array Pattern)
      (additionalFVars : Array LocalDecl) : MetaM (Array LocalDecl × Array Pattern) := do
      if belowFields.size ≥ belowFieldOpts.size then (additionalFVars, belowFields) else
      if let some belowField := belowFieldOpts[belowFields.size] then
        let belowFieldExpr ← belowField.toExpr
        let belowCtor := mkApp belowCtor belowFieldExpr
        let patTy ← inferType belowFieldExpr
        patTy.withApp fun f args => do
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
  | Pattern.inaccessible p => Pattern.inaccessible p
  | Pattern.var v => Pattern.var v
  | p => do Pattern.inaccessible $ ←p.toExpr

  newMotive (belowType : Expr) (ys : Array Expr) : MetaM Expr :=
    lambdaTelescope matcherApp.motive fun xs t => do
    let numDiscrs := matcherApp.discrs.size
    withLocalDeclD (←mkFreshUserName `h_below) (←belowType.replaceFVars ys xs) fun h_below => do
    let motive ← mkLambdaFVars (xs[:numDiscrs] ++ #[h_below] ++ xs[numDiscrs:]) t
    trace[Meta.IndPredBelow.match] "motive := {motive}"
    motive

def findBelowIdx (xs : Array Expr) (motive : Expr) : MetaM $ Option (Expr × Nat) := do
  xs.findSomeM? fun x => do
  let xTy ← inferType x
  xTy.withApp fun f args =>
  match f.constName?, xs.indexOf? x with
  | some name, some idx => do
    if ←isInductivePredicate name then
      let (_, belowTy) ← belowType motive xs idx
      let below ← mkFreshExprSyntheticOpaqueMVar belowTy
      try
        trace[Meta.IndPredBelow.match] "{←Meta.ppGoal below.mvarId!}"
        if ←backwardsChaining below.mvarId! 10 then
          trace[Meta.IndPredBelow.match] "Found below term in the local context: {below}"
          if ←xs.anyM (isDefEq below) then none else (below, idx.val)
        else
          trace[Meta.IndPredBelow.match] "could not find below term in the local context"
          none
      catch _ => none
    else none
  | _, _ => none

def mkBelow (declName : Name) : MetaM Unit := do
  if (←isInductivePredicate declName) then
    let x ← getConstInfoInduct declName
    if x.isRec then
      let ctx ← IndPredBelow.mkContext declName
      let decl ← IndPredBelow.mkBelowDecl ctx
      addDecl decl
      trace[Meta.IndPredBelow] "added {ctx.belowNames}"
      ctx.belowNames.forM Lean.mkCasesOn
      for i in [:ctx.typeInfos.size] do
        try
          let decl ← IndPredBelow.mkBrecOnDecl ctx i
          addDecl decl
        catch e => trace[Meta.IndPredBelow] "failed to prove brecOn for {ctx.belowNames[i]}\n{e.toMessageData}"
    else trace[Meta.IndPredBelow] "Not recursive"
  else trace[Meta.IndPredBelow] "Not inductive predicate"

builtin_initialize
  registerTraceClass `Meta.IndPredBelow
  registerTraceClass `Meta.IndPredBelow.match

end Lean.Meta.IndPredBelow
