/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

import Lean.Util.Constructions
import Lean.Meta.Transform
import Lean.Meta.Tactic

namespace Lean.Meta.IndPredBelow

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
      (ctx.belowNames[idx], fun _ => pure header)

    withLocalDeclsD headersWithNames fun xs =>
      addMotives { vars with indVal := xs } 

  addMotives (vars : Variables) := do
    let motiveBuilders ← ctx.motives.mapM fun (motiveName, motiveType) => 
      (motiveName, BinderInfo.implicit, fun _ => 
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

partial def proveBrecOn (ctx : Context) (indVal : InductiveVal) (type : Expr) : MetaM Expr := do
  let main ← mkFreshExprSyntheticOpaqueMVar type
  let (m, vars) ← intros main.mvarId!
  let [m] ← applyIH m vars | 
    throwError "applying the induction hypothesis should only return one goal"
  let ms ← induction m vars
  let ms ← applyCtors ms 
  ms.forM (closeGoal vars)
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
    withMVarContext m do
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
      args.back.withApp fun ctor args =>
      let ctor := ctor.constName!.updatePrefix below.constName!
      withMVarContext m do
      let ctor := mkConst ctor below.constLevels!
      apply m ctor 
    return mss.foldr List.append []

  introNPRec (m : MVarId) : MetaM MVarId := do
    if (←getMVarType m).isForall then introNPRec (←intro1P m).2 else m
  
  closeGoal (vars : BrecOnVariables) (m : MVarId) : MetaM Unit := do
    unless ←isExprMVarAssigned m do
      let m ← introNPRec m
      unless ←solveByAssumption m do
        let subGoals ← applyIH m vars
        subGoals.forM (closeGoal vars)
  
  solveByAssumption (m : MVarId) : MetaM Bool := do
    withMVarContext m do
    let lctx ← getLCtx 
    let mTy ← getMVarType m
    lctx.anyM fun localDecl => do
      let (mvars, _, t) ← forallMetaTelescope localDecl.type
      commitWhen do
      if ←isDefEq mTy t then 
        assignExprMVar m t
        if ←mvars.allM (fun v => isExprMVarAssigned v.mvarId!) then 
          assignExprMVar m (mkAppN (mkFVar localDecl.fvarId) mvars)
          true
        else false
      else false

def mkBrecOnDecl (ctx : Context) (idx : Nat) : MetaM Declaration := do
  let type ← mkType
  let indVal := ctx.typeInfos[idx]
  let name := indVal.name ++ brecOnSuffix
  Declaration.thmDecl { 
    name := indVal.name ++ brecOnSuffix
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
    let mkDomain _ := 
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

end Lean.Meta.IndPredBelow