/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.ScopedEnvExtension

namespace Lean.Meta

structure ElimAltInfo where
  name      : Name
  declName? : Option Name
  numFields : Nat
  deriving Repr, Inhabited

structure ElimInfo where
  name       : Name
  motivePos  : Nat
  targetsPos : Array Nat := #[]
  altsInfo   : Array ElimAltInfo := #[]
  deriving Repr, Inhabited

def getElimInfo (declName : Name) (baseDeclName? : Option Name := none) : MetaM ElimInfo := do
  let declInfo ← getConstInfo declName
  forallTelescopeReducing declInfo.type fun xs type => do
    let motive  := type.getAppFn
    let targets := type.getAppArgs
    unless motive.isFVar && targets.all (·.isFVar) && targets.size > 0 do
      throwError "unexpected eliminator resulting type{indentExpr type}"
    let motiveType ← inferType motive
    forallTelescopeReducing motiveType fun motiveArgs motiveResultType => do
      unless motiveArgs.size == targets.size do
        throwError "unexpected number of arguments at motive type{indentExpr motiveType}"
      unless motiveResultType.isSort do
        throwError "motive result type must be a sort{indentExpr motiveType}"
    let some motivePos ← pure (xs.indexOf? motive) |
      throwError "unexpected eliminator type{indentExpr declInfo.type}"
    let targetsPos ← targets.mapM fun target => do
      match xs.indexOf? target with
      | none => throwError "unexpected eliminator type{indentExpr declInfo.type}"
      | some targetPos => pure targetPos.val
    let mut altsInfo := #[]
    let env ← getEnv
    for i in [:xs.size] do
      let x := xs[i]!
      if x != motive && !targets.contains x then
        let xDecl ← x.fvarId!.getDecl
        if xDecl.binderInfo.isExplicit then
          let numFields ← forallTelescopeReducing xDecl.type fun args _ => pure args.size
          let name := xDecl.userName
          let declName? := do
            let base ← baseDeclName?
            let altDeclName := base ++ name
            if env.contains altDeclName then some altDeclName else none
          altsInfo := altsInfo.push { name, declName?, numFields }
    pure { name := declName, motivePos, targetsPos, altsInfo }

/--
  Eliminators/recursors may have implicit targets. For builtin recursors, all indices are implicit targets.
  Given an eliminator and the sequence of explicit targets, this methods returns a new sequence containing
  implicit and explicit targets.
-/
partial def addImplicitTargets (elimInfo : ElimInfo) (targets : Array Expr) : MetaM (Array Expr) :=
  withNewMCtxDepth do
    let f ← mkConstWithFreshMVarLevels elimInfo.name
    let targets ← collect (← inferType f) 0 0 #[]
    let targets ← targets.mapM instantiateMVars
    for target in targets do
      if (← hasAssignableMVar target) then
        throwError "failed to infer implicit target, it contains unresolved metavariables{indentExpr target}"
    return targets
where
  collect (type : Expr) (argIdx targetIdx : Nat) (targets' : Array Expr) : MetaM (Array Expr) := do
    match (← whnfD type) with
    | Expr.forallE _ d b bi =>
      if elimInfo.targetsPos.contains argIdx then
        if bi.isExplicit then
          unless targetIdx < targets.size do
            throwError "insufficient number of targets for '{elimInfo.name}'"
          let target := targets[targetIdx]!
          let targetType ← inferType target
          unless (← isDefEq d targetType) do
            throwError "target{indentExpr target}\n{← mkHasTypeButIsExpectedMsg targetType d}"
          collect (b.instantiate1 target) (argIdx+1) (targetIdx+1) (targets'.push target)
        else
          let implicitTarget ← mkFreshExprMVar d
          collect (b.instantiate1 implicitTarget) (argIdx+1) targetIdx (targets'.push implicitTarget)
      else
        collect (b.instantiate1 (← mkFreshExprMVar d)) (argIdx+1) targetIdx targets'
    | _ =>
      return targets'

structure CustomEliminator where
  typeNames : Array Name
  elimInfo  : ElimInfo
  deriving Inhabited, Repr

structure CustomEliminators where
  map : SMap (Array Name) ElimInfo := {}
  deriving Inhabited, Repr

def addCustomEliminatorEntry (es : CustomEliminators) (e : CustomEliminator) : CustomEliminators :=
  match es with
  | { map := map } => { map := map.insert e.typeNames e.elimInfo }

builtin_initialize customEliminatorExt : SimpleScopedEnvExtension CustomEliminator CustomEliminators ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := addCustomEliminatorEntry
    finalizeImport := fun { map := map } => { map := map.switch }
  }

def mkCustomEliminator (declName : Name) : MetaM CustomEliminator := do
  let info ← getConstInfo declName
  let elimInfo ← getElimInfo declName
  forallTelescopeReducing info.type fun xs _ => do
    let mut typeNames := #[]
    for i in [:elimInfo.targetsPos.size] do
      let targetPos := elimInfo.targetsPos[i]!
      let x := xs[targetPos]!
      /- Return true if there is another target that depends on `x`. -/
      let isImplicitTarget : MetaM Bool := do
        for j in [i+1:elimInfo.targetsPos.size] do
          let y := xs[elimInfo.targetsPos[j]!]!
          let yType ← inferType y
          if (← dependsOn yType x.fvarId!) then
            return true
        return false
      /- We should only use explicit targets when creating the key for the `CustomEliminators` map.
         See test `tests/lean/run/eliminatorImplicitTargets.lean`. -/
      unless (← isImplicitTarget) do
        let xType ← inferType x
        let .const typeName .. := xType.getAppFn | throwError "unexpected eliminator target type{indentExpr xType}"
        typeNames := typeNames.push typeName
    return { typeNames, elimInfo }

def addCustomEliminator (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let e ← mkCustomEliminator declName
  customEliminatorExt.add e attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `eliminator
    descr := "custom eliminator for `cases` and `induction` tactics"
    add   := fun declName _ attrKind => do
      discard <| addCustomEliminator declName attrKind |>.run {} {}
  }

def getCustomEliminators : CoreM CustomEliminators := do
  return customEliminatorExt.getState (← getEnv)

def getCustomEliminator? (targets : Array Expr) : MetaM (Option ElimInfo) := do
  let mut key := #[]
  for target in targets do
    let targetType := (← instantiateMVars (← inferType target)).headBeta
    let .const declName .. := targetType.getAppFn | return none
    key := key.push declName
  return customEliminatorExt.getState (← getEnv) |>.map.find? key

end Lean.Meta
