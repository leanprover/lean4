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

/--
Information about an eliminator as used by `induction` or `cases`.

Created from an expression by `getElimInfo`. This typically contains level metavariables that
are instantiated as we go (e.g. in `addImplicitTargets`), so this is single use.
-/
structure ElimInfo where
  elimExpr   : Expr
  elimType   : Expr
  motivePos  : Nat
  targetsPos : Array Nat := #[]
  altsInfo   : Array ElimAltInfo := #[]
  deriving Repr, Inhabited

def getElimExprInfo (elimExpr : Expr) (baseDeclName? : Option Name := none) : MetaM ElimInfo := do
  let elimType ← inferType elimExpr
  trace[Elab.induction] "eliminator {indentExpr elimExpr}\nhas type{indentExpr elimType}"
  forallTelescopeReducing elimType fun xs type => do
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
      throwError "unexpected eliminator type{indentExpr elimType}"
    let targetsPos ← targets.mapM fun target => do
      match xs.indexOf? target with
      | none => throwError "unexpected eliminator type{indentExpr elimType}"
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
    pure { elimExpr, elimType,  motivePos, targetsPos, altsInfo }

def getElimInfo (elimName : Name) (baseDeclName? : Option Name := none) : MetaM ElimInfo := do
  getElimExprInfo (← mkConstWithFreshMVarLevels elimName) baseDeclName?

/--
  Eliminators/recursors may have implicit targets. For builtin recursors, all indices are implicit targets.
  Given an eliminator and the sequence of explicit targets, this methods returns a new sequence containing
  implicit and explicit targets.
-/
partial def addImplicitTargets (elimInfo : ElimInfo) (targets : Array Expr) : MetaM (Array Expr) := do
  let (implicitMVars, targets) ← collect elimInfo.elimType 0 0 #[] #[]
  for mvar in implicitMVars do
    unless ← mvar.isAssigned do
      let name := (←mvar.getDecl).userName
      if name.isAnonymous || name.hasMacroScopes then
        throwError "failed to infer implicit target"
      else
        throwError "failed to infer implicit target {(←mvar.getDecl).userName}"
  targets.mapM instantiateMVars
where
  collect (type : Expr) (argIdx targetIdx : Nat) (implicits : Array MVarId) (targets' : Array Expr) :
      MetaM (Array MVarId × Array Expr) := do
    match (← whnfD type) with
    | Expr.forallE n d b bi =>
      if elimInfo.targetsPos.contains argIdx then
        if bi.isExplicit then
          unless targetIdx < targets.size do
            throwError "insufficient number of targets for '{elimInfo.elimExpr}'"
          let target := targets[targetIdx]!
          let targetType ← inferType target
          unless (← isDefEq d targetType) do
            throwError "target{indentExpr target}\n{← mkHasTypeButIsExpectedMsg targetType d}"
          collect (b.instantiate1 target) (argIdx+1) (targetIdx+1) implicits (targets'.push target)
        else
          let implicitTarget ← mkFreshExprMVar (type? := d) (userName := n)
          collect (b.instantiate1 implicitTarget) (argIdx+1) targetIdx (implicits.push implicitTarget.mvarId!) (targets'.push implicitTarget)
      else
        collect (b.instantiate1 (← mkFreshExprMVar d)) (argIdx+1) targetIdx implicits targets'
    | _ =>
      return (implicits, targets')

structure CustomEliminator where
  typeNames : Array Name
  elimName  : Name -- NB: Do not store the ElimInfo, it can contain MVars
  deriving Inhabited, Repr

structure CustomEliminators where
  map : SMap (Array Name) Name := {}
  deriving Inhabited, Repr

def addCustomEliminatorEntry (es : CustomEliminators) (e : CustomEliminator) : CustomEliminators :=
  match es with
  | { map := map } => { map := map.insert e.typeNames e.elimName }

builtin_initialize customEliminatorExt : SimpleScopedEnvExtension CustomEliminator CustomEliminators ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := addCustomEliminatorEntry
    finalizeImport := fun { map := map } => { map := map.switch }
  }

def mkCustomEliminator (elimName : Name) : MetaM CustomEliminator := do
  let elimInfo ← getElimInfo elimName
  let info ← getConstInfo elimName
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
    return { typeNames, elimName}

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

def getCustomEliminator? (targets : Array Expr) : MetaM (Option Name) := do
  let mut key := #[]
  for target in targets do
    let targetType := (← instantiateMVars (← inferType target)).headBeta
    let .const declName .. := targetType.getAppFn | return none
    key := key.push declName
  return customEliminatorExt.getState (← getEnv) |>.map.find? key

end Lean.Meta
