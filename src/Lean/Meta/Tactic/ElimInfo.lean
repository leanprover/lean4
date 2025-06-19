/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.ScopedEnvExtension

namespace Lean.Meta

structure ElimAltInfo where
  name      : Name
  /-- A declaration corresponding to the inductive constructor.
  (For custom recursors, the alternatives correspond to parameter names in the
  recursor, so we may not have a declaration to point to.)
  This is used for go-to-definition on the alternative name. -/
  declName? : Option Name
  numFields : Nat
  /-- If `provesMotive := true`, then this alternative has `motive` as its conclusion.
  Only for those alternatives the `induction` tactic should introduce reverted hypotheses.  -/
  provesMotive : Bool
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
  /--
  Extra arguments to the motive, after the targets, that are instantiated with
  non-atomic expressions in the goal
  -/
  numComplexMotiveArgs : Nat
  deriving Repr, Inhabited


/-- Given the type `t` of an alternative, determines the number of parameters
(.forall and .let)-bound, and whether the conclusion is a `motive`-application.  -/
def altArity (motive : Expr) (n : Nat) : Expr → Nat × Bool
  | .forallE _ _ b _ => altArity motive (n+1) b
  | .letE _ _ _ b _ => altArity motive (n+1) b
  | conclusion => (n, conclusion.getAppFn == motive)


def getElimExprInfo (elimExpr : Expr) (baseDeclName? : Option Name := none) : MetaM ElimInfo := do
  let elimType ← inferType elimExpr
  trace[Elab.induction] "eliminator {indentExpr elimExpr}\nhas type{indentExpr elimType}"
  forallTelescopeReducing elimType fun xs type => type.withApp fun motive motiveArgs => do
    unless motive.isFVar do
      throwError "expected resulting type of eliminator to be an application of one of its parameters (the motive):{indentExpr type}"
    let targets  := motiveArgs.takeWhile (·.isFVar)
    let complexMotiveArgs := motiveArgs[targets.size:]
    let motiveType ← inferType motive
    forallTelescopeReducing motiveType fun motiveParams motiveResultType => do
      unless motiveParams.size == motiveArgs.size do
        throwError "expected {motiveArgs.size} parameters at motive type, got {motiveParams.size}:{indentExpr motiveType}"
      unless motiveResultType.isSort do
        throwError "motive result type must be a sort{indentExpr motiveType}"
    let some motivePos ← pure (xs.idxOf? motive) |
      throwError "unexpected eliminator type{indentExpr elimType}"
    let targetsPos ← targets.mapM fun target => do
      match xs.idxOf? target with
      | none => throwError "unexpected eliminator type{indentExpr elimType}"
      | some targetPos => pure targetPos
    let mut altsInfo := #[]
    let env ← getEnv
    for h : i in [:xs.size] do
      let x := xs[i]
      if x != motive && !targets.contains x then
        let xDecl ← x.fvarId!.getDecl
        if xDecl.binderInfo.isExplicit then
          let (numFields, provesMotive) := altArity motive 0 xDecl.type
          let name := xDecl.userName
          let declName? := do
            let base ← baseDeclName?
            let altDeclName := base ++ name
            if env.contains altDeclName then some altDeclName else none
          altsInfo := altsInfo.push { name, declName?, numFields, provesMotive }
    pure { elimExpr, elimType,  motivePos, targetsPos, altsInfo, numComplexMotiveArgs := complexMotiveArgs.size }

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
      unless targetIdx = targets.size do
        throwError "extra targets for '{elimInfo.elimExpr}'"
      return (implicits, targets')

structure CustomEliminator where
  induction : Bool
  typeNames : Array Name
  elimName  : Name -- NB: Do not store the ElimInfo, it can contain MVars
  deriving Inhabited, Repr

structure CustomEliminators where
  map : SMap (Bool × Array Name) Name := {}
  deriving Inhabited, Repr

def addCustomEliminatorEntry (es : CustomEliminators) (e : CustomEliminator) : CustomEliminators :=
  match es with
  | { map := map } => { map := map.insert (e.induction, e.typeNames) e.elimName }

builtin_initialize customEliminatorExt : SimpleScopedEnvExtension CustomEliminator CustomEliminators ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := addCustomEliminatorEntry
    finalizeImport := fun { map := map } => { map := map.switch }
  }

def mkCustomEliminator (elimName : Name) (induction : Bool) : MetaM CustomEliminator := do
  let elimInfo ← getElimInfo elimName
  let info ← getConstInfo elimName
  forallTelescopeReducing info.type fun xs _ => do
    let mut typeNames := #[]
    for hi : i in [:elimInfo.targetsPos.size] do
      let targetPos := elimInfo.targetsPos[i]
      let x := xs[targetPos]!
      /- Return true if there is another target that depends on `x`. -/
      let isImplicitTarget : MetaM Bool := do
        for hj : j in [i+1:elimInfo.targetsPos.size] do
          let y := xs[elimInfo.targetsPos[j]]!
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
    return { induction, typeNames, elimName }

def addCustomEliminator (declName : Name) (attrKind : AttributeKind) (induction : Bool) : MetaM Unit := do
  let e ← mkCustomEliminator declName induction
  customEliminatorExt.add e attrKind

/--
Registers a custom eliminator for the `induction` tactic.

Whenever the types of the targets in an `induction` call matches a custom eliminator, it is used
instead of the recursor. This can be useful for redefining the default eliminator to a more useful
one.

Example:
```lean example
structure Three where
  val : Fin 3

example (x : Three) (p : Three → Prop) : p x := by
  induction x
  -- val : Fin 3 ⊢ p ⟨val⟩

@[induction_eliminator, elab_as_elim]
def Three.myRec {motive : Three → Sort u}
    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :
    ∀ x, motive x
  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two

example (x : Three) (p : Three → Prop) : p x := by
  induction x
  -- ⊢ p ⟨0⟩
  -- ⊢ p ⟨1⟩
  -- ⊢ p ⟨2⟩
```

`@[cases_eliminator]` works similarly for the `cases` tactic.
-/
@[builtin_doc]
builtin_initialize
  registerBuiltinAttribute {
    name  := `induction_eliminator
    descr := "custom `rec`-like eliminator for the `induction` tactic"
    add   := fun declName _ attrKind => do
      discard <| addCustomEliminator declName attrKind (induction := true) |>.run {} {}
  }

/--
Registers a custom eliminator for the `cases` tactic.

Whenever the types of the targets in an `cases` call matches a custom eliminator, it is used
instead of the `casesOn` eliminator. This can be useful for redefining the default eliminator to a
more useful one.

Example:
```lean example
structure Three where
  val : Fin 3

example (x : Three) (p : Three → Prop) : p x := by
  cases x
  -- val : Fin 3 ⊢ p ⟨val⟩

@[cases_eliminator, elab_as_elim]
def Three.myRec {motive : Three → Sort u}
    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :
    ∀ x, motive x
  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two

example (x : Three) (p : Three → Prop) : p x := by
  cases x
  -- ⊢ p ⟨0⟩
  -- ⊢ p ⟨1⟩
  -- ⊢ p ⟨2⟩
```

`@[induction_eliminator]` works similarly for the `induction` tactic.
-/
@[builtin_doc]
builtin_initialize
  registerBuiltinAttribute {
    name  := `cases_eliminator
    descr := "custom `casesOn`-like eliminator for the `cases` tactic"
    add   := fun declName _ attrKind => do
      discard <| addCustomEliminator declName attrKind (induction := false) |>.run {} {}
  }

/-- Gets all the eliminators defined using the `@[induction_eliminator]` and `@[cases_eliminator]` attributes. -/
def getCustomEliminators : CoreM CustomEliminators := do
  return customEliminatorExt.getState (← getEnv)

/--
Gets an eliminator appropriate for the provided array of targets.
If `induction` is `true` then returns a matching eliminator defined using the `@[induction_eliminator]` attribute
and otherwise returns one defined using the `@[cases_eliminator]` attribute.

The `@[induction_eliminator]` attribute is for the `induction` tactic
and the `@[cases_eliminator]` attribute is for the `cases` tactic.
-/
def getCustomEliminator? (targets : Array Expr) (induction : Bool) : MetaM (Option Name) := do
  let mut key := #[]
  for target in targets do
    let targetType := (← instantiateMVars (← inferType target)).headBeta
    let .const declName .. := targetType.getAppFn | return none
    key := key.push declName
  return customEliminatorExt.getState (← getEnv) |>.map.find? (induction, key)

end Lean.Meta
