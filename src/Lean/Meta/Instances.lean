/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Meta.GlobalInstances
import Lean.Meta.DiscrTree
import Lean.Meta.CollectMVars

namespace Lean.Meta

register_builtin_option synthInstance.checkSynthOrder : Bool := {
  defValue := true
  descr := "check that instances do not introduce metavariable in non-out-params"
}

/-
Note: we want to use iota reduction when indexing instances. Otherwise,
we cannot elaborate examples such as
```
inductive Ty where
  | int
  | bool

@[reducible] def Ty.interp (ty : Ty) : Type :=
  Ty.casesOn (motive := fun _ => Type) ty Int Bool

def test {a b c : Ty} (f : a.interp → b.interp → c.interp) (x : a.interp) (y : b.interp) : c.interp :=
  f x y

def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  -- We want to synthesize `BEq Ty.bool.interp` here, and it will fail
  -- if we do not reduce `Ty.bool.interp` to `Bool`.
  test (.==.) a b
```
See comment at `DiscrTree`.
-/

abbrev InstanceKey := DiscrTree.Key

structure InstanceEntry where
  keys        : Array InstanceKey
  val         : Expr
  priority    : Nat
  globalName? : Option Name := none
  /-- The order in which the instance's arguments are to be synthesized. -/
  synthOrder  : Array Nat
  /-
  We store the attribute kind to be able to implement the API `getInstanceAttrKind`.
  TODO: add better support for retrieving the `attrKind` of any attribute.
  The current implementation here works only for instances, but it is good enough for unblocking the
  implementation of `to_additive`.
  -/
  attrKind    : AttributeKind
  deriving Inhabited

instance : BEq InstanceEntry where
  beq e₁ e₂ := e₁.val == e₂.val

instance : ToFormat InstanceEntry where
  format e := match e.globalName? with
    | some n => format n
    | _      => "<local>"

abbrev InstanceTree := DiscrTree InstanceEntry

structure Instances where
  discrTree     : InstanceTree := DiscrTree.empty
  instanceNames : PHashMap Name InstanceEntry := {}
  erased        : PHashSet Name := {}
  deriving Inhabited

/-- Configuration for the discrimination tree module -/
def tcDtConfig : WhnfCoreConfig := {}

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances :=
  match e.globalName? with
  | some n => { d with discrTree := d.discrTree.insertCore e.keys e tcDtConfig, instanceNames := d.instanceNames.insert n e, erased := d.erased.erase n }
  | none   => { d with discrTree := d.discrTree.insertCore e.keys e tcDtConfig }

def Instances.eraseCore (d : Instances) (declName : Name) : Instances :=
  { d with erased := d.erased.insert declName, instanceNames := d.instanceNames.erase declName }

def Instances.erase [Monad m] [MonadError m] (d : Instances) (declName : Name) : m Instances := do
  unless d.instanceNames.contains declName do
    throwError "'{declName}' does not have [instance] attribute"
  return d.eraseCore declName

builtin_initialize instanceExtension : SimpleScopedEnvExtension InstanceEntry Instances ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := addInstanceEntry
  }

private def mkInstanceKey (e : Expr) : MetaM (Array InstanceKey) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    DiscrTree.mkPath type tcDtConfig

/--
Compute the order the arguments of `inst` should by synthesized.

The synthesization order makes sure that all mvars in non-out-params of the
subgoals are assigned before we try to synthesize it.  Otherwise it goes left
to right.

For example:
  - `[Add α] [Zero α] : Foo α` returns `[0, 1]`
  - `[Mul A] [Mul B] [MulHomClass F A B] : FunLike F A B` returns `[2, 0, 1]`
    (because A B are out-params and are only filled in once we synthesize 2)

(The type of `inst` must not contain mvars.)
-/
partial def computeSynthOrder (inst : Expr) : MetaM (Array Nat) :=
  withReducible do
  let instTy ← inferType inst

  -- Gets positions of all out- and semi-out-params of `classTy`
  -- (where `classTy` is e.g. something like `Inhabited Nat`)
  let rec getSemiOutParamPositionsOf (classTy : Expr) : MetaM (Array Nat) := do
    if let .const className .. := classTy.getAppFn then
      forallTelescopeReducing (← inferType classTy.getAppFn) fun args _ => do
      let mut pos := (getOutParamPositions? (← getEnv) className).getD #[]
      for arg in args, i in [:args.size] do
        if (← inferType arg).isAppOf ``semiOutParam then
          pos := pos.push i
      return pos
    else
      return #[]

  -- Create both metavariables and free variables for the instance args
  -- We will successively pick subgoals where all non-out-params have been
  -- assigned already. After picking such a "ready" subgoal, we assign the
  -- mvars in its out-params by the corresponding fvars.
  let (argMVars, argBIs, ty) ← forallMetaTelescopeReducing instTy
  let ty ← whnf ty
  forallTelescopeReducing instTy fun argVars _ => do

  -- Assigns all mvars from argMVars in e by the corresponding fvar.
  let rec assignMVarsIn (e : Expr) : MetaM Unit := do
    for mvarId in ← getMVars e do
      if let some i := argMVars.findIdx? (·.mvarId! == mvarId) then
        mvarId.assign argVars[i]!
      assignMVarsIn (← inferType (.mvar mvarId))

  -- We start by assigning all metavariables in non-out-params of the return value.
  -- These are assumed to not be mvars during TC search (or at least not assignable)
  let tyOutParams ← getSemiOutParamPositionsOf ty
  let tyArgs := ty.getAppArgs
  for tyArg in tyArgs, i in [:tyArgs.size] do
    unless tyOutParams.contains i do assignMVarsIn tyArg

  -- Now we successively try to find the next ready subgoal, where all
  -- non-out-params are mvar-free.
  let mut synthed := #[]
  let mut toSynth := List.range argMVars.size |>.filter (argBIs[·]! == .instImplicit) |>.toArray
  while !toSynth.isEmpty do
    let next? ← toSynth.findM? fun i => do
      forallTelescopeReducing (← instantiateMVars (← inferType argMVars[i]!)) fun _ argTy => do
      let argTy ← whnf argTy
      let argOutParams ← getSemiOutParamPositionsOf argTy
      let argTyArgs := argTy.getAppArgs
      for i in [:argTyArgs.size], argTyArg in argTyArgs do
        if !argOutParams.contains i && argTyArg.hasExprMVar then
          return false
      return true
    let next ←
      match next? with
      | some next => pure next
      | none =>
        if synthInstance.checkSynthOrder.get (← getOptions) then
          let typeLines := ("" : MessageData).joinSep <| Array.toList <| ← toSynth.mapM fun i => do
            let ty ← instantiateMVars (← inferType argMVars[i]!)
            return indentExpr (ty.setPPExplicit true)
          logError m!"cannot find synthesization order for instance {inst} with type{indentExpr instTy}\nall remaining arguments have metavariables:{typeLines}"
        pure toSynth[0]!
    synthed := synthed.push next
    toSynth := toSynth.filter (· != next)
    assignMVarsIn (← inferType argMVars[next]!)
    assignMVarsIn argMVars[next]!

  if synthInstance.checkSynthOrder.get (← getOptions) then
    let ty ← instantiateMVars ty
    if ty.hasExprMVar then
      logError m!"instance does not provide concrete values for (semi-)out-params{indentExpr (ty.setPPExplicit true)}"

  trace[Meta.synthOrder] "synthesizing the arguments of {inst} in the order {synthed}:{("" : MessageData).joinSep (← synthed.mapM fun i => return indentExpr (← inferType argVars[i]!)).toList}"

  return synthed

def addInstance (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let c ← mkConstWithLevelParams declName
  let keys ← mkInstanceKey c
  addGlobalInstance declName attrKind
  let synthOrder ← computeSynthOrder c
  instanceExtension.add { keys, val := c, priority := prio, globalName? := declName, attrKind, synthOrder } attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `instance
    descr := "type class instance"
    add   := fun declName stx attrKind => do
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addInstance declName attrKind prio |>.run {} {}
    erase := fun declName => do
      let s := instanceExtension.getState (← getEnv)
      let s ← s.erase declName
      modifyEnv fun env => instanceExtension.modifyState env fun _ => s
  }

def getGlobalInstancesIndex : CoreM (DiscrTree InstanceEntry) :=
  return Meta.instanceExtension.getState (← getEnv) |>.discrTree

def getErasedInstances : CoreM (PHashSet Name) :=
  return Meta.instanceExtension.getState (← getEnv) |>.erased

def isInstance (declName : Name) : CoreM Bool :=
  return Meta.instanceExtension.getState (← getEnv) |>.instanceNames.contains declName

def getInstancePriority? (declName : Name) : CoreM (Option Nat) := do
  let some entry := Meta.instanceExtension.getState (← getEnv) |>.instanceNames.find? declName | return none
  return entry.priority

def getInstanceAttrKind? (declName : Name) : CoreM (Option AttributeKind) := do
  let some entry := Meta.instanceExtension.getState (← getEnv) |>.instanceNames.find? declName | return none
  return entry.attrKind

/-! # Default instance support -/

structure DefaultInstanceEntry where
  className    : Name
  instanceName : Name
  priority     : Nat

abbrev PrioritySet := RBTree Nat (fun x y => compare y x)

structure DefaultInstances where
  defaultInstances : NameMap (List (Name × Nat)) := {}
  priorities       : PrioritySet := {}
  deriving Inhabited

def addDefaultInstanceEntry (d : DefaultInstances) (e : DefaultInstanceEntry) : DefaultInstances :=
  let d := { d with priorities := d.priorities.insert e.priority }
  match d.defaultInstances.find? e.className with
  | some insts => { d with defaultInstances := d.defaultInstances.insert e.className <| (e.instanceName, e.priority) :: insts }
  | none       => { d with defaultInstances := d.defaultInstances.insert e.className [(e.instanceName, e.priority)] }

builtin_initialize defaultInstanceExtension : SimplePersistentEnvExtension DefaultInstanceEntry DefaultInstances ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addDefaultInstanceEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addDefaultInstanceEntry {} es)
  }

def addDefaultInstance (declName : Name) (prio : Nat := 0) : MetaM Unit := do
  match (← getEnv).find? declName with
  | none => throwError "unknown constant '{declName}'"
  | some info =>
    forallTelescopeReducing info.type fun _ type => do
      match type.getAppFn with
      | Expr.const className _ =>
        unless isClass (← getEnv) className do
          throwError "invalid default instance '{declName}', it has type '({className} ...)', but {className}' is not a type class"
        setEnv <| defaultInstanceExtension.addEntry (← getEnv) { className := className, instanceName := declName, priority := prio }
      | _ => throwError "invalid default instance '{declName}', type must be of the form '(C ...)' where 'C' is a type class"

builtin_initialize
  registerBuiltinAttribute {
    name  := `default_instance
    descr := "type class default instance"
    add   := fun declName stx kind => do
      let prio ← getAttrParamOptPrio stx[1]
      unless kind == AttributeKind.global do throwError "invalid attribute 'default_instance', must be global"
      discard <| addDefaultInstance declName prio |>.run {} {}
  }
  registerTraceClass `Meta.synthOrder

def getDefaultInstancesPriorities [Monad m] [MonadEnv m] : m PrioritySet :=
  return defaultInstanceExtension.getState (← getEnv) |>.priorities

def getDefaultInstances [Monad m] [MonadEnv m] (className : Name) : m (List (Name × Nat)) :=
  return defaultInstanceExtension.getState (← getEnv) |>.defaultInstances.find? className |>.getD []

end Lean.Meta
