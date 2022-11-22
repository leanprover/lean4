/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Meta.GlobalInstances
import Lean.Meta.DiscrTree

namespace Lean.Meta

/-
Note: we want to use iota reduction when indexing instaces. Otherwise,
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

abbrev InstanceKey := DiscrTree.Key (simpleReduce := false)

structure InstanceEntry where
  keys        : Array InstanceKey
  val         : Expr
  priority    : Nat
  globalName? : Option Name := none
  deriving Inhabited

instance : BEq InstanceEntry where
  beq e₁ e₂ := e₁.val == e₂.val

instance : ToFormat InstanceEntry where
  format e := match e.globalName? with
    | some n => format n
    | _      => "<local>"

abbrev InstanceTree := DiscrTree InstanceEntry (simpleReduce := false)

structure Instances where
  discrTree     : InstanceTree := DiscrTree.empty
  instanceNames : PHashSet Name := {}
  erased        : PHashSet Name := {}
  deriving Inhabited

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances :=
  match e.globalName? with
  | some n => { d with discrTree := d.discrTree.insertCore e.keys e, instanceNames := d.instanceNames.insert n }
  | none   => { d with discrTree := d.discrTree.insertCore e.keys e }

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
    DiscrTree.mkPath type

def addInstance (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let c ← mkConstWithLevelParams declName
  let keys ← mkInstanceKey c
  addGlobalInstance declName attrKind
  instanceExtension.add { keys := keys, val := c, priority := prio, globalName? := declName } attrKind

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

def getGlobalInstancesIndex : CoreM (DiscrTree InstanceEntry (simpleReduce := false)) :=
  return Meta.instanceExtension.getState (← getEnv) |>.discrTree

def getErasedInstances : CoreM (PHashSet Name) :=
  return Meta.instanceExtension.getState (← getEnv) |>.erased

def isInstance (declName : Name) : CoreM Bool :=
  return Meta.instanceExtension.getState (← getEnv) |>.instanceNames.contains declName

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

def getDefaultInstancesPriorities [Monad m] [MonadEnv m] : m PrioritySet :=
  return defaultInstanceExtension.getState (← getEnv) |>.priorities

def getDefaultInstances [Monad m] [MonadEnv m] (className : Name) : m (List (Name × Nat)) :=
  return defaultInstanceExtension.getState (← getEnv) |>.defaultInstances.find? className |>.getD []

end Lean.Meta
