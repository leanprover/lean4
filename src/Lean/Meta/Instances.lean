/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.DiscrTree

namespace Lean.Meta

structure InstanceEntry :=
  (keys        : Array DiscrTree.Key)
  (val         : Expr)
  (globalName? : Option Name := none)

structure Instances :=
  (discrTree       : DiscrTree Expr := DiscrTree.empty )
  (globalInstances : NameSet := {})

instance : Inhabited Instances := {
  default := {}
}

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances :=
  { d with
    discrTree := d.discrTree.insertCore e.keys e.val
    globalInstances := match e.globalName? with
      | some n => d.globalInstances.insert n
      | none   => d.globalInstances
  }

builtin_initialize instanceExtension : SimplePersistentEnvExtension InstanceEntry Instances ←
  registerSimplePersistentEnvExtension {
    name          := `instanceExt,
    addEntryFn    := addInstanceEntry,
    addImportedFn := fun es => (mkStateFromImportedEntries addInstanceEntry {} es)
  }

private def mkInstanceKey (e : Expr) : MetaM (Array DiscrTree.Key) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    DiscrTree.mkPath type

@[export lean_add_instance]
def addGlobalInstanceImp (env : Environment) (constName : Name) : IO Environment := do
  match env.find? constName with
  | none => throw $ IO.userError "unknown constant"
  | some cinfo =>
    let c := mkConst constName (cinfo.lparams.map mkLevelParam)
    let (keys, s, _) ← (mkInstanceKey c).toIO {} { env := env } {} {}
    pure $ instanceExtension.addEntry s.env { keys := keys, val := c, globalName? := constName }

def addGlobalInstance {m} [Monad m] [MonadEnv m] [MonadLiftT IO m] (declName : Name) : m Unit := do
  let env ← getEnv
  let env ← Meta.addGlobalInstanceImp env declName
  setEnv env

builtin_initialize
  registerBuiltinAttribute {
    name  := `instance,
    descr := "type class instance",
    add   := fun declName args persistent => do
      if args.hasArgs then throwError "invalid attribute 'instance', unexpected argument"
      unless persistent do throwError "invalid attribute 'instance', must be persistent"
      addGlobalInstance declName
  }

@[export lean_is_instance]
def isGlobalInstance (env : Environment) (declName : Name) : Bool :=
  Meta.instanceExtension.getState env |>.globalInstances.contains declName

def getGlobalInstancesIndex : MetaM (DiscrTree Expr) :=
  return Meta.instanceExtension.getState (← getEnv) |>.discrTree

end Lean.Meta
