#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.DiscrTree

namespace Lean.Meta

structure InstanceEntry :=
(keys : Array DiscrTree.Key)
(val  : Expr)

abbrev Instances := DiscrTree Expr

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances :=
d.insertCore e.keys e.val

initialize instanceExtension : SimplePersistentEnvExtension InstanceEntry Instances ←
registerSimplePersistentEnvExtension {
  name          := `instanceExt,
  addEntryFn    := addInstanceEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries addInstanceEntry DiscrTree.empty es)
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
  pure $ instanceExtension.addEntry s.env { keys := keys, val := c }

def addGlobalInstance {m} [Monad m] [MonadEnv m] [MonadIO m] (declName : Name) : m Unit := do
let env ← getEnv
let env ← liftIO $ Meta.addGlobalInstanceImp env declName
setEnv env

initialize
registerBuiltinAttribute {
  name  := `instance,
  descr := "type class instance",
  add   := fun declName args persistent => do
    if args.hasArgs then throwError "invalid attribute 'instance', unexpected argument"
    unless persistent do throwError "invalid attribute 'instance', must be persistent"
    let env ← getEnv
    let env ← ofExcept (addGlobalInstanceOld env declName); setEnv env; -- TODO: delete after we remove old frontend
    addGlobalInstance declName
}

end Meta

def Environment.getGlobalInstances (env : Environment) : Meta.Instances :=
Meta.instanceExtension.getState env

namespace Meta

def getGlobalInstances : MetaM Instances := do
let env ← getEnv
pure env.getGlobalInstances

end Meta
end Lean
