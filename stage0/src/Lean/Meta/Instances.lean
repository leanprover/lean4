/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.DiscrTree

namespace Lean
namespace Meta

structure InstanceEntry :=
(keys : Array DiscrTree.Key)
(val  : Expr)

abbrev Instances := DiscrTree Expr

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances :=
d.insertCore e.keys e.val

def mkInstanceExtension : IO (SimplePersistentEnvExtension InstanceEntry Instances) :=
registerSimplePersistentEnvExtension {
  name          := `instanceExt,
  addEntryFn    := addInstanceEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries addInstanceEntry DiscrTree.empty es)
}

@[init mkInstanceExtension]
constant instanceExtension : SimplePersistentEnvExtension InstanceEntry Instances := arbitrary _

private def mkInstanceKey (e : Expr) : MetaM (Array DiscrTree.Key) := do
type ← inferType e;
withNewMCtxDepth $ do
  (_, _, type) ← forallMetaTelescopeReducing type;
  DiscrTree.mkPath type

@[export lean_add_instance]
def addGlobalInstance (env : Environment) (constName : Name) : IO Environment :=
match env.find? constName with
| none => throw $ IO.userError "unknown constant"
| some cinfo => do
  let c := mkConst constName (cinfo.lparams.map mkLevelParam);
  (env, keys) ← ((mkInstanceKey c).run).run' env;
  pure $ instanceExtension.addEntry env { keys := keys, val := c }

@[init] def registerInstanceAttr : IO Unit :=
registerBuiltinAttribute {
  name  := `instance,
  descr := "type class instance",
  add   := fun declName args persistent => do
    when args.hasArgs $ Core.throwError "invalid attribute 'instance', unexpected argument";
    unless persistent $ Core.throwError "invalid attribute 'instance', must be persistent";
    env ← Core.getEnv;
    env ← Core.ofExcept (addGlobalInstanceOld env declName); -- TODO: delete
    env ← liftIO $ addGlobalInstance env declName;
    Core.setEnv env
}

end Meta

def Environment.getGlobalInstances (env : Environment) : Meta.Instances :=
Meta.instanceExtension.getState env

namespace Meta

def getGlobalInstances : MetaM Instances := do
env ← getEnv;
pure env.getGlobalInstances

end Meta

end Lean
