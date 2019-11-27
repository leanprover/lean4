/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.DiscrTree

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

private def mkInstanceKey (e : Expr) : MetaM (Array DiscrTree.Key) :=
do type ← inferType e;
   withNewMCtxDepth $ do
     (_, _, type) ← forallMetaTelescopeReducing type;
     DiscrTree.mkPath type

def addGlobalInstance (env : Environment) (constName : Name) : IO Environment :=
match env.find constName with
| none => throw $ IO.userError "unknown constant"
| some cinfo => do
  let c := mkConst constName (cinfo.lparams.map mkLevelParam);
  (keys, env) ← IO.runMeta (mkInstanceKey c) env;
  pure $ instanceExtension.addEntry env { keys := keys, val := c }

def getInstances (env : Environment) : Instances :=
instanceExtension.getState env

@[init] def registerInstanceAttr : IO Unit :=
registerAttribute {
  name  := `instance,
  descr := "type class instance",
  add   := fun env declName args persistent => do
    unless args.isMissing $ throw (IO.userError ("invalid attribute 'instance', unexpected argument"));
    unless persistent $ throw (IO.userError ("invalid attribute 'instance', must be persistent"));
    env ← IO.ofExcept (addGlobalInstanceOld env declName); -- TODO: delete
    addGlobalInstance env declName
}

end Meta
end Lean
