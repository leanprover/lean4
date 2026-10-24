import Lean

/-!
The instances imported from per-module data (`InstanceModuleIndex`) equal those obtained by adding
each imported entry in module order, down to the order of instances in the discrimination tree, and
imported instance names are looked up in per-module arrays when all imported modules store their
summaries.
-/

open Lean Meta

def sequentialInstances (env : Environment) : Instances :=
  (instanceExtension.ext.toEnvExtension.getState env).importedEntries.foldl (init := {}) fun d es =>
    es.foldl (init := d) fun d e => match e with
      | .global e => addInstanceEntry d e
      | _ => d

def entryInfo (e : InstanceEntry) : Option Name × Nat × Array Nat :=
  (e.globalName?, e.priority, e.synthOrder)

def sortedNames (ns : List Name) : List Name :=
  ns.toArray.qsort Name.lt |>.toList

def sameInstances (d₁ d₂ : Instances) : Bool :=
  d₁.discrTree.toArray.map (fun (ks, e) => (ks, entryInfo e)) ==
    d₂.discrTree.toArray.map (fun (ks, e) => (ks, entryInfo e)) &&
  sortedNames (d₁.instanceNames.toList.map (·.1)) == sortedNames (d₂.instanceNames.toList.map (·.1)) &&
  d₂.instanceNames.toList.all (fun (n, e) => (d₁.instanceNames.find? n).map entryInfo == some (entryInfo e)) &&
  d₁.instanceNames.isEmpty == d₂.instanceNames.isEmpty &&
  sortedNames d₁.erased.toList == sortedNames d₂.erased.toList

/--
Whether all imported modules with global entries store a summary, without which the per-module data
is not used (e.g. at stage 1, whose core library is exported by stage 0).
-/
def allIndexed (entries : Array (Array (ScopedEnvExtension.Entry α))) : Bool :=
  entries.all fun es =>
    ((es[0]? : Option (ScopedEnvExtension.Entry α)) matches some (.index _)) || !es.any (· matches .global _)

#eval show CoreM Unit from do
  let env ← getEnv
  let d := instanceExtension.getState env
  unless sameInstances d (sequentialInstances env) do
    throwError "instances differ from the sequentially built ones"
  unless d.discrTree.size > 5000 do throwError "too few instances: {d.discrTree.size}"
  let indexed := allIndexed (instanceExtension.ext.toEnvExtension.getState env).importedEntries
  unless d.instanceNames.imported.ownedKeys.isEmpty != indexed do
    throwError "unexpected representation of imported instance names"
