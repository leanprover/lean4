import Lean

/-!
The instances imported from per-module data (`InstanceModuleIndex`) equal those obtained by adding
each imported entry in module order, down to the order of instances in the discrimination tree, and
imported instance names are looked up in per-module arrays.
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

#eval show CoreM Unit from do
  let env ← getEnv
  let d := instanceExtension.getState env
  unless sameInstances d (sequentialInstances env) do
    throwError "instances differ from the sequentially built ones"
  unless d.discrTree.size > 5000 do throwError "too few instances: {d.discrTree.size}"
  if d.instanceNames.imported.owned.isEmpty then
    throwError "imported instance names were not looked up per module"
