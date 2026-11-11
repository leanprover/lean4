import Lean

open Lean Meta

def sequentialState (ext : SimpExtension) (env : Environment) : SimpTheorems :=
  (ext.ext.toEnvExtension.getState env).importedEntries.foldl (init := {}) fun d es =>
    es.foldl (init := d) fun d e => match e with
      | .global e => d.addSimpEntry e
      | _ => d

def treeContents (t : SimpTheoremTree) : Array (Array DiscrTree.Key × Name × Nat × Bool × Bool) :=
  t.toArray.map fun (ks, thm) => (ks, thm.origin.key, thm.priority, thm.post, thm.perm)

def sortedNames (ns : List Name) : List Name :=
  ns.toArray.qsort Name.lt |>.toList

def originSet (os : List Origin) : List (Name × Bool) :=
  let os := os.toArray.map fun o => match o with
    | .decl n _ inv => (n, inv)
    | o => (o.key, false)
  os.qsort (fun a b => Name.lt a.1 b.1 || (a.1 == b.1 && !a.2 && b.2)) |>.toList

def sameState (d₁ d₂ : SimpTheorems) : Bool :=
  treeContents d₁.pre == treeContents d₂.pre &&
  treeContents d₁.post == treeContents d₂.post &&
  originSet d₁.lemmaNames.toList == originSet d₂.lemmaNames.toList &&
  d₂.lemmaNames.toList.all d₁.lemmaNames.contains &&
  originSet (d₁.lemmaNames.fold (fun l o => o :: l) []) == originSet d₂.lemmaNames.toList &&
  d₁.lemmaNames.isEmpty == d₂.lemmaNames.isEmpty &&
  originSet d₁.erased.toList == originSet d₂.erased.toList &&
  sortedNames d₁.toUnfold.toList == sortedNames d₂.toUnfold.toList &&
  sortedNames (d₁.toUnfoldThms.toList.map (·.1)) == sortedNames (d₂.toUnfoldThms.toList.map (·.1))

/-- Whether module `i` stores a summary of its entries of `ext`. -/
def hasSummary [Inhabited σ] (ext : ScopedEnvExtension α β σ) (env : Environment) (i : Nat) :
    IO Bool := do
  let some idx := (← persistentEnvExtensionsRef.get).find? (·.name == ext.ext.name ++ `moduleSummary)
    | throw <| .userError s!"no summary extension for {ext.ext.name}"
  return !(idx.getModuleEntries env (i : ModuleIdx)).isEmpty

/--
Whether all imported modules with global entries of `ext` store a summary, without which the
summaries are not used (e.g. at stage 1, whose core library is exported by stage 0).
-/
def allSummarized [Inhabited σ] (ext : ScopedEnvExtension α β σ) (env : Environment) : IO Bool := do
  let entries := (ext.ext.toEnvExtension.getState env).importedEntries
  let mut ok := true
  for h : i in [0:entries.size] do
    if entries[i].any (· matches .global _) && !(← hasSummary ext env i) then
      ok := false
  return ok

def sequentialInstances (env : Environment) : Instances :=
  (instanceExtension.ext.toEnvExtension.getState env).importedEntries.foldl (init := {}) fun d es =>
    es.foldl (init := d) fun d e => match e with
      | .global e => addInstanceEntry d e
      | _ => d

def entryInfo (e : InstanceEntry) : Option Name × Nat × Array Nat :=
  (e.globalName?, e.priority, e.synthOrder)

def sameInstances (d₁ d₂ : Instances) : Bool :=
  d₁.discrTree.toArray.map (fun (ks, e) => (ks, entryInfo e)) ==
    d₂.discrTree.toArray.map (fun (ks, e) => (ks, entryInfo e)) &&
  sortedNames (d₁.instanceNames.toList.map (·.1)) == sortedNames (d₂.instanceNames.toList.map (·.1)) &&
  d₂.instanceNames.toList.all (fun (n, e) => (d₁.instanceNames.find? n).map entryInfo == some (entryInfo e)) &&
  d₁.instanceNames.isEmpty == d₂.instanceNames.isEmpty &&
  sortedNames d₁.erased.toList == sortedNames d₂.erased.toList

/-- Checks that the given modules store their instance summaries and that the imported instances equal the sequentially built ones. -/
def checkInstances (mods : List Name) : MetaM Unit := do
  let env ← getEnv
  for mod in mods do
    let some modIdx := env.getModuleIdx? mod | throwError "{mod} not imported"
    unless ← hasSummary instanceExtension env modIdx.toNat do
      throwError "{mod} has no stored instance summary"
  let d := instanceExtension.getState env
  unless sameInstances d (sequentialInstances env) do
    throwError "instances differ from the sequentially built ones"
  let summarized ← allSummarized instanceExtension env
  unless d.instanceNames.imported.ownedKeys.isEmpty != summarized do
    throwError "unexpected representation of imported instance names"

/--
Checks that the given modules store their simp summaries, that all simp sets equal the sequentially
built ones, and whether imported lemma names are looked up per module (`perModule`, if all imported
modules store summaries) or were replayed.
-/
def checkSimpSets (mods : List Name) (perModule : Bool) : MetaM Unit := do
  let env ← getEnv
  for mod in mods do
    let some modIdx := env.getModuleIdx? mod | throwError "{mod} not imported"
    unless ← hasSummary simpExtension env modIdx.toNat do
      throwError "{mod} has no stored summary"
  for (attr, ext) in (← simpExtensionMapRef.get) do
    unless sameState (ext.getState env) (sequentialState ext env) do
      throwError "simp set `{attr}` differs from the sequentially built one"
  let summarized ← allSummarized simpExtension env
  unless (← getSimpTheorems).lemmaNames.imported.ownedKeys.isEmpty != (perModule && summarized) do
    throwError "unexpected representation of imported lemma names"
