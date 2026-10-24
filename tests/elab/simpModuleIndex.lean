import Lean

/-!
The simp sets built at import from per-module theorem trees (`SimpModuleIndex`) equal those obtained
by adding each imported entry in module order, down to the order of theorems in the trees.
-/

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

def sameState (d₁ d₂ : SimpTheorems) : Bool :=
  treeContents d₁.pre == treeContents d₂.pre &&
  treeContents d₁.post == treeContents d₂.post &&
  d₁.lemmaNames.toList.map (·.key) == d₂.lemmaNames.toList.map (·.key) &&
  d₁.erased.toList.map (·.key) == d₂.erased.toList.map (·.key) &&
  sortedNames d₁.toUnfold.toList == sortedNames d₂.toUnfold.toList &&
  sortedNames (d₁.toUnfoldThms.toList.map (·.1)) == sortedNames (d₂.toUnfoldThms.toList.map (·.1))

#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  for (attr, ext) in (← simpExtensionMapRef.get) do
    let d := ext.getState env
    unless sameState d (sequentialState ext env) do
      throwError "simp set `{attr}` differs from the sequentially built one"
    n := n + d.pre.size + d.post.size
  -- make sure the comparison covered the default simp set
  unless n > 10000 do throwError "too few simp theorems: {n}"
