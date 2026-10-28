import Lean

/-!
The simp sets built at import from per-module theorem trees (`SimpModuleIndex`) equal those obtained
by adding each imported entry in module order, down to the order of theorems in the trees, and
that imported lemma names are looked up in per-module arrays when all imported modules store their
summaries.
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

/--
Whether all imported modules with global entries store a summary, without which the per-module data
is not used (e.g. at stage 1, whose core library is exported by stage 0).
-/
def allIndexed (entries : Array (Array (ScopedEnvExtension.Entry α))) : Bool :=
  entries.all fun es =>
    ((es[0]? : Option (ScopedEnvExtension.Entry α)) matches some (.index _)) || !es.any (· matches .global _)

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
  -- no constant is a simp theorem in both directions, so lemma names are looked up per module
  -- whenever the summaries are used
  let indexed := allIndexed (simpExtension.ext.toEnvExtension.getState env).importedEntries
  unless (← getSimpTheorems).lemmaNames.imported.ownedKeys.isEmpty != indexed do
    throwError "unexpected representation of imported lemma names"
