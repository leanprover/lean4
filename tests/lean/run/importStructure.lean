import Lean
import Std

open Std Lean

/-!
This test analyzes the import structure of the modules in core and fails if it detects something
wrong.

Currently, we only test the following:
* There are no orphaned modules
* No module in `Init` or `Std` (transitively) imports `Init.Data.Option.Coe`.
-/

/-- Collects the module names corresponding to all `lean` files in the file system. -/
partial def collectModulesOnFileSystem (sysroot : System.FilePath) (roots : Array String) :
    IO (Array String) :=
  roots.flatMapM (fun (root : String) => go (sysroot / "lib" / "lean" / root) root #[])
where
  go (dir : System.FilePath) (pref : String) (sofar : Array String) : IO (Array String) := do
    if !(← dir.pathExists) then
      return sofar

    let mut arr := sofar
    for entry in ← dir.readDir do
      let mdata ← entry.path.metadata
      match mdata.type with
      | .dir => arr ← go entry.path (pref ++ "." ++ entry.fileName) arr
      | .file =>
          if entry.path.extension == some "olean" then
            arr := arr.push (pref ++ "." ++ entry.path.fileStem.get!)
      | _ => pure ()
    return arr

partial def dfs (cur : String) (graph : HashMap String (Array String)) (seen : HashSet String) :
    HashSet String := Id.run do
  if cur ∈ seen then
    return seen

  let mut seen' := seen.insert cur
  for next in graph.getD cur #[] do
    seen' := dfs next graph seen'

  return seen'

structure ImportGraph where
  imports : HashMap String (Array String)
  reverseImports : HashMap String (Array String)

def analyzeModuleData (data : Array (Name × ModuleData)) : ImportGraph := Id.run do
  let mut result : ImportGraph := ⟨∅, ∅⟩

  for (name, module) in data do
    for imp in module.imports do
      let fromString := name.toString
      let toString := imp.module.toString
      result := {
        imports := result.imports.alter fromString
          (fun arr => some <| (arr.getD #[]).push toString)
        reverseImports := result.reverseImports.alter toString
          (fun arr => some <| (arr.getD #[]).push fromString)
      }

  result

def computeOrphanedModules (sysroot : System.FilePath) (importGraph : ImportGraph) :
    IO (Array String) := do
  let onFS ← collectModulesOnFileSystem sysroot #["Init", "Std", "Lean"]
  let imported : HashSet String := #["Init", "Std", "Lean"].foldl (init := ∅)
    (fun sofar root => sofar.insertMany (dfs root importGraph.imports ∅))
  return onFS.filter (fun module => !imported.contains module)

def computeIllegalReverseImportsOfInitDataOptionCoe (importGraph : ImportGraph) :
    Array String :=
  let reverseImports := dfs "Init.Data.Option.Coe" importGraph.reverseImports ∅
  reverseImports.toArray.filter isBannedModule
where
  isBannedModule (moduleName : String) : Bool :=
    (moduleName.startsWith "Init." || moduleName.startsWith "Std.") && !allowList.contains moduleName
  allowList : HashSet String :=
    .ofList ["Init.Data.Option.Coe", "Init.Data.Option", "Init.Data"]

def test : MetaM Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let env ← importModules #[`Init, `Std, `Lean] {}
  let importGraph := analyzeModuleData (env.header.moduleNames.zip env.header.moduleData)

  let orphanedModules ← computeOrphanedModules sysroot importGraph
  if !orphanedModules.isEmpty then do
    logError s!"There are orphaned modules: {orphanedModules}"

  let illegalReverseImports := computeIllegalReverseImportsOfInitDataOptionCoe importGraph
  if !illegalReverseImports.isEmpty then do
    logError s!"The following modules illegally (transitively) import Init.Data.Option.Coe: {illegalReverseImports}"

/-!
We check which modules exist by looking at which `olean` files are present in the file system.
This means that locally you might get false positives on this test because there are some `olean`
files still floating around where the corresponding `lean` file no longer exists in the source.

It would be better to check for `lean` files directly, but our CI step which runs the tests doesn't
see the source files in the `srcPath`.
-/

#guard_msgs in
#eval test
