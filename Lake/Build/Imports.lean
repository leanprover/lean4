/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module
import Lake.Config.Workspace

/-!
Definitions to support `lake print-paths` builds.
-/

namespace Lake

/--
Construct an `Array` of `Module`s for the workspace-local modules of
a `List` of import strings.
-/
def Workspace.processImportList
(imports : List String) (self : Workspace) : Array Module := Id.run do
  let mut localImports := #[]
  for imp in imports do
    if let some mod := self.findModule? imp.toName then
      localImports := localImports.push mod
  return localImports

/--
Build the workspace-local modules of list of imports.

Build only module `.olean` and `.ilean` files if
the default package build does not include any binary targets
Otherwise, also build `.c` files.
-/
def Package.buildImportsAndDeps (imports : List String) (self : Package) : BuildM PUnit := do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    buildPackageFacet self &`extraDep >>= (·.buildOpaque)
  else
    -- build local imports from list
    let mods := (← getWorkspace).processImportList imports
    if self.leanExes.isEmpty && self.defaultFacet matches .none | .leanLib | .oleans then
      let targets ← buildModuleFacetArray mods &`lean
      targets.forM (·.buildOpaque)
    else
      let targets ← buildModuleFacetArray mods &`lean.c
      targets.forM (·.buildOpaque)
