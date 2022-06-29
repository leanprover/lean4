/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Path
import Lake.Config.InstallPath

open System
namespace Lake

/--
Initializes the search path the Lake executable
uses when interpreting package configuration files.

In order to use the Lean stdlib (e.g., `Init`),
the executable needs the search path to include the directory
with the stdlib's `.olean` files (e.g., from `<lean-home>/lib/lean`).
In order to use Lake's modules as well, the search path also
needs to include Lake's `.olean` files (e.g., from `build`).

While this can be done by having the user augment `LEAN_PATH` with
the necessary directories, Lake also intelligently augments the initial
search path with the `.olean` directories of the provided Lean and Lake
installations.

See `findInstall?` for more information on how Lake determines those
directories. If everything is configured as expected, the user will not
need to augment `LEAN_PATH`. Otherwise, they will need to provide Lake
with more information (either through `LEAN_PATH` or through other options).
-/
def setupLeanSearchPath
(leanInstall? : Option LeanInstall) (lakeInstall? : Option LakeInstall)
: IO Unit := do
  let mut sp : SearchPath := []
  sp ← Lean.addSearchPathFromEnv sp
  if let some leanInstall := leanInstall? then
    sp := leanInstall.oleanDir :: sp
  if let some lakeInstall := lakeInstall? then
    sp := lakeInstall.oleanDir :: sp
  Lean.searchPathRef.set sp
