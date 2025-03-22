/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Facets
import Lake.Config.LeanConfig

namespace Lake
open Lean System

/-- A Lean executable's declarative configuration. -/
configuration LeanExeConfig (name : Name) extends LeanConfig where
  /--
  The subdirectory of the package's source directory containing the executable's
  Lean source file. Defaults simply to said `srcDir`.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The root module of the binary executable.
  Should include a `main` definition that will serve
  as the entry point of the program.

  The root is built by recursively building its
  local imports (i.e., fellow modules of the workspace).

  Defaults to the name of the target.
  -/
  root : Name := name

  /--
  The name of the binary executable.
  Defaults to the target name with any `.` replaced with a `-`.
  -/
  exeName : String := name.toStringWithSep "-" (escape := false)

  /-- An `Array` of target names to build before the executable's modules. -/
  extraDepTargets : Array Name := #[]

  /--
  Enables the executable to interpret Lean files (e.g., via
  `Lean.Elab.runFrontend`) by exposing symbols within the  executable
  to the Lean interpreter.

  Implementation-wise, on Windows, the Lean shared libraries are linked
  to the executable and, on other systems, the executable is linked with
  `-rdynamic`. This increases the size of the binary on Linux and, on Windows,
  requires `libInit_shared.dll` and `libleanshared.dll` to  be co-located
  with the executable or part of `PATH` (e.g., via `lake exe`). Thus, this
  feature should only be enabled when necessary.

  Defaults to `false`.
  -/
  supportInterpreter : Bool := false

  /--
  The module facets to build and combine into the executable.
  If `shouldExport` is true, the module facets should export any symbols
  a user may expect to lookup in the executable. For example, the Lean
  interpreter will use exported symbols in the executable. Thus, `shouldExport`
  will be `true` if `supportInterpreter := true`.

  Defaults to a singleton of `Module.oExportFacet` (if `shouldExport`) or
  `Module.oFacet`. That is, the  object file compiled from the Lean source,
  potentially with exported Lean symbols.
  -/
  nativeFacets (shouldExport : Bool) : Array (ModuleFacet FilePath) :=
    #[if shouldExport then Module.oExportFacet else Module.oFacet]

deriving Inhabited

instance : EmptyCollection (LeanExeConfig n) := ⟨{}⟩

/-- The executable's name. -/
abbrev LeanExeConfig.name (_ : LeanExeConfig n) := n
