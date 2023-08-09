/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Facets
import Lake.Config.LeanConfig

namespace Lake
open Lean System

/-- A Lean executable's declarative configuration. -/
structure LeanExeConfig extends LeanConfig where
  /-- The name of the target. -/
  name : Name

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
  An `Array` of module facets to build and combine into the executable.
  Defaults to ``#[Module.oFacet]`` (i.e., the object file compiled from
  the Lean source).
  -/
  nativeFacets : Array (ModuleFacet (BuildJob FilePath)) := #[Module.oFacet]

  /--
  Whether to expose symbols within the executable to the Lean interpreter.
  This allows the executable to interpret Lean files (e.g.,  via
  `Lean.Elab.runFrontend`).

  Implementation-wise, this passes `-rdynamic` to the linker when building
  on non-Windows systems.

  Defaults to `false`.
  -/
  supportInterpreter : Bool := false

deriving Inhabited
