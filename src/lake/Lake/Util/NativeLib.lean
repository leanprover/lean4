/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO
import Init.Data.ToString.Macro
import Init.System.Platform

open System
namespace Lake

/-- The shared library file extension for the `Platform`. -/
public def sharedLibExt : String :=
  if Platform.isWindows then "dll"
  else if Platform.isOSX  then "dylib"
  else "so"

/-- Convert a library name into its static library file name for the `Platform`. -/
public def nameToStaticLib (name : String) (libPrefixOnWindows := false) : String :=
  if libPrefixOnWindows || !System.Platform.isWindows then s!"lib{name}.a" else s!"{name}.a"

/-- Convert a library name into its shared library file name for the `Platform`. -/
public def nameToSharedLib (name : String) (libPrefixOnWindows := false) : String :=
  let libPrefix := if libPrefixOnWindows || !System.Platform.isWindows then "lib" else ""
  s!"{libPrefix}{name}.{sharedLibExt}"

/--
The environment variable that stores the search path
used to find shared libraries on the `Platform`.
-/
public def sharedLibPathEnvVar : String :=
  if Platform.isWindows then
    "PATH"
  else if Platform.isOSX then
    "DYLD_LIBRARY_PATH"
  else
    "LD_LIBRARY_PATH"

/-- Gets a `SearchPath` from an environment variable. -/
public def getSearchPath (envVar : String) : BaseIO SearchPath := do
  match (← IO.getEnv envVar) with
  | some path => pure <| SearchPath.parse path
  | none => pure []
