/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.System.IO

open System
namespace Lake

/-- The shared library file extension for the `Platform`. -/
def sharedLibExt : String :=
  if Platform.isWindows then "dll"
  else if Platform.isOSX  then "dylib"
  else "so"

/-- Convert a library name into its static library file name for the `Platform`. -/
def nameToStaticLib (name : String) : String :=
  if Platform.isWindows then s!"{name}.a" else s!"lib{name}.a"

/-- Convert a library name into its shared library file name for the `Platform`. -/
def nameToSharedLib (name : String) : String :=
  if Platform.isWindows then s!"{name}.dll"
  else if Platform.isOSX  then s!"lib{name}.dylib"
  else s!"lib{name}.so"

/--
The environment variable that stores the search path
used to find shared libraries on the `Platform`.
-/
def sharedLibPathEnvVar :=
  if Platform.isWindows then
    "PATH"
  else if Platform.isOSX then
    "DYLD_LIBRARY_PATH"
  else
    "LD_LIBRARY_PATH"

/-- Gets a `SearchPath` from an environment variable. -/
def getSearchPath (envVar : String) : BaseIO SearchPath := do
  match (← IO.getEnv envVar) with
  | some path => pure <| SearchPath.parse path
  | none => pure []
