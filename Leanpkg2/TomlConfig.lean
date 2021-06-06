/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Toml
import Leanpkg2.LeanVersion
import Leanpkg2.Package

open System

namespace Leanpkg2

def leanpkgToml : FilePath := "leanpkg.toml"

namespace Source

def fromToml? (v : Toml.Value) : Option Source :=
  (do let Toml.Value.str dir ← v.lookup "path" | none
      path ⟨dir⟩) <|>
  (do let Toml.Value.str url ← v.lookup "git" | none
      let Toml.Value.str rev ← v.lookup "rev" | none
      match v.lookup "branch" with
      | none                         => git url rev none
      | some (Toml.Value.str branch) => git url rev (some branch)
      | _ => none)

def toToml : Source → Toml.Value
  | path dir => Toml.Value.table [("path", Toml.Value.str dir.toString)]
  | git url rev none =>
    Toml.Value.table [("git", Toml.Value.str url), ("rev", Toml.Value.str rev)]
  | git url rev (some branch) =>
    Toml.Value.table [("git", Toml.Value.str url), ("branch", Toml.Value.str branch), ("rev", Toml.Value.str rev)]

end Source

namespace PackageConfig

def fromToml? (t : Toml.Value) : Option PackageConfig := OptionM.run do
  let pkg ← t.lookup "package"
  let Toml.Value.str name ← pkg.lookup "name" | none
  let Toml.Value.str version ← pkg.lookup "version" | none
  let module ← match pkg.lookup "module" with
    | some (Toml.Value.str mod) => mod
    | none => some name.capitalize
    | _ => none
  let leanVersion ← match pkg.lookup "lean_version" with
    | some (Toml.Value.str leanVer) => some leanVer
    | none => some leanVersionString
    | _ => none
  let timeout ← match pkg.lookup "timeout" with
    | some (Toml.Value.nat timeout) => some (some timeout)
    | none => some none
    | _ => none
  let Toml.Value.table deps ← t.lookup "dependencies" <|> some (Toml.Value.table []) | none
  let dependencies ← deps.mapM fun ⟨n, src⟩ => do Dependency.mk n (← Source.fromToml? src)
  return { name, module, version, leanVersion, dependencies, timeout }

def fromTomlString? (str : String) : IO (Option PackageConfig) := do
  fromToml? (← Toml.parse str)

def fromTomlFile? (path : FilePath) : IO (Option PackageConfig) := do
  fromTomlString? (← IO.FS.readFile path)

def fromTomlFile (path : FilePath) : IO PackageConfig := do
  let some config ← fromTomlFile? path
    | throw <| IO.userError s!"configuration (at {path}) is ill-formed"
  config

end PackageConfig
