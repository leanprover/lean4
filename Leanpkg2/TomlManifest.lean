/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Toml
import Leanpkg2.LeanVersion
import Leanpkg2.Manifest

open System

namespace Leanpkg2

namespace Source

def fromToml (v : Toml.Value) : Option Source :=
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

namespace Manifest

def fromToml (t : Toml.Value) : Option Manifest := OptionM.run do
  let pkg ← t.lookup "package"
  let Toml.Value.str name ← pkg.lookup "name" | none
  let Toml.Value.str version ← pkg.lookup "version" | none
  let module := match pkg.lookup "module" with
    | some (Toml.Value.str mod) => mod
    | _ => name.capitalize
  let leanVersion ← match pkg.lookup "lean_version" with
    | some (Toml.Value.str leanVer) => some leanVer
    | none => some leanVersionString
    | _ => none
  let timeout ← match pkg.lookup "timeout" with
    | some (Toml.Value.nat timeout) => some (some timeout)
    | none => some none
    | _ => none
  let path ← match pkg.lookup "path" with
    | some (Toml.Value.str path) => some (some ⟨path⟩)
    | none => some none
    | _ => none
  let Toml.Value.table deps ← t.lookup "dependencies" <|> some (Toml.Value.table []) | none
  let dependencies ← deps.mapM fun ⟨n, src⟩ => do Dependency.mk n (← Source.fromToml src)
  return { name, module, version, leanVersion, path, dependencies, timeout }

def fromTomlFile (fn : System.FilePath) : IO Manifest := do
  let cnts ← IO.FS.readFile fn
  let toml ← Toml.parse cnts
  let some manifest ← pure (fromToml toml)
    | throw <| IO.userError s!"cannot read manifest from {fn}"
  manifest

end Manifest

def leanpkgToml : System.FilePath := "leanpkg.toml"

def readManifest : IO Manifest := do
  let m ← Manifest.fromTomlFile leanpkgToml
  if m.leanVersion ≠ leanVersionString then
    IO.eprintln $ "\nWARNING: Lean version mismatch: installed version is " ++ leanVersionString
       ++ ", but package requires " ++ m.leanVersion ++ "\n"
  return m

def writeManifest (manifest : Lean.Syntax) (fn : FilePath) : IO Unit := do
  IO.FS.writeFile fn manifest.reprint.get!
