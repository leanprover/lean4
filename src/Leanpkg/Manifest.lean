/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Leanpkg.Toml
import Leanpkg.LeanVersion

open System

namespace Leanpkg

inductive Source where
  | path (dir : System.FilePath) : Source
  | git (url rev : String) (branch : Option String) : Source

namespace Source

def fromToml (v : Toml.Value) : OptionM Source :=
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

structure Dependency where
  name : String
  src : Source

structure Manifest where
  name : String
  version : String
  leanVersion : String := leanVersionString
  timeout : Option Nat := none
  path : Option FilePath := none
  dependencies : List Dependency := []

namespace Manifest

def effectivePath (m : Manifest) : FilePath :=
  m.path.getD ⟨"."⟩

def fromToml (t : Toml.Value) : Option Manifest := OptionM.run do
  let pkg ← t.lookup "package"
  let Toml.Value.str n ← pkg.lookup "name" | none
  let Toml.Value.str ver ← pkg.lookup "version" | none
  let leanVer ← match pkg.lookup "lean_version" with
    | some (Toml.Value.str leanVer) => some leanVer
    | none => some leanVersionString
    | _ => none
  let tm ← match pkg.lookup "timeout" with
    | some (Toml.Value.nat timeout) => some (some timeout)
    | none => some none
    | _ => none
  let path ← match pkg.lookup "path" with
    | some (Toml.Value.str path) => some (some ⟨path⟩)
    | none => some none
    | _ => none
  let Toml.Value.table deps ← t.lookup "dependencies" <|> some (Toml.Value.table []) | none
  let deps ← deps.mapM fun ⟨n, src⟩ => do Dependency.mk n (← Source.fromToml src)
  return { name := n, version := ver, leanVersion := leanVer,
           path := path, dependencies := deps, timeout := tm }

def fromFile (fn : System.FilePath) : IO Manifest := do
  let cnts ← IO.FS.readFile fn
  let toml ← Toml.parse cnts
  let some manifest ← pure (fromToml toml)
    | throw <| IO.userError s!"cannot read manifest from {fn}"
  manifest

end Manifest

def leanpkgTomlFn : System.FilePath := ⟨"leanpkg.toml"⟩

end Leanpkg
