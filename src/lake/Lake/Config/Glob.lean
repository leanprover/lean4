/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Mac Malone
-/
prelude
import Lean.Util.Path
import Lake.Util.Name

open Lean (Name)
open System (FilePath)

namespace Lake

/-- A specification of a set of module names. -/
inductive Glob
  /-- Selects just the specified module name. -/
  | one : Name → Glob
  /-- Selects all submodules of the specified module, but not the module itself. -/
  | submodules : Name → Glob
  /-- Selects the specified module and all submodules. -/
  | andSubmodules : Name → Glob
deriving Inhabited, Repr, DecidableEq

instance : Coe Name Glob := ⟨Glob.one⟩
instance : Coe Glob (Array Glob) := ⟨Array.singleton⟩

/-- A name glob which matches all names with the prefix, including itself. -/
scoped macro:max n:name noWs ".*" : term =>
  ``(Glob.andSubmodules $(⟨Lean.mkNode `Lean.Parser.Term.quotedName #[n]⟩))

/-- A name glob which matches all names with the prefix, but not the prefix itself. -/
scoped macro:max n:name noWs ".+" : term =>
  ``(Glob.submodules $(⟨Lean.mkNode `Lean.Parser.Term.quotedName #[n]⟩))

namespace Glob

protected def toString : Glob → String
| .one n => n.toString
| .submodules n => n.toString ++ ".+"
| .andSubmodules n => n.toString ++ ".*"

instance : ToString Glob := ⟨Glob.toString⟩

def «matches» (m : Name) : (self : Glob) → Bool
| one n => n == m
| submodules n => n.isPrefixOf m && n != m
| andSubmodules n => n.isPrefixOf m

@[inline] nonrec def forEachModuleIn [Monad m] [MonadLiftT IO m]
(dir : FilePath) (f : Name → m PUnit) : (self : Glob) → m PUnit
| one n => f n
| submodules n =>
  Lean.forEachModuleInDir (Lean.modToFilePath dir n "") (f <| n ++ ·)
| andSubmodules n =>
  f n *> Lean.forEachModuleInDir (Lean.modToFilePath dir n "") (f <| n ++ ·)
