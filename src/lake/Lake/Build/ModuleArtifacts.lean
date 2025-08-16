/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Trace
public import Lake.Config.Artifact
import Lake.Util.JsonObject

open Lean (Json ToJson FromJson)

namespace Lake

/-- The content hashes of the output artifacts of a module build. -/
public structure ModuleOutputHashes where
  olean : Hash := .nil
  oleanServer? : Option Hash := none
  oleanPrivate? : Option Hash := none
  ilean : Hash := .nil
  ir? : Option Hash := none
  c : Hash := .nil
  bc? : Option Hash := none

public def ModuleOutputHashes.oleanHashes (hashes : ModuleOutputHashes) : Array Hash := Id.run do
  let mut oleanHashes := #[hashes.olean]
  if let some hash := hashes.oleanServer? then
    oleanHashes := oleanHashes.push hash
  if let some hash := hashes.oleanPrivate? then
    oleanHashes := oleanHashes.push hash
  return oleanHashes

public protected def ModuleOutputHashes.toJson (hashes : ModuleOutputHashes) : Json := Id.run do
  let mut obj : JsonObject := {}
  obj := obj.insert "o" hashes.oleanHashes
  obj := obj.insert "i" hashes.ilean
  if let some ir := hashes.ir? then
    obj := obj.insert "r" ir
  obj := obj.insert "c" hashes.c
  if let some bc := hashes.bc? then
    obj := obj.insert "b" bc
  return obj

public instance : ToJson ModuleOutputHashes := ⟨ModuleOutputHashes.toJson⟩

public protected def ModuleOutputHashes.fromJson? (val : Json) : Except String ModuleOutputHashes := do
  let obj ← JsonObject.fromJson? val
  let oleanHashes : Array Hash ← obj.get "o"
  let some olean := oleanHashes[0]?
    | throw "expected a least one 'o' (OLean) hash"
  return {
    olean := olean
    oleanServer? := oleanHashes[1]?
    oleanPrivate? := oleanHashes[2]?
    ilean := ← obj.get "i"
    ir? := ← obj.get? "r"
    c := ← obj.get "c"
    bc? := ← obj.get? "b"
  }

public instance : FromJson ModuleOutputHashes := ⟨ModuleOutputHashes.fromJson?⟩

/-- The output artifacts of a module build. -/
public structure ModuleOutputArtifacts where
  olean : Artifact
  oleanServer? : Option Artifact := none
  oleanPrivate? : Option Artifact := none
  ilean : Artifact
  ir? : Option Artifact := none
  c : Artifact
  bc? : Option Artifact := none

/-- Content hashes of the artifacts. -/
public def ModuleOutputArtifacts.hashes (arts : ModuleOutputArtifacts) : ModuleOutputHashes where
  olean := arts.olean.hash
  oleanServer? := arts.oleanServer?.map (·.hash)
  oleanPrivate? := arts.oleanPrivate?.map (·.hash)
  ilean := arts.ilean.hash
  ir? := arts.ir?.map (·.hash)
  c := arts.c.hash
  bc? := arts.bc?.map (·.hash)
