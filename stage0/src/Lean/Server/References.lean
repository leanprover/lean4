/-
Copyright (c) 2021 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/

import Init.System.IO
import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.Utils
import Lean.Server.InfoUtils
import Lean.Server.Snapshots

/- Representing collected and deduplicated definitions and usages -/

namespace Lean.Server
open Lsp

structure Reference where
  ident : RefIdent
  range : Lsp.Range
  isBinder : Bool
  deriving BEq, Inhabited

end Lean.Server

namespace Lean.Lsp.RefInfo
open Server

def empty : RefInfo := ⟨ none, #[] ⟩

def merge (a : RefInfo) (b : RefInfo) : RefInfo :=
  {
    definition := b.definition.orElse fun _ => a.definition
    usages := a.usages.append b.usages
  }

def addRef : RefInfo → Reference → RefInfo
  | i@{ definition := none, .. }, { range, isBinder := true, .. } =>
    { i with definition := range }
  | i@{ usages, .. }, { range, isBinder := false, .. } =>
    { i with usages := usages.push range }
  | i, _ => i

def contains (self : RefInfo) (pos : Lsp.Position) : Bool := Id.run do
  if let some range := self.definition then
    if contains range pos then
      return true
  for range in self.usages do
    if contains range pos then
      return true
  false
where
  contains (range : Lsp.Range) (pos : Lsp.Position) : Bool :=
    range.start <= pos && pos < range.end

end Lean.Lsp.RefInfo

namespace Lean.Lsp.ModuleRefs
open Server

def addRef (self : ModuleRefs) (ref : Reference) : ModuleRefs :=
  let refInfo := self.findD ref.ident RefInfo.empty
  self.insert ref.ident (refInfo.addRef ref)

def findAt (self : ModuleRefs) (pos : Lsp.Position) : Array RefIdent := Id.run do
  let mut result := #[]
  for (ident, info) in self.toList do
    if info.contains pos then
      result := result.push ident
  result

end Lean.Lsp.ModuleRefs

namespace Lean.Server
open IO
open Std
open Lsp
open Elab

/-- Content of individual `.ilean` files -/
structure Ilean where
  version : Nat := 1
  module : Name
  references : ModuleRefs
  deriving FromJson, ToJson

namespace Ilean

def load (path : System.FilePath) : IO Ilean := do
  let content ← FS.readFile path
  match Json.parse content >>= fromJson? with
    | Except.ok ilean => pure ilean
    | Except.error msg => throwServerError s!"Failed to load ilean at {path}: {msg}"

end Ilean
/- Collecting and deduplicating definitions and usages -/

def identOf : Info → Option (RefIdent × Bool)
  | Info.ofTermInfo ti => match ti.expr with
    | Expr.const n .. => some (RefIdent.const n, ti.isBinder)
    | Expr.fvar id .. => some (RefIdent.fvar id, ti.isBinder)
    | _ => none
  | Info.ofFieldInfo fi => some (RefIdent.const fi.projName, false)
  | _ => none

def findReferences (text : FileMap) (trees : Array InfoTree) : Array Reference := Id.run do
  let mut refs := #[]
  for tree in trees do
    refs := refs.appendList <| tree.deepestNodes fun _ info _ => Id.run do
      if let some (ident, isBinder) := identOf info then
        if let some range := info.range? then
          return some { ident, range := range.toLspRange text, isBinder }
      return none
  refs

/--
The `FVarId`s of a function parameter in the function's signature and body
differ. However, they have `TermInfo` nodes with `binder := true` in the exact
same position. Moreover, macros such as do-reassignment `x := e` may create
chains of variable definitions where a helper definition overlaps with a use
of a variable.

This function changes every such group to use a single `FVarId` (the head of the
chain/DAG) and gets rid of duplicate definitions.
-/
partial def combineFvars (refs : Array Reference) : Array Reference := Id.run do
  -- Deduplicate definitions based on their exact range
  let mut posMap : HashMap Lsp.Range FVarId := HashMap.empty
  for ref in refs do
    if let { ident := RefIdent.fvar id, range, isBinder := true } := ref then
      posMap := posMap.insert range id

  -- Map fvar defs to overlapping fvar defs/uses
  -- NOTE: poor man's union-find; see also `findCanonicalBinder?`
  let mut idMap : HashMap FVarId FVarId := HashMap.empty
  for ref in refs do
    if let { ident := RefIdent.fvar baseId, range, .. } := ref then
      if let some id := posMap.find? range then
        let id := findCanonicalBinder idMap id
        let baseId := findCanonicalBinder idMap baseId
        if baseId != id then
          idMap := idMap.insert id baseId

  let mut refs' := #[]
  for ref in refs do
    match ref with
    | { ident := ident@(RefIdent.fvar id), range, isBinder } =>
      -- downgrade chained definitions to usages
      -- (we shouldn't completely remove them in case they do not have usages)
      let isBinder := isBinder && !idMap.contains id
      refs' := refs'.push { ident := applyIdMap idMap ident, range, isBinder }
    | _ =>
      refs' := refs'.push ref
  refs'
where
  findCanonicalBinder (idMap : HashMap FVarId FVarId) (id : FVarId) : FVarId :=
    match idMap.find? id with
    | some id' => findCanonicalBinder idMap id'  -- recursion depth is expected to be very low
    | none     => id

  applyIdMap : HashMap FVarId FVarId → RefIdent → RefIdent
    | m, RefIdent.fvar id => RefIdent.fvar <| findCanonicalBinder m id
    | _, ident => ident

def dedupReferences (refs : Array Reference) : Array Reference := Id.run do
  let mut refsByIdAndRange : HashMap (RefIdent × Lsp.Range) Reference := HashMap.empty
  for ref in refs do
    if ref.isBinder || !(refsByIdAndRange.contains (ref.ident, ref.range)) then
      refsByIdAndRange := refsByIdAndRange.insert (ref.ident, ref.range) ref

  let dedupedRefs := refsByIdAndRange.fold (init := #[]) fun refs _ ref => refs.push ref
  return dedupedRefs.qsort (·.range < ·.range)

def findModuleRefs (text : FileMap) (trees : Array InfoTree) (localVars : Bool := true)
    : ModuleRefs := Id.run do
  let mut refs := dedupReferences <| combineFvars <| findReferences text trees
  if !localVars then
    refs := refs.filter fun
      | { ident := RefIdent.fvar _, .. } => false
      | _ => true
  refs.foldl (init := HashMap.empty) fun m ref => m.addRef ref

/- Collecting and maintaining reference info from different sources -/

structure References where
  /-- References loaded from ilean files -/
  ileans : HashMap Name (System.FilePath × ModuleRefs)
  /-- References from workers, overriding the corresponding ilean files -/
  workers : HashMap Name (Nat × ModuleRefs)

namespace References

def empty : References := { ileans := HashMap.empty, workers := HashMap.empty }

def addIlean (self : References) (path : System.FilePath) (ilean : Ilean) : References :=
  { self with ileans := self.ileans.insert ilean.module (path, ilean.references) }

def removeIlean (self : References) (path : System.FilePath) : References :=
  let namesToRemove := self.ileans.toList.filter (fun (_, p, _) => p == path)
    |>.map (fun (n, _, _) => n)
  namesToRemove.foldl (init := self) fun self name =>
    { self with ileans := self.ileans.erase name }

def updateWorkerRefs (self : References) (name : Name) (version : Nat) (refs : ModuleRefs) : References := Id.run do
  if let some (currVersion, _) := self.workers.find? name then
    if version > currVersion then
      return { self with workers := self.workers.insert name (version, refs) }
    if version == currVersion then
      let current := self.workers.findD name (version, HashMap.empty)
      let merged := refs.fold (init := current.snd) fun m ident info =>
        m.findD ident RefInfo.empty |>.merge info |> m.insert ident
      return { self with workers := self.workers.insert name (version, merged) }
  return self

def finalizeWorkerRefs (self : References) (name : Name) (version : Nat) (refs : ModuleRefs) : References := Id.run do
  if let some (currVersion, _) := self.workers.find? name then
    if version < currVersion then
      return self
  return { self with workers := self.workers.insert name (version, refs) }

def removeWorkerRefs (self : References) (name : Name) : References :=
  { self with workers := self.workers.erase name }

def allRefs (self : References) : HashMap Name ModuleRefs :=
  let ileanRefs := self.ileans.toList.foldl (init := HashMap.empty) fun m (name, _, refs) => m.insert name refs
  self.workers.toList.foldl (init := ileanRefs) fun m (name, _, refs) => m.insert name refs

def findAt (self : References) (module : Name) (pos : Lsp.Position) : Array RefIdent := Id.run do
  if let some refs := self.allRefs.find? module then
    return refs.findAt pos
  #[]

def referringTo (self : References) (identModule : Name) (ident : RefIdent) (srcSearchPath : SearchPath)
    (includeDefinition : Bool := true) : IO (Array Location) := do
  let refsToCheck := match ident with
    | RefIdent.const _ => self.allRefs.toList
    | RefIdent.fvar _ => match self.allRefs.find? identModule with
      | none => []
      | some refs => [(identModule, refs)]
  let mut result := #[]
  for (module, refs) in refsToCheck do
    if let some info := refs.find? ident then
      if let some path ← srcSearchPath.findModuleWithExt "lean" module then
        -- Resolve symlinks (such as `src` in the build dir) so that files are
        -- opened in the right folder
        let uri := DocumentUri.ofPath <| ← IO.FS.realPath path
        if includeDefinition then
          if let some range := info.definition then
            result := result.push ⟨uri, range⟩
        for range in info.usages do
          result := result.push ⟨uri, range⟩
  return result

def definitionOf? (self : References) (ident : RefIdent) (srcSearchPath : SearchPath)
    : IO (Option Location) := do
  for (module, refs) in self.allRefs.toList do
    if let some info := refs.find? ident then
      if let some definition := info.definition then
        if let some path ← srcSearchPath.findModuleWithExt "lean" module then
          -- Resolve symlinks (such as `src` in the build dir) so that files are
          -- opened in the right folder
          let uri := DocumentUri.ofPath <| ← IO.FS.realPath path
          return some ⟨uri, definition⟩
  return none

def definitionsMatching (self : References) (srcSearchPath : SearchPath) (filter : Name → Option α)
    (maxAmount? : Option Nat := none) : IO $ Array (α × Location) := do
  let mut result := #[]
  for (module, refs) in self.allRefs.toList do
    if let some path ← srcSearchPath.findModuleWithExt "lean" module then
      let uri := DocumentUri.ofPath <| ← IO.FS.realPath path
      for (ident, info) in refs.toList do
        if let (RefIdent.const name, some definition) := (ident, info.definition) then
          if let some a := filter name then
            result := result.push (a, ⟨uri, definition⟩)
            if let some maxAmount := maxAmount? then
              if result.size >= maxAmount then
                return result
  return result

end References

end Lean.Server
