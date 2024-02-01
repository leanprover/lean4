/-
Copyright (c) 2021 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/
import Lean.Data.Lsp.Internal
import Lean.Server.Utils

/-! # Representing collected and deduplicated definitions and usages -/

namespace Lean.Server
open Lsp Lean.Elab Std

structure Reference where
  ident    : RefIdent
  /-- FVarIds that are logically identical to this reference -/
  aliases  : Array RefIdent := #[]
  range    : Lsp.Range
  stx      : Syntax
  ci       : ContextInfo
  info     : Info
  isBinder : Bool

structure RefInfo where
  definition : Option Reference
  usages     : Array Reference

namespace RefInfo

def empty : RefInfo := ⟨ none, #[] ⟩

def addRef : RefInfo → Reference → RefInfo
  | i@{ definition := none, .. }, ref@{ isBinder := true, .. } =>
    { i with definition := ref }
  | i@{ usages, .. }, ref@{ isBinder := false, .. } =>
    { i with usages := usages.push ref }
  | i, _ => i

def toLspRefInfo (i : RefInfo) : IO Lsp.RefInfo := do
  let refToRefInfoLocation (ref : Reference) : IO RefInfo.Location := do
    let parentDeclName? := ref.ci.parentDecl?
    let parentDeclRanges? ← ref.ci.runMetaM ref.info.lctx do
      let some parentDeclName := parentDeclName?
        | return none
      findDeclarationRanges? parentDeclName
    return {
      range := ref.range
      parentDecl? := do
        let parentDeclName ← parentDeclName?
        let parentDeclRange := (← parentDeclRanges?).range.toLspRange
        let parentDeclSelectionRange := (← parentDeclRanges?).selectionRange.toLspRange
        return ⟨parentDeclName, parentDeclRange, parentDeclSelectionRange⟩
    }
  let definition? ← i.definition.mapM refToRefInfoLocation
  let usages ← i.usages.mapM refToRefInfoLocation
  return {
    definition? := definition?
    usages := usages
  }

end RefInfo

def ModuleRefs := HashMap RefIdent RefInfo

namespace ModuleRefs

def addRef (self : ModuleRefs) (ref : Reference) : ModuleRefs :=
  let refInfo := self.findD ref.ident RefInfo.empty
  self.insert ref.ident (refInfo.addRef ref)

def toLspModuleRefs (refs : ModuleRefs) : IO Lsp.ModuleRefs := do
  let refs ← refs.toList.mapM fun (k, v) => do
    return (k, ← v.toLspRefInfo)
  return HashMap.ofList refs

end ModuleRefs

end Lean.Server

namespace Lean.Lsp.RefInfo
open Server

def empty : RefInfo := ⟨ none, #[] ⟩

def merge (a : RefInfo) (b : RefInfo) : RefInfo :=
  {
    definition? := b.definition?.orElse fun _ => a.definition?
    usages := a.usages.append b.usages
  }

def findRange? (self : RefInfo) (pos : Lsp.Position) (includeStop := false) : Option Range := do
  if let some ⟨range, _⟩ := self.definition? then
    if contains range pos then
      return range
  for ⟨range, _⟩ in self.usages do
    if contains range pos then
      return range
  none
where
  contains (range : Lsp.Range) (pos : Lsp.Position) : Bool :=
    -- Note: includeStop is used here to toggle between closed-interval and half-open-interval
    -- behavior for the range. Closed-interval behavior matches the expectation of VSCode
    -- when selecting an identifier at a cursor position, see #767.
    range.start <= pos && (if includeStop then pos <= range.end else pos < range.end)

def contains (self : RefInfo) (pos : Lsp.Position) (includeStop := false) : Bool := Id.run do
  (self.findRange? pos includeStop).isSome

end Lean.Lsp.RefInfo

namespace Lean.Lsp.ModuleRefs
open Server

def findAt (self : ModuleRefs) (pos : Lsp.Position) (includeStop := false) : Array RefIdent := Id.run do
  let mut result := #[]
  for (ident, info) in self.toList do
    if info.contains pos includeStop then
      result := result.push ident
  result

def findRange? (self : ModuleRefs) (pos : Lsp.Position) (includeStop := false) : Option Range := do
  for (_, info) in self.toList do
    if let some range := info.findRange? pos includeStop then
      return range
  none

end Lean.Lsp.ModuleRefs

namespace Lean.Server
open IO
open Lsp
open Elab

/-- Content of individual `.ilean` files -/
structure Ilean where
  version    : Nat := 2
  module     : Name
  references : Lsp.ModuleRefs
  deriving FromJson, ToJson

namespace Ilean

def load (path : System.FilePath) : IO Ilean := do
  let content ← FS.readFile path
  match Json.parse content >>= fromJson? with
    | Except.ok ilean => pure ilean
    | Except.error msg => throwServerError s!"Failed to load ilean at {path}: {msg}"

end Ilean
/-! # Collecting and deduplicating definitions and usages -/

def identOf : Info → Option (RefIdent × Bool)
  | Info.ofTermInfo ti => match ti.expr with
    | Expr.const n .. => some (RefIdent.const n, ti.isBinder)
    | Expr.fvar id .. => some (RefIdent.fvar id, ti.isBinder)
    | _ => none
  | Info.ofFieldInfo fi => some (RefIdent.const fi.projName, false)
  | Info.ofOptionInfo oi => some (RefIdent.const oi.declName, false)
  | _ => none

def findReferences (text : FileMap) (trees : Array InfoTree) : Array Reference := Id.run <| StateT.run' (s := #[]) do
  for tree in trees do
    tree.visitM' (postNode := fun ci info _ => do
      if let some (ident, isBinder) := identOf info then
        if let some range := info.range? then
          if info.stx.getHeadInfo matches .original .. then  -- we are not interested in canonical syntax here
            modify (·.push { ident, range := range.toLspRange text, stx := info.stx, ci, info, isBinder }))
  get

/--
There are several different identifiers that should be considered equal for the purpose of finding
all references of an identifier:
- `FVarId`s of a function parameter in the function's signature and body
- Chains of helper definitions like those created for do-reassignment `x := e`
- Overlapping definitions like those defined by `where` declarations that define both an FVar
  (for local usage) and a constant (for non-local usage)
- Identifiers connected by `FVarAliasInfo` such as variables before and after `match` generalization

In the first three cases that are not explicitly denoted as aliases with an `FVarAliasInfo`, the
corresponding `Reference`s have the exact same range.
This function finds all definitions that have the exact same range as another definition or usage
and collapses them into a single identifier. It also collapses identifiers connected by
an `FVarAliasInfo`.
When collapsing identifiers, it prefers using a `RefIdent.const name` over a `RefIdent.fvar id` for
all identifiers that are being collapsed into one.
-/
partial def combineIdents (trees : Array InfoTree) (refs : Array Reference) : Array Reference := Id.run do
  -- Deduplicate definitions based on their exact range
  let mut posMap : HashMap Lsp.Range RefIdent := HashMap.empty
  for ref in refs do
    if let { ident, range, isBinder := true, .. } := ref then
      posMap := posMap.insert range ident

  let idMap := useConstRepresentatives <| buildIdMap posMap

  let mut refs' := #[]
  for ref in refs do
    let id := ref.ident
    if idMap.contains id then
      refs' := refs'.push { ref with ident := findCanonicalRepresentative idMap id, aliases := #[id] }
    else if !idMap.contains id then
      refs' := refs'.push ref
  refs'
where
  useConstRepresentatives (idMap : HashMap RefIdent RefIdent)
      : HashMap RefIdent RefIdent := Id.run do
    let insertIntoClass classesById id :=
      let representative := findCanonicalRepresentative idMap id
      let «class»     := classesById.findD representative ∅
      let classesById := classesById.erase representative -- make `«class»` referentially unique
      let «class»     := «class».insert id
      classesById.insert representative «class»

    -- collect equivalence classes
    let mut classesById : HashMap RefIdent (HashSet RefIdent) := ∅
    for ⟨id, baseId⟩ in idMap.toArray do
      classesById := insertIntoClass classesById id
      classesById := insertIntoClass classesById baseId

    let mut r := ∅
    for ⟨currentRepresentative, «class»⟩ in classesById.toArray do
      -- find best representative (ideally a const if available)
      let mut bestRepresentative := currentRepresentative
      for id in «class» do
        bestRepresentative :=
          match bestRepresentative, id with
          | .fvar a,  .fvar _  => .fvar a
          | .fvar _,  .const b => .const b
          | .const a, .fvar _  => .const a
          | .const a, .const _ => .const a

      -- compress `idMap` so that all identifiers in a class point to the best representative
      for id in «class» do
        if id != bestRepresentative then
          r := r.insert id bestRepresentative
    return r

  findCanonicalRepresentative (idMap : HashMap RefIdent RefIdent) (id : RefIdent) : RefIdent := Id.run do
    let mut canonicalRepresentative := id
    while idMap.contains canonicalRepresentative do
      canonicalRepresentative := idMap.find! canonicalRepresentative
    return canonicalRepresentative

  buildIdMap posMap := Id.run <| StateT.run' (s := HashMap.empty) do
    -- map fvar defs to overlapping fvar defs/uses
    for ref in refs do
      let baseId := ref.ident
      if let some id := posMap.find? ref.range then
        insertIdMap id baseId

    -- apply `FVarAliasInfo`
    trees.forM (·.visitM' (postNode := fun _ info _ => do
      if let .ofFVarAliasInfo ai := info then
        insertIdMap (.fvar ai.id) (.fvar ai.baseId)))

    get

  -- poor man's union-find; see also `findCanonicalBinder`
  insertIdMap id baseId := do
    let idMap ← get
    let id := findCanonicalRepresentative idMap id
    let baseId := findCanonicalRepresentative idMap baseId
    if baseId != id then
      modify (·.insert id baseId)

def dedupReferences (refs : Array Reference) (allowSimultaneousBinderUse := false) : Array Reference := Id.run do
  let mut refsByIdAndRange : HashMap (RefIdent × Option Bool × Lsp.Range) Reference := HashMap.empty
  for ref in refs do
    let isBinder := if allowSimultaneousBinderUse then some ref.isBinder else none
    let key := (ref.ident, isBinder, ref.range)
    refsByIdAndRange := match refsByIdAndRange[key] with
      | some ref' => refsByIdAndRange.insert key { ref' with aliases := ref'.aliases ++ ref.aliases }
      | none => refsByIdAndRange.insert key ref

  let dedupedRefs := refsByIdAndRange.fold (init := #[]) fun refs _ ref => refs.push ref
  return dedupedRefs.qsort (·.range < ·.range)

def findModuleRefs (text : FileMap) (trees : Array InfoTree) (localVars : Bool := true)
    (allowSimultaneousBinderUse := false) : ModuleRefs := Id.run do
  let mut refs :=
    dedupReferences (allowSimultaneousBinderUse := allowSimultaneousBinderUse) <|
    combineIdents trees <|
    findReferences text trees
  if !localVars then
    refs := refs.filter fun
      | { ident := RefIdent.fvar _, .. } => false
      | _ => true
  refs.foldl (init := HashMap.empty) fun m ref => m.addRef ref

/-! # Collecting and maintaining reference info from different sources -/

structure References where
  /-- References loaded from ilean files -/
  ileans : HashMap Name (System.FilePath × Lsp.ModuleRefs)
  /-- References from workers, overriding the corresponding ilean files -/
  workers : HashMap Name (Nat × Lsp.ModuleRefs)

namespace References

def empty : References := { ileans := HashMap.empty, workers := HashMap.empty }

def addIlean (self : References) (path : System.FilePath) (ilean : Ilean) : References :=
  { self with ileans := self.ileans.insert ilean.module (path, ilean.references) }

def removeIlean (self : References) (path : System.FilePath) : References :=
  let namesToRemove := self.ileans.toList.filter (fun (_, p, _) => p == path)
    |>.map (fun (n, _, _) => n)
  namesToRemove.foldl (init := self) fun self name =>
    { self with ileans := self.ileans.erase name }

def updateWorkerRefs (self : References) (name : Name) (version : Nat) (refs : Lsp.ModuleRefs) : References := Id.run do
  if let some (currVersion, _) := self.workers.find? name then
    if version > currVersion then
      return { self with workers := self.workers.insert name (version, refs) }
    if version == currVersion then
      let current := self.workers.findD name (version, HashMap.empty)
      let merged := refs.fold (init := current.snd) fun m ident info =>
        m.findD ident Lsp.RefInfo.empty |>.merge info |> m.insert ident
      return { self with workers := self.workers.insert name (version, merged) }
  return self

def finalizeWorkerRefs (self : References) (name : Name) (version : Nat) (refs : Lsp.ModuleRefs) : References := Id.run do
  if let some (currVersion, _) := self.workers.find? name then
    if version < currVersion then
      return self
  return { self with workers := self.workers.insert name (version, refs) }

def removeWorkerRefs (self : References) (name : Name) : References :=
  { self with workers := self.workers.erase name }

def allRefs (self : References) : HashMap Name Lsp.ModuleRefs :=
  let ileanRefs := self.ileans.toList.foldl (init := HashMap.empty) fun m (name, _, refs) => m.insert name refs
  self.workers.toList.foldl (init := ileanRefs) fun m (name, _, refs) => m.insert name refs

def findAt (self : References) (module : Name) (pos : Lsp.Position) (includeStop := false) : Array RefIdent := Id.run do
  if let some refs := self.allRefs.find? module then
    return refs.findAt pos includeStop
  #[]

def findRange? (self : References) (module : Name) (pos : Lsp.Position) (includeStop := false) : Option Range := do
  let refs ← self.allRefs.find? module
  refs.findRange? pos includeStop

structure DocumentRefInfo where
  location    : Location
  parentInfo? : Option RefInfo.ParentDecl

def referringTo (self : References) (identModule : Name) (ident : RefIdent) (srcSearchPath : SearchPath)
    (includeDefinition : Bool := true) : IO (Array DocumentRefInfo) := do
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
        let uri := System.Uri.pathToUri <| ← IO.FS.realPath path
        if includeDefinition then
          if let some ⟨range, parentDeclInfo?⟩ := info.definition? then
            result := result.push ⟨⟨uri, range⟩, parentDeclInfo?⟩
        for ⟨range, parentDeclInfo?⟩ in info.usages do
          result := result.push ⟨⟨uri, range⟩, parentDeclInfo?⟩
  return result

def definitionOf? (self : References) (ident : RefIdent) (srcSearchPath : SearchPath)
    : IO (Option DocumentRefInfo) := do
  for (module, refs) in self.allRefs.toList do
    if let some info := refs.find? ident then
      if let some ⟨definitionRange, definitionParentDeclInfo?⟩ := info.definition? then
        if let some path ← srcSearchPath.findModuleWithExt "lean" module then
          -- Resolve symlinks (such as `src` in the build dir) so that files are
          -- opened in the right folder
          let uri := System.Uri.pathToUri <| ← IO.FS.realPath path
          return some ⟨⟨uri, definitionRange⟩, definitionParentDeclInfo?⟩
  return none

def definitionsMatching (self : References) (srcSearchPath : SearchPath) (filter : Name → Option α)
    (maxAmount? : Option Nat := none) : IO $ Array (α × Location) := do
  let mut result := #[]
  for (module, refs) in self.allRefs.toList do
    if let some path ← srcSearchPath.findModuleWithExt "lean" module then
      let uri := System.Uri.pathToUri <| ← IO.FS.realPath path
      for (ident, info) in refs.toList do
        if let (RefIdent.const name, some ⟨definitionRange, _⟩) := (ident, info.definition?) then
          if let some a := filter name then
            result := result.push (a, ⟨uri, definitionRange⟩)
            if let some maxAmount := maxAmount? then
              if result.size >= maxAmount then
                return result
  return result

end References

end Lean.Server
