/-
Copyright (c) 2022 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/
module

prelude
public import Lean.Expr
public import Lean.Data.Lsp.Basic
public import Lean.Data.JsonRpc
public import Lean.Data.DeclarationRange

public section

set_option linter.missingDocs true -- keep it documented

/-! This file contains types for communication between the watchdog and the
workers. These messages are not visible externally to users of the LSP server.
-/

namespace Lean.Lsp

/-! Most reference-related types have custom FromJson/ToJson implementations to
reduce the size of the resulting JSON. -/

/-- Information about a single import statement. -/
structure ImportInfo where
  /-- Name of the module that is imported. -/
  module    : String
  /-- Whether the module is being imported via `private import`. -/
  isPrivate : Bool
  /-- Whether the module is being imported via `import all`. -/
  isAll     : Bool
  /-- Whether the module is being imported via `meta import`. -/
  isMeta    : Bool
  deriving Inhabited

instance : ToJson ImportInfo where
  toJson info := Json.arr #[info.module, info.isPrivate, info.isAll, info.isMeta]

instance : FromJson ImportInfo where
  fromJson?
    | .arr #[moduleJson, isPrivateJson, isAllJson, isMetaJson] => do
      return {
        module    := ← fromJson? moduleJson
        isPrivate := ← fromJson? isPrivateJson
        isAll     := ← fromJson? isAllJson
        isMeta    := ← fromJson? isMetaJson
      }
    | _ => .error "Expected array, got other JSON type"

/--
Identifier of a reference.
-/
-- Names are represented by strings to avoid having to parse them to `Name`,
-- which is relatively expensive. Most uses of these names only need equality, anyways.
inductive RefIdent where
  /-- Named identifier. These are used in all references that are globally available. -/
  | const (moduleName : String) (identName : String) : RefIdent
  /-- Unnamed identifier. These are used for all local references. -/
  | fvar (moduleName : String) (id : String) : RefIdent
  deriving BEq, Hashable, Inhabited, Ord

namespace RefIdent

/-- Shortened representation of `RefIdent` for more compact serialization. -/
inductive RefIdentJsonRepr
  /-- Shortened representation of `RefIdent.const` for more compact serialization. -/
  | c (m n : String)
  /-- Shortened representation of `RefIdent.fvar` for more compact serialization. -/
  | f (m : String) (i : String)
  deriving FromJson, ToJson

/-- Converts `id` to its compact serialization representation. -/
def toJsonRepr : (id : RefIdent) → RefIdentJsonRepr
  | const moduleName identName => .c moduleName identName
  | fvar moduleName id => .f moduleName id

/-- Converts `repr` to `RefIdent`. -/
def fromJsonRepr : (repr : RefIdentJsonRepr) → RefIdent
  | .c m n => const m n
  | .f m i => fvar m i

/-- Converts `RefIdent` from a JSON for `RefIdentJsonRepr`. -/
def fromJson? (s : Json) : Except String RefIdent :=
  return fromJsonRepr (← Lean.FromJson.fromJson? s)

/-- Converts `RefIdent` to a JSON for `RefIdentJsonRepr`. -/
def toJson (id : RefIdent) : Json :=
  Lean.ToJson.toJson <| toJsonRepr id

instance : FromJson RefIdent where
  fromJson? := fromJson?

instance : ToJson RefIdent where
  toJson := toJson

end RefIdent

/-- Position information for a declaration. Inlined to reduce memory consumption. -/
structure DeclInfo where
  /-- Start line of range. -/
  rangeStartPosLine : Nat
  /-- Start character of range. -/
  rangeStartPosCharacter : Nat
  /-- End line of range. -/
  rangeEndPosLine : Nat
  /-- End character of range. -/
  rangeEndPosCharacter : Nat
  /-- Start line of selection range. -/
  selectionRangeStartPosLine : Nat
  /-- Start character of selection range. -/
  selectionRangeStartPosCharacter : Nat
  /-- End line of selection range. -/
  selectionRangeEndPosLine : Nat
  /-- End character of selection range. -/
  selectionRangeEndPosCharacter : Nat

/-- Converts a set of `DeclarationRanges` to a `DeclInfo`. -/
def DeclInfo.ofDeclarationRanges (r : DeclarationRanges) : DeclInfo where
  rangeStartPosLine := r.range.pos.line - 1
  rangeStartPosCharacter := r.range.charUtf16
  rangeEndPosLine := r.range.endPos.line - 1
  rangeEndPosCharacter := r.range.endCharUtf16
  selectionRangeStartPosLine := r.selectionRange.pos.line - 1
  selectionRangeStartPosCharacter := r.selectionRange.charUtf16
  selectionRangeEndPosLine := r.selectionRange.endPos.line - 1
  selectionRangeEndPosCharacter := r.selectionRange.endCharUtf16

/-- Range of this parent decl. -/
def DeclInfo.range (i : DeclInfo) : Lsp.Range :=
  ⟨⟨i.rangeStartPosLine, i.rangeStartPosCharacter⟩, ⟨i.rangeEndPosLine, i.rangeEndPosCharacter⟩⟩

/-- Selection range of this parent decl. -/
def DeclInfo.selectionRange (i : DeclInfo) : Lsp.Range :=
  ⟨⟨i.selectionRangeStartPosLine, i.selectionRangeStartPosCharacter⟩,
    ⟨i.selectionRangeEndPosLine, i.selectionRangeEndPosCharacter⟩⟩

instance : ToJson DeclInfo where
  toJson i :=
    Json.arr #[
      i.rangeStartPosLine,
      i.rangeStartPosCharacter,
      i.rangeEndPosLine,
      i.rangeEndPosCharacter,
      i.selectionRangeStartPosLine,
      i.selectionRangeStartPosCharacter,
      i.selectionRangeEndPosLine,
      i.selectionRangeEndPosCharacter
    ]

instance : FromJson DeclInfo where
  fromJson?
    | .arr xs => do
      if xs.size != 8 then
        throw s!"Expected list of length 8, not length {xs.size}"
      return {
        rangeStartPosLine := ← fromJson? xs[0]!
        rangeStartPosCharacter := ← fromJson? xs[1]!
        rangeEndPosLine := ← fromJson? xs[2]!
        rangeEndPosCharacter := ← fromJson? xs[3]!
        selectionRangeStartPosLine := ← fromJson? xs[4]!
        selectionRangeStartPosCharacter := ← fromJson? xs[5]!
        selectionRangeEndPosLine := ← fromJson? xs[6]!
        selectionRangeEndPosCharacter := ← fromJson? xs[7]!
      }
    | _ => throw "Expected list"

/-- Declarations of a file with associated position information. -/
@[expose] def Decls := Std.TreeMap String DeclInfo
  deriving EmptyCollection, ForIn Id

instance : ToJson Decls where
  toJson m := Json.mkObj <| m.toList.map fun (declName, info) => (declName, toJson info)

instance : FromJson Decls where
  fromJson? j := do
    let node ← j.getObj?
    node.foldlM (init := ∅) fun m k v =>
      return m.insert k (← fromJson? v)

/--
Denotes the range of a reference, as well as the parent declaration of the reference.
If the reference is itself a declaration, then it contains no parent declaration.
The position information is inlined to reduce memory consumption.
-/
structure RefInfo.Location where
  mk' ::
  /-- Start line of the range of this location. -/
  startPosLine : Nat
  /-- Start character of the range of this location. -/
  startPosCharacter : Nat
  /-- End line of the range of this location. -/
  endPosLine : Nat
  /-- End character of the range of this location. -/
  endPosCharacter : Nat
  /--
  Parent declaration of the reference. Empty string if the reference is itself a declaration.
  We do not use `Option` for memory consumption reasons.
  -/
  parentDecl : String
deriving Inhabited

/-- Creates a `RefInfo.Location`. -/
def RefInfo.Location.mk (range : Lsp.Range) (parentDecl? : Option String) : RefInfo.Location where
  startPosLine := range.start.line
  startPosCharacter := range.start.character
  endPosLine := range.end.line
  endPosCharacter := range.end.character
  parentDecl := parentDecl?.getD ""

/-- Range of this location. -/
def RefInfo.Location.range (l : RefInfo.Location) : Lsp.Range :=
  ⟨⟨l.startPosLine, l.startPosCharacter⟩, ⟨l.endPosLine, l.endPosCharacter⟩⟩

/-- Name of the parent declaration of this location. -/
def RefInfo.Location.parentDecl? (l : RefInfo.Location) : Option String :=
  if l.parentDecl.isEmpty then
    none
  else
    some l.parentDecl

/-- Definition site and usage sites of a reference. Obtained from `Lean.Server.RefInfo`. -/
structure RefInfo where
  /-- Definition site of the reference. May be `none` when we cannot find a definition site. -/
  definition? : Option RefInfo.Location
  /-- Usage sites of the reference. -/
  usages      : Array RefInfo.Location

instance : ToJson RefInfo where
  toJson i :=
    let locationToList (l : RefInfo.Location) : List Json :=
      let range := [l.startPosLine, l.startPosCharacter, l.endPosLine, l.endPosCharacter].map toJson
      let parentDecl := l.parentDecl?.map ([toJson ·]) |>.getD []
      range ++ parentDecl
    Json.mkObj [
      ("definition", toJson $ i.definition?.map locationToList),
      ("usages", toJson $ i.usages.map locationToList)
    ]

instance : FromJson RefInfo where
  -- This implementation is optimized to prevent redundant intermediate allocations.
  fromJson? j := do
    let toLocation (a : Array Json) : Except String RefInfo.Location := do
      if h : a.size ≠ 4 ∧ a.size ≠ 5 then
        .error s!"Expected list of length 4 or 5, not {a.size}"
      else
        let startPosLine ← fromJson? a[0]
        let startPosCharacter ← fromJson? a[1]
        let endPosLine ← fromJson? a[2]
        let endPosCharacter ← fromJson? a[3]
        if h' : a.size = 5 then
          return {
            startPosLine
            startPosCharacter
            endPosLine
            endPosCharacter
            parentDecl := ← fromJson? a[4]
          }
        else
          return {
            startPosLine
            startPosCharacter
            endPosLine
            endPosCharacter
            parentDecl := ""
          }
    let definition? ← j.getObjValAs? (Option $ Array Json) "definition"
    let definition? ← match definition? with
      | none => pure none
      | some array => some <$> toLocation array
    let usages ← j.getObjValAs? (Array $ Array Json) "usages"
    let usages ← usages.mapM toLocation
    pure { definition?, usages }

/-- References from a single module/file -/
@[expose] def ModuleRefs := Std.TreeMap RefIdent RefInfo
  deriving EmptyCollection

instance [Monad m] : ForIn m ModuleRefs (RefIdent × RefInfo) where
  forIn map init f :=
    let map : Std.TreeMap RefIdent RefInfo := map
    forIn map init f

instance : ToJson ModuleRefs where
  toJson m := Json.mkObj <| m.toList.map fun (ident, info) => (ident.toJson.compress, toJson info)

instance : FromJson ModuleRefs where
  fromJson? j := do
    let node ← j.getObj?
    node.foldlM (init := ∅) fun m k v =>
      return m.insert (← RefIdent.fromJson? (← Json.parse k)) (← fromJson? v)

/--
Used in the `$/lean/ileanHeaderSetupInfo` watchdog <- worker notifications.
Contains status information about `lake setup-file` and the direct imports of the file managed by
a worker.
-/
structure LeanILeanHeaderSetupInfoParams where
  /-- Version of the file these imports are from. -/
  version        : Nat
  /-- Whether setting up the header using `lake setup-file` has failed. -/
  isSetupFailure : Bool
  /-- Direct imports of this file. -/
  directImports : Array ImportInfo
  deriving FromJson, ToJson

/--
Used in the `$/lean/ileanInfoUpdate` and `$/lean/ileanInfoFinal` watchdog <- worker notifications.
Contains the definitions and references of the file managed by a worker.
-/
structure LeanIleanInfoParams where
  /-- Version of the file these references are from. -/
  version    : Nat
  /-- All references for the file. -/
  references : ModuleRefs
  /-- All decls for the file. -/
  decls      : Decls
  deriving FromJson, ToJson

/--
Used in the `$/lean/importClosure` watchdog <- worker notification.
Contains the full import closure of the file managed by a worker.
-/
structure LeanImportClosureParams where
  /-- Full import closure of the file. -/
  importClosure : Array DocumentUri
  deriving FromJson, ToJson

/--
Used in the `$/lean/importClosure` watchdog -> worker notification.
Informs the worker that one of its dependencies has gone stale and likely needs to be rebuilt.
-/
structure LeanStaleDependencyParams where
  /-- The dependency that is stale. -/
  staleDependency : DocumentUri
  deriving FromJson, ToJson

/-- LSP type for `Lean.OpenDecl`. -/
inductive OpenNamespace
  /-- All declarations in `«namespace»` are opened, except for `exceptions`. -/
  | allExcept («namespace» : Name) (exceptions : Array Name)
  /-- The declaration `«from»` is renamed to `to`. -/
  | renamed («from» : Name) (to : Name)
  deriving FromJson, ToJson

/-- Query in the `$/lean/queryModule` watchdog <- worker request. -/
structure LeanModuleQuery where
  /-- Identifier (potentially partial) to query. -/
  identifier : String
  /--
  Namespaces that are open at the position of `identifier`.
  Used for accurately matching declarations against `identifier` in context.
  -/
  openNamespaces : Array OpenNamespace
  deriving FromJson, ToJson

/--
Used in the `$/lean/queryModule` watchdog <- worker request, which is used by the worker to
extract information from the .ilean information in the watchdog.
-/
structure LeanQueryModuleParams where
  /--
  The request ID in the context of which this worker -> watchdog request was emitted.
  Used for cancelling this request in the watchdog.
  -/
  sourceRequestID : JsonRpc.RequestID
  /-- Module queries for extracting .ilean information in the watchdog. -/
  queries : Array LeanModuleQuery
  deriving FromJson, ToJson

/-- Result entry of a module query. -/
structure LeanIdentifier where
  /-- Module that `decl` is defined in. -/
  module : Name
  /-- Full name of the declaration that matches the query. -/
  decl : Name
  /-- Whether this `decl` matched the query exactly. -/
  isExactMatch : Bool
  deriving FromJson, ToJson

/--
Result for a single module query.
Identifiers in the response are sorted descendingly by how well they match the query.
-/
abbrev LeanQueriedModule := Array LeanIdentifier

/-- Response for the `$/lean/queryModule` watchdog <- worker request. -/
structure LeanQueryModuleResponse where
  /--
  Results for each query in `LeanQueryModuleParams`.
  Positions correspond to `queries` in the parameter of the request.
  -/
  queryResults : Array LeanQueriedModule
  deriving FromJson, ToJson, Inhabited

/-- Name of a declaration in a given module. -/
structure LeanDeclIdent where
  /-- Uri of the module that this identifier is in. -/
  uri  : DocumentUri
  /-- Name of the declaration. -/
  decl : Name
  deriving FromJson, ToJson

/--
`LocationLink` with additional meta-data that allows the watchdog to resolve the range of this
`LocationLink`. This is necessary because the position information from the .olean may be stale
(e.g. if the user has edited the file that the definition is from, but neither saved or built it),
while file workers sync their current reference information into the watchdog using ilean info
notifications, which is up-to-date.
-/
structure LeanLocationLink extends LocationLink where
  /-- Identifier that caused this location link. -/
  ident? : Option LeanDeclIdent
  /--
  Whether this location link was generated by a fallback handler.
  If the file worker can't produce any non-fallback location links, the watchdog tries again
  using its reference information from the ileans and ilean updates.
  -/
  isDefault : Bool
  deriving FromJson, ToJson

end Lean.Lsp
