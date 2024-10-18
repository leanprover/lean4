/-
Copyright (c) 2022 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/
prelude
import Lean.Expr
import Lean.Data.Lsp.Basic

set_option linter.missingDocs true -- keep it documented

/-! This file contains types for communication between the watchdog and the
workers. These messages are not visible externally to users of the LSP server.
-/

namespace Lean.Lsp

/-! Most reference-related types have custom FromJson/ToJson implementations to
reduce the size of the resulting JSON. -/

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
  deriving BEq, Hashable, Inhabited

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

/-- Information about the declaration surrounding a reference. -/
structure RefInfo.ParentDecl where
  /-- Name of the declaration surrounding a reference. -/
  name           : String
  /-- Range of the declaration surrounding a reference. -/
  range          : Lsp.Range
  /-- Selection range of the declaration surrounding a reference. -/
  selectionRange : Lsp.Range
  deriving ToJson

/--
Denotes the range of a reference, as well as the parent declaration of the reference.
If the reference is itself a declaration, then it contains no parent declaration.
-/
structure RefInfo.Location where
  /-- Range of the reference. -/
  range       : Lsp.Range
  /-- Parent declaration of the reference. `none` if the reference is itself a declaration. -/
  parentDecl? : Option RefInfo.ParentDecl
deriving Inhabited

/-- Definition site and usage sites of a reference. Obtained from `Lean.Server.RefInfo`. -/
structure RefInfo where
  /-- Definition site of the reference. May be `none` when we cannot find a definition site. -/
  definition? : Option RefInfo.Location
  /-- Usage sites of the reference. -/
  usages      : Array RefInfo.Location

instance : ToJson RefInfo where
  toJson i :=
    let rangeToList (r : Lsp.Range) : List Nat :=
      [r.start.line, r.start.character, r.end.line, r.end.character]
    let parentDeclToList (d : RefInfo.ParentDecl) : List Json :=
      let name := d.name |> toJson
      let range := rangeToList d.range |>.map toJson
      let selectionRange := rangeToList d.selectionRange |>.map toJson
      [name] ++ range ++ selectionRange
    let locationToList (l : RefInfo.Location) : List Json :=
      let range := rangeToList l.range |>.map toJson
      let parentDecl := l.parentDecl?.map parentDeclToList |>.getD []
      range ++ parentDecl
    Json.mkObj [
      ("definition", toJson $ i.definition?.map locationToList),
      ("usages", toJson $ i.usages.map locationToList)
    ]

instance : FromJson RefInfo where
  -- This implementation is optimized to prevent redundant intermediate allocations.
  fromJson? j := do
    let toRange (a : Array Json) (i : Nat) : Except String Lsp.Range :=
      if h : a.size < i + 4 then
        throw s!"Expected list of length 4, not {a.size}"
      else
        return {
          start := {
            line := ← fromJson? a[i]
            character := ← fromJson? a[i+1]
          }
          «end» := {
            line := ← fromJson? a[i+2]
            character := ← fromJson? a[i+3]
          }
        }
    let toParentDecl (a : Array Json) (i : Nat) : Except String RefInfo.ParentDecl := do
      let name ← fromJson? a[i]!
      let range ← toRange a (i + 1)
      let selectionRange ← toRange a (i + 5)
      return ⟨name, range, selectionRange⟩
    let toLocation (a : Array Json) : Except String RefInfo.Location := do
      if a.size != 4 && a.size != 13 then
        .error "Expected list of length 4 or 13, not {l.size}"
      let range ← toRange a 0
      if a.size == 13 then
        let parentDecl ← toParentDecl a 4
        return ⟨range, parentDecl⟩
      else
        return ⟨range, none⟩

    let definition? ← j.getObjValAs? (Option $ Array Json) "definition"
    let definition? ← match definition? with
      | none => pure none
      | some array => some <$> toLocation array
    let usages ← j.getObjValAs? (Array $ Array Json) "usages"
    let usages ← usages.mapM toLocation
    pure { definition?, usages }

/-- References from a single module/file -/
def ModuleRefs := Std.HashMap RefIdent RefInfo

instance : ToJson ModuleRefs where
  toJson m := Json.mkObj <| m.toList.map fun (ident, info) => (ident.toJson.compress, toJson info)

instance : FromJson ModuleRefs where
  fromJson? j := do
    let node ← j.getObj?
    node.foldM (init := Std.HashMap.empty) fun m k v =>
      return m.insert (← RefIdent.fromJson? (← Json.parse k)) (← fromJson? v)

/--
Used in the `$/lean/ileanInfoUpdate` and `$/lean/ileanInfoFinal` watchdog <- worker notifications.
Contains the definitions and references of the file managed by a worker.
-/
structure LeanIleanInfoParams where
  /-- Version of the file these references are from. -/
  version    : Nat
  /-- All references for the file. -/
  references : ModuleRefs
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

end Lean.Lsp
