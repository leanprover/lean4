/-
Copyright (c) 2022 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/

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
inductive RefIdent where
  /-- Named identifier. These are used in all references that are globally available. -/
  | const : Name → RefIdent
  /-- Unnamed identifier. These are used for all local references. -/
  | fvar  : FVarId → RefIdent
  deriving BEq, Hashable, Inhabited

namespace RefIdent

/-- Converts the reference identifier to a string by prefixing it with a symbol. -/
def toString : RefIdent → String
  | RefIdent.const n => s!"c:{n}"
  | RefIdent.fvar id => s!"f:{id.name}"

/--
Converts the string representation of a reference identifier back to a reference identifier.
The string representation must have been created by `RefIdent.toString`.
-/
def fromString (s : String) : Except String RefIdent := do
  let sPrefix := s.take 2
  let sName := s.drop 2
  -- See `FromJson Name`
  let name ← match sName with
    | "[anonymous]" => pure Name.anonymous
    | _ =>
      let n := sName.toName
      if n.isAnonymous then throw s!"expected a Name, got {sName}"
      else pure n
  match sPrefix with
    | "c:" => return RefIdent.const name
    | "f:" => return RefIdent.fvar <| FVarId.mk name
    | _ => throw "string must start with 'c:' or 'f:'"

instance : FromJson RefIdent where
  fromJson?
    | (s : String) => fromString s
    | j => Except.error s!"expected a String, got {j}"

instance : ToJson RefIdent where
  toJson ident := toString ident

end RefIdent

/-- Information about the declaration surrounding a reference. -/
structure RefInfo.ParentDecl where
  /-- Name of the declaration surrounding a reference. -/
  name           : Name
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
      let name := d.name.toString |> toJson
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
  fromJson? j := do
    let toRange : List Nat → Except String Lsp.Range
      | [sLine, sChar, eLine, eChar] => pure ⟨⟨sLine, sChar⟩, ⟨eLine, eChar⟩⟩
      | l => throw s!"Expected list of length 4, not {l.length}"
    let toParentDecl (a : Array Json) : Except String RefInfo.ParentDecl := do
      let name := String.toName <| ← fromJson? a[0]!
      let range ← a[1:5].toArray.toList |>.mapM fromJson?
      let range ← toRange range
      let selectionRange ← a[5:].toArray.toList |>.mapM fromJson?
      let selectionRange ← toRange selectionRange
      return ⟨name, range, selectionRange⟩
    let toLocation (l : List Json) : Except String RefInfo.Location := do
      let l := l.toArray
      if l.size != 4 && l.size != 13 then
        .error "Expected list of length 4 or 13, not {l.size}"
      let range ← l[:4].toArray.toList |>.mapM fromJson?
      let range ← toRange range
      if l.size == 13 then
        let parentDecl ← toParentDecl l[4:].toArray
        return ⟨range, parentDecl⟩
      else
        return ⟨range, none⟩

    let definition? ← j.getObjValAs? (Option $ List Json) "definition"
    let definition? ← match definition? with
      | none => pure none
      | some list => some <$> toLocation list
    let usages ← j.getObjValAs? (Array $ List Json) "usages"
    let usages ← usages.mapM toLocation
    pure { definition?, usages }

/-- References from a single module/file -/
def ModuleRefs := HashMap RefIdent RefInfo

instance : ToJson ModuleRefs where
  toJson m := Json.mkObj <| m.toList.map fun (ident, info) => (ident.toString, toJson info)

instance : FromJson ModuleRefs where
  fromJson? j := do
    let node ← j.getObj?
    node.foldM (init := HashMap.empty) fun m k v =>
      return m.insert (← RefIdent.fromString k) (← fromJson? v)

/-- `$/lean/ileanInfoUpdate` and `$/lean/ileanInfoFinal` watchdog<-worker notifications.

Contains the file's definitions and references. -/
structure LeanIleanInfoParams where
  /-- Version of the file these references are from. -/
  version    : Nat
  /-- All references for the file. -/
  references : ModuleRefs
  deriving FromJson, ToJson

end Lean.Lsp
