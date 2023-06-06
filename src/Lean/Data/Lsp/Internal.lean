/-
Copyright (c) 2022 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/

import Lean.Expr
import Lean.Data.Lsp.Basic

/-! This file contains types for communication between the watchdog and the
workers. These messages are not visible externally to users of the LSP server.
-/

namespace Lean.Lsp

/-! Most reference-related types have custom FromJson/ToJson implementations to
reduce the size of the resulting JSON. -/

inductive RefIdent where
  | const : Name → RefIdent
  | fvar : FVarId → RefIdent
  deriving BEq, Hashable, Inhabited

namespace RefIdent

def toString : RefIdent → String
  | RefIdent.const n => s!"c:{n}"
  | RefIdent.fvar id => s!"f:{id.name}"

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

end RefIdent

structure RefInfo where
  definition : Option Lsp.Range
  usages : Array Lsp.Range

instance : ToJson RefInfo where
  toJson i :=
    let rangeToList (r : Lsp.Range) : List Nat :=
      [r.start.line, r.start.character, r.end.line, r.end.character]
    Json.mkObj [
      ("definition", toJson $ i.definition.map rangeToList),
      ("usages", toJson $ i.usages.map rangeToList)
    ]

instance : FromJson RefInfo where
  fromJson? j := do
    let listToRange (l : List Nat) : Except String Lsp.Range := match l with
      | [sLine, sChar, eLine, eChar] => pure ⟨⟨sLine, sChar⟩, ⟨eLine, eChar⟩⟩
      | _ => throw s!"Expected list of length 4, not {l.length}"
    let definition ← j.getObjValAs? (Option $ List Nat) "definition"
    let definition ← match definition with
      | none => pure none
      | some list => some <$> listToRange list
    let usages ← j.getObjValAs? (Array $ List Nat) "usages"
    let usages ← usages.mapM listToRange
    pure { definition, usages }

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
  version : Nat
  references : ModuleRefs
  deriving FromJson, ToJson

end Lean.Lsp
