import Lean.Data.Json
import Lean.Data.Lsp

namespace Lean.Server.References
open Std
open Lsp

inductive RefIdent where
  | const : Name → RefIdent
  | fvar : FVarId → RefIdent
  deriving BEq, Hashable

namespace RefIdent

def toString : RefIdent → String
  | RefIdent.const n => s!"c:{n}"
  | RefIdent.fvar id => s!"f:{id.name}"

def fromString (s : String) : Except String RefIdent := do
  let sPrefix := s.take 2
  let sName := s.drop 2
  let mk ← match sPrefix with
    | "c:" => RefIdent.const
    | "f:" => fun n => RefIdent.fvar <| FVarId.mk n
    | _ => throw "string must start with 'c:' or 'f:'"
  -- See `FromJson Name`
  let name ← match sName with
    | "[anonymous]" => Name.anonymous
    | _ => match Syntax.decodeNameLit ("`" ++ sName) with
      | some n => n
      | none => throw s!"expected a Name, got {sName}"
  mk name

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

def FileRefMap := HashMap RefIdent RefInfo

instance : ToJson FileRefMap where
  toJson m := Json.mkObj <| m.toList.map fun (ident, info) => (ident.toString, toJson info)

instance : FromJson FileRefMap where
  fromJson? j := do
    let node ← j.getObj?
    node.foldM (init := HashMap.empty) fun m k v => do
      m.insert (← RefIdent.fromString k) (← fromJson? v)

def RefMap := HashMap String FileRefMap

end Lean.Server.References
