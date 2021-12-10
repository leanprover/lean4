import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.InfoUtils
import Lean.Server.Snapshots

namespace Lean.Server.References
open Std
open Lsp
open Elab
open Snapshots

/- Representing collected and deduplicated definitions and usages -/

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

structure Reference where
  ident : RefIdent
  range : Lsp.Range
  isDeclaration : Bool
  deriving BEq

structure RefInfo where
  definition : Option Lsp.Range
  usages : Array Lsp.Range

namespace RefInfo

def empty : RefInfo := ⟨ none, #[] ⟩

def addRef : RefInfo → Reference → RefInfo
  | i@{ definition := none, .. }, { range, isDeclaration := true, .. } =>
    { i with definition := range }
  | i@{ usages, .. }, { range, isDeclaration := false, .. } =>
    { i with usages := usages.push range }
  | i, _ => i

end RefInfo

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

namespace FileRefMap

def addRef (self : FileRefMap) (ref : Reference) : FileRefMap :=
  let refInfo := self.findD ref.ident RefInfo.empty
  self.insert ref.ident (refInfo.addRef ref)

end FileRefMap

def RefMap := HashMap String FileRefMap

/- Collecting and deduplicating definitions and usages -/

def identOf : Info → Option (RefIdent × Bool)
  | Info.ofTermInfo ti => match ti.expr with
    | Expr.const n .. => some (RefIdent.const n, ti.isBinder)
    | Expr.fvar id .. => some (RefIdent.fvar id, ti.isBinder)
    | _ => none
  | Info.ofFieldInfo fi => some (RefIdent.const fi.projName, false)
  | _ => none

def findReferences (text : FileMap) (trees : List InfoTree) : Array Reference := Id.run do
  let mut refs := #[]
  for tree in trees do
    refs := refs.appendList <| tree.deepestNodes fun _ info _ => Id.run do
      if let some (ident, isDeclaration) := identOf info then
        if let some range := info.range? then
          return some { ident, range := range.toLspRange text, isDeclaration }
      return none
  refs

/--
The `FVarId`s of a function parameter in the function's signature and body
differ. However, they have `TermInfo` nodes with `binder := true` in the exact
same position.

This function changes every such group to use a single `FVarId` and gets rid of
duplicate definitions.
-/
def combineFvars (refs : Array Reference) : Array Reference := Id.run do
  -- Deduplicate definitions based on their exact range
  let mut posMap : HashMap Lsp.Range FVarId := HashMap.empty
  -- Map all `FVarId`s of a group to the first definition's id
  let mut idMap : HashMap FVarId FVarId := HashMap.empty
  for ref in refs do
    if let { ident := RefIdent.fvar id, range, isDeclaration := true } := ref then
      if let some baseId := posMap.find? range then
        idMap := idMap.insert id baseId
      else
        posMap := posMap.insert range id
        idMap := idMap.insert id id

  refs.foldl (init := #[]) fun refs ref => match ref with
    | { ident := RefIdent.fvar id, range, isDeclaration := true } =>
      -- Since deduplication works via definitions, we know that this keeps (at
      -- least) one definition.
      if idMap.contains id then refs.push ref else refs
    | { ident := ident@(RefIdent.fvar _), range, isDeclaration := false } =>
      refs.push { ident := applyIdMap idMap ident, range, isDeclaration := false }
    | _ => refs.push ref
  where
    applyIdMap : HashMap FVarId FVarId → RefIdent → RefIdent
      | m, RefIdent.fvar id => RefIdent.fvar <| m.findD id id
      | _, ident => ident

def findFileRefs (text : FileMap) (trees : List InfoTree) : FileRefMap :=
  let refs := combineFvars <| findReferences text trees
  refs.foldl (init := HashMap.empty) fun m ref => m.addRef ref

end Lean.Server.References
