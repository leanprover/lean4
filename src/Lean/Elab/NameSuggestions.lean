/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.CoreM
import Lean.Data.Lsp.Utf16
import Lean.Elab.InfoTree
import Lean.Message


namespace Lean.Elab

structure NameSuggestions where
  localSuggestions : List (String × Nat × FVarId) := []
  constSuggestions : List (String × Nat × Name × List Name) := []

structure NameSuggestionInfo where
  range : Lsp.Range
  replacements : Array String
deriving TypeName

def NameSuggestions.isEmpty (suggestions : NameSuggestions) : Bool :=
  suggestions.localSuggestions == [] && suggestions.constSuggestions == []

def Suggestions.isSingleton (suggestions : NameSuggestions) : Bool :=
  match suggestions.localSuggestions, suggestions.constSuggestions with
  | [], [_] => true
  | [_], [] => true
  | _, _ => false

def NameSuggestions.addConstant
    (toShow : String) (score : Nat) (name : Name) (universeParams : List Name)
    (suggestions : NameSuggestions) : NameSuggestions :=
  {suggestions with
    constSuggestions := (toShow, score, name, universeParams) :: suggestions.constSuggestions}

def NameSuggestions.addFVar
    (toShow : String) (score : Nat) (fvarId : FVarId)
    (suggestions : NameSuggestions) : NameSuggestions :=
  {suggestions with localSuggestions := (toShow, score, fvarId) :: suggestions.localSuggestions}

def NameSuggestions.toMessageData (suggestions : NameSuggestions) : MessageData :=
  if suggestions.isEmpty then .nil
  else m!"\n\n" ++
    let locals := suggestions.localSuggestions.map fun (str, score, fv) =>
      (str, score, m!"'{Expr.fvar fv}'")
    let consts := suggestions.constSuggestions.map fun (str, score, c, lvls) =>
      let params := lvls.map Level.param
      (str, score, MessageData.ofFormatWithInfos {
        fmt := "'" ++ Std.Format.tag 0 str ++ "'",
        infos :=
          .fromList [(0, Info.ofTermInfo {
            lctx := .empty,
            expr := .const c params,
            stx := .ident .none str.toSubstring c [],
            elaborator := `Delab,
            expectedType? := none
          })] _
      })
    let all := locals ++ consts |>.toArray |>.qsort lt
    let howMany : Nat := all.size
    let diff :=
        if howMany > 10 then [m!" (or {all.size - 10} others)"]
        else []
    let toShow := (all.extract 0 10 |>.toList |>.map (fun (_, _, msg) => msg)) ++ diff
    match toShow with
    | [s] => m!"Suggestion: {s}"
    | _ => m!"Suggestions: {MessageData.joinSep toShow ", "}"
where
  lt
    | (str1, score1, _), (str2, score2, _) =>
      if score1 == score2 then str1 < str2 else score1 < score2

def NameSuggestions.getReplacements (suggestions : NameSuggestions) (max := 10) : Array String :=
  let locals := suggestions.localSuggestions.map fun (str, score, _) =>
    (str, score)
  let consts := suggestions.constSuggestions.map fun (str, score, _, _) => (str, score)
  let all := locals ++ consts |>.toArray |>.qsort lt
  all.extract 0 max |>.map fun (x, _) => x
where
  lt
    | (str1, score1), (str2, score2) =>
      if score1 == score2 then str1 < str2 else score1 < score2

def NameSuggestions.saveInfo (ref : Syntax) (suggestions : NameSuggestions) : CoreM Unit := do
  if let some range := ref.getRange? then
    let map ← getFileMap
    let range := map.utf8RangeToLspRange range
    pushInfoLeaf <| .ofCustomInfo {
      stx := ref
      value := Dynamic.mk
        { range, replacements := suggestions.getReplacements : NameSuggestionInfo }
    }
