/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Data.Lsp.LanguageFeatures

namespace Lean.Lsp.ResolvableCompletionList

@[inline]
def compressItemDataFast (acc : String) (data : ResolvableCompletionItemData) :
    String := Id.run do
  let mut acc := acc ++ "["
  acc := acc ++ "\"" ++ data.mod.toString ++ "\""
  acc := acc ++ "," ++ data.pos.line.repr
  acc := acc ++ "," ++ data.pos.character.repr
  if let some cPos := data.cPos? then
    acc := acc ++ "," ++ cPos.repr
  if let some id := data.id? then
    acc := acc ++ ","
    match id with
    | .const declName =>
      acc := acc ++ "\"c" ++ declName.toString ++ "\""
    | .fvar id =>
      acc := acc ++ "\"f" ++ id.name.toString ++ "\""
  acc ++ "]"

@[inline]
def compressMarkupContentFast (acc : String) (c : MarkupContent) : String :=
  let kind := match c.kind with
    | .plaintext => "plaintext"
    | .markdown => "markdown"
  acc ++ "{\"kind\":\"" ++ kind ++ "\",\"value\":\"" ++ c.value ++ "\"}"

@[inline]
def compressPositionFast (acc : String) (p : Position) : String :=
  acc ++ "{\"character\":" ++ p.character.repr ++ ",\"line\":" ++ p.line.repr ++ "}"

@[inline]
def compressRangeFast (acc : String) (range : Range) : String :=
  let acc := acc ++ "{\"end\":"
  let acc := compressPositionFast acc range.end
  let acc := acc ++ ",\"start\":"
  let acc := compressPositionFast acc range.start
  acc ++ "}"

@[inline]
def compressEditFast (acc : String) (edit : InsertReplaceEdit) : String :=
  let acc := acc ++ "{\"insert\":"
  let acc := compressRangeFast acc edit.insert
  let acc := acc ++ ",\"newText\":\"" ++ edit.newText ++ "\""
  let acc := acc ++ ",\"replace\":"
  let acc := compressRangeFast acc edit.replace
  acc ++ "}"

def compressCompletionTagsFast (acc : String) (tags : Array CompletionItemTag) (i : Nat) :
    String :=
  if h : i < tags.size then
    let acc := acc ++ (tags[i].ctorIdx + 1).repr
    let acc :=
      if i < tags.size - 1 then
        acc ++ ","
      else
        acc
    compressCompletionTagsFast acc tags (i + 1)
  else
    acc

@[inline]
def compressItemFast (acc : String) (item : ResolvableCompletionItem) : String := Id.run do
  let mut acc := acc ++ "{\"label\":\"" ++ item.label ++ "\""
  if let some detail := item.detail? then
    acc := acc ++ ",\"detail\":\"" ++ detail ++ "\""
  if let some documentation := item.documentation? then
    acc := acc ++ ",\"documentation\":"
    acc := compressMarkupContentFast acc documentation
  if let some kind := item.kind? then
    acc := acc ++ ",\"kind\":" ++ (kind.ctorIdx + 1).repr
  if let some textEdit := item.textEdit? then
    acc := acc ++ ",\"edit\":"
    acc := compressEditFast acc textEdit
  if let some sortText := item.sortText? then
    acc := acc ++ ",\"sortText\":\"" ++ sortText ++ "\""
  if let some data := item.data? then
    acc := acc ++ ",\"data\":"
    acc := compressItemDataFast acc data
  if let some tags := item.tags? then
    acc := acc ++ ",\"tags\":["
    if h : tags.size == 1 then
      have : 0 < tags.size := by
        rw [beq_iff_eq] at h
        simp [h]
      acc := acc ++ (tags[0].ctorIdx + 1).repr
    else
      acc := compressCompletionTagsFast acc tags 0
    acc := acc ++ "]"
  return acc ++ "}"

def compressItemsFast
    (acc : String) (items : Array ResolvableCompletionItem) (i : Nat) :
    String :=
  if h : i < items.size then
    let acc := compressItemFast acc items[i]
    let acc :=
      if i < items.size - 1 then
        acc ++ ","
      else
        acc
    compressItemsFast acc items (i + 1)
  else
    acc

/--
Fast path for `(toJson l).compress` that skips the intermediate `Json` object.
Used in place of `(toJson l).compress` in the language server.
-/
public def compressFast (l : ResolvableCompletionList) : String :=
  let acc := "{\"isIncomplete\":" ++ toString l.isIncomplete ++ ",\"items\":["
  let acc := compressItemsFast acc l.items 0
  acc ++ "]}"
