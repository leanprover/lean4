/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Setup

open Lean

namespace Lake

/-- Target output formats supported by the Lake CLI (e.g., `lake query`). -/
inductive OutFormat
| /-- Format target output as text. -/ text
| /-- Format target output as JSON. -/ json

class ToText (α : Type u) where
  toText : α → String

export ToText (toText)

instance (priority := 0) [ToString α] : ToText α := ⟨toString⟩

instance : ToText Json := ⟨Json.compress⟩
instance [ToText α] : ToText (List α) := ⟨(·.foldl (s!"{·}{toText ·}\n") "" |>.dropRight 1)⟩
instance [ToText α] : ToText (Array α) := ⟨(·.foldl (s!"{·}{toText ·}\n") "" |>.dropRight 1)⟩

/-- Class used to format target output as text for `lake query`. -/
class QueryText (α : Type u) where
  /-- Format target output as text (e.g., for `lake query`). -/
  queryText : α → String

export QueryText (queryText)

instance (priority := 0) : QueryText α := ⟨fun _ => ""⟩
instance (priority := low) [ToText α] : QueryText α := ⟨toText⟩
instance : QueryText Unit := ⟨fun _ => ""⟩

attribute [deprecated QueryText (since := "2025-07-25")] ToText

/-- Class used to format target output as JSON for `lake query -J`. -/
class QueryJson (α : Type u) where
  /-- Format target output as JSON (e.g., for `lake query -J`). -/
  queryJson : α → Json

export QueryJson (queryJson)

instance (priority := 0) : QueryJson α := ⟨fun _ => .null⟩
instance (priority := low) [ToJson α] : QueryJson α := ⟨toJson⟩
instance : QueryJson Unit := ⟨fun _ => .null⟩

/-- Class used to format target output for `lake query`. -/
class FormatQuery (α : Type u) extends QueryText α, QueryJson α

instance [QueryText α] [QueryJson α] : FormatQuery α := {}

/-- Format function that produces "null" output. -/
def nullFormat (fmt : OutFormat) (_ : α) : String :=
  match fmt with
  | .text => ""
  | .json => Json.null.compress

/-- Format function that uses `QueryText` and `QueryJson` to produce output. -/
@[specialize] def formatQuery [FormatQuery α] (fmt : OutFormat) (a : α) : String :=
  match fmt with
  | .text => queryText a
  | .json => queryJson a |>.compress

def ppImport (imp : Import) (isModule : Bool) (init := "") : String := Id.run do
  let mut s := init
  if isModule && imp.isExported then
    s := s ++ "public "
  if imp.isMeta then
    s := s ++ "meta "
  s := s ++ "import "
   if imp.importAll then
    s := s!"{s}all "
  s := s ++ imp.module.toString
  return s

def ppModuleHeader (header : ModuleHeader) : String :=
  let isModule := header.isModule
  let s := if isModule then "module prelude" else "prelude"
  header.imports.foldl (init := s) fun s imp =>
    ppImport imp isModule (s.push '\n')

instance : QueryText ModuleHeader := ⟨ppModuleHeader⟩
