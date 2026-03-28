/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Setup
public import Init.Data.String.TakeDrop

open Lean

namespace Lake

/-- Target output formats supported by the Lake CLI (e.g., `lake query`). -/
public inductive OutFormat
| /-- Format target output as text. -/ text
| /-- Format target output as JSON. -/ json

public class ToText (α : Type u) where
  toText : α → String

export ToText (toText)

public instance (priority := 0) [ToString α] : ToText α := ⟨toString⟩

@[inline] public def listToLines (as : List α) (f : α → String) : String :=
  as.foldl (s!"{·}{f ·}\n") "" |>.dropEnd 1 |>.copy

@[inline] public def arrayToLines (as : Array α) (f : α → String) : String :=
  as.foldl (s!"{·}{f ·}\n") "" |>.dropEnd 1 |>.copy

public instance : ToText Json := ⟨Json.compress⟩
public instance [ToText α] : ToText (List α) := ⟨(listToLines · toText)⟩
public instance [ToText α] : ToText (Array α) := ⟨(arrayToLines · toText)⟩

/-- Class used to format target output as text for `lake query`. -/
public class QueryText (α : Type u) where
  /-- Format target output as text (e.g., for `lake query`). -/
  queryText : α → String

export QueryText (queryText)

public instance (priority := 0) : QueryText α := ⟨fun _ => ""⟩
public instance (priority := low) [ToText α] : QueryText α := ⟨toText⟩
public instance [QueryText α] : QueryText (List α) := ⟨(listToLines · queryText)⟩
public instance [QueryText α] : QueryText (Array α) := ⟨(arrayToLines · queryText)⟩
public instance : QueryText Unit := ⟨fun _ => ""⟩

attribute [deprecated QueryText (since := "2025-07-25")] ToText

/-- Class used to format target output as JSON for `lake query -J`. -/
public class QueryJson (α : Type u) where
  /-- Format target output as JSON (e.g., for `lake query -J`). -/
  queryJson : α → Json

export QueryJson (queryJson)

public instance (priority := 0) : QueryJson α := ⟨fun _ => .null⟩
public instance (priority := low) [ToJson α] : QueryJson α := ⟨toJson⟩
public instance [QueryJson α] : QueryJson (List α) := ⟨(Json.arr <| ·.toArray.map queryJson)⟩
public instance [QueryJson α] : QueryJson (Array α) := ⟨(Json.arr <| ·.map queryJson)⟩
public instance : QueryJson Unit := ⟨fun _ => .null⟩

/-- Class used to format target output for `lake query`. -/
public class FormatQuery (α : Type u) extends QueryText α, QueryJson α

public instance [QueryText α] [QueryJson α] : FormatQuery α := {}

/-- Format function that produces "null" output. -/
public def nullFormat (fmt : OutFormat) (_ : α) : String :=
  match fmt with
  | .text => ""
  | .json => Json.null.compress

/-- Format function that uses `QueryText` and `QueryJson` to produce output. -/
@[specialize] public  def formatQuery [FormatQuery α] (fmt : OutFormat) (a : α) : String :=
  match fmt with
  | .text => queryText a
  | .json => queryJson a |>.compress

public def ppImport (imp : Import) (isModule : Bool) (init := "") : String := Id.run do
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

public def ppModuleHeader (header : ModuleHeader) : String :=
  let isModule := header.isModule
  let s := if isModule then "module prelude" else "prelude"
  header.imports.foldl (init := s) fun s imp =>
    ppImport imp isModule (s.push '\n')

instance : QueryText ModuleHeader := ⟨ppModuleHeader⟩
