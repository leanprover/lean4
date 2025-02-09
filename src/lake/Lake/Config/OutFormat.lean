/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Data.Json
import Lake.Build.Job.Basic

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

/-- Class used to format target output for `lake query`. -/
class FormatQuery (α : Type u) where
  formatQuery : OutFormat → α → String

export FormatQuery (formatQuery)

/-- A format function that produces "null" output. -/
def nullFormat (fmt : OutFormat) (_ : α) : String :=
  match fmt with
  | .text => ""
  | .json => Json.null.compress

instance (priority := 0) : FormatQuery α := ⟨nullFormat⟩

/-- Format function that uses `ToText` and `ToJson` to print output. -/
@[specialize] def stdFormat [ToText α] [ToJson α]  (fmt : OutFormat) (a : α) : String :=
  match fmt with
  | .text => toText a
  | .json => toJson a |>.compress

instance [ToText α] [ToJson α] : FormatQuery α := ⟨stdFormat⟩
instance: FormatQuery Unit := ⟨nullFormat⟩
