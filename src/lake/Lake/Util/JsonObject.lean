/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json

open Lean

/-! # JSON Object
Defines a convenient wrapper type for JSON object data that makes
indexing fields more convenient.
-/

namespace Lake

/-- A JSON object (`Json.obj` data). -/
abbrev JsonObject :=
  RBNode String (fun _ => Json)

namespace JsonObject

@[inline] protected def toJson (obj : JsonObject) : Json :=
  .obj obj

instance : ToJson JsonObject := ⟨JsonObject.toJson⟩

@[inline] protected def fromJson? (json : Json) : Except String JsonObject :=
  json.getObj?

instance : FromJson JsonObject := ⟨JsonObject.fromJson?⟩

@[inline] nonrec def erase (obj : JsonObject) (prop : String) : JsonObject :=
  obj.erase compare prop

@[inline] def getJson? (obj : JsonObject) (prop : String) : Option Json :=
  obj.find compare prop

@[inline] def get [FromJson α] (obj : JsonObject) (prop : String) : Except String α :=
  match obj.getJson? prop with
  | none => throw s!"property not found: {prop}"
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[inline] def get? [FromJson α] (obj : JsonObject) (prop : String) : Except String (Option α) :=
  match obj.getJson? prop with
  | none => pure none
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[inline] def getD  [FromJson α] (obj : JsonObject) (prop : String) (default : α) : Except String α :=
  (Option.getD · default) <$> obj.get? prop
