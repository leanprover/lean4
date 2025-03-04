/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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

@[inline] def mk (val : RBNode String (fun _ => Json)) : JsonObject :=
  val

@[inline] protected def toJson (obj : JsonObject) : Json :=
  .obj obj

instance : Coe JsonObject Json := ⟨Json.obj⟩
instance : ToJson JsonObject := ⟨JsonObject.toJson⟩

@[inline] protected def fromJson? (json : Json) : Except String JsonObject :=
  json.getObj?

instance : FromJson JsonObject := ⟨JsonObject.fromJson?⟩

@[inline] nonrec def insert [ToJson α] (obj : JsonObject) (prop : String) (val : α) : JsonObject :=
  obj.insert compare prop (toJson val)

@[inline] def insertSome [ToJson α] (obj : JsonObject) (prop : String) (val? : Option α) : JsonObject :=
  if let some val := val? then obj.insert prop val else obj

nonrec def erase (obj : JsonObject) (prop : String) : JsonObject :=
  inline <| obj.erase compare prop

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

@[macro_inline] def getD [FromJson α] (obj : JsonObject) (prop : String) (default : α) : Except String α := do
  return (← obj.get? prop).getD default
