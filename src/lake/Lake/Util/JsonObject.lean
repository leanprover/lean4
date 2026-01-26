/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json

open Lean

/-! # JSON Object
Defines a convenient wrapper type for JSON object data that makes
indexing fields more convenient.
-/

namespace Lake

/-- A JSON object (`Json.obj` data). -/
@[expose] public abbrev JsonObject :=
  Std.TreeMap.Raw String Json

namespace JsonObject

@[inline] public def mk (val : Std.TreeMap.Raw String Json) : JsonObject :=
  val

@[inline] public def empty : JsonObject :=
  Std.TreeMap.Raw.empty

@[inline] public protected def toJson (obj : JsonObject) : Json :=
  .obj obj

public instance : Coe JsonObject Json := ⟨Json.obj⟩
public instance : ToJson JsonObject := ⟨JsonObject.toJson⟩

@[inline] public protected def fromJson? (json : Json) : Except String JsonObject :=
  json.getObj?

public instance : FromJson JsonObject := ⟨JsonObject.fromJson?⟩

@[inline] public nonrec def contains (obj : JsonObject) (prop : String) : Bool :=
  obj.contains prop

public def insertJson (obj : JsonObject) (prop : String) (val : Json) : JsonObject :=
  obj.insert prop (toJson val) -- specializes `insert`

@[inline] public def insert [ToJson α] (obj : JsonObject) (prop : String) (val : α) : JsonObject :=
  obj.insertJson prop (toJson val)

@[inline] public def insertSome [ToJson α] (obj : JsonObject) (prop : String) (val? : Option α) : JsonObject :=
  if let some val := val? then obj.insert prop val else obj

public nonrec def erase (obj : JsonObject) (prop : String) : JsonObject :=
  obj.erase prop -- specializes `erase`

public def getJson? (obj : JsonObject) (prop : String) : Option Json :=
  obj.get? prop -- specializes `get?`

@[inline] public def get [FromJson α] (obj : JsonObject) (prop : String) : Except String α :=
  match obj.getJson? prop with
  | none => throw s!"property not found: {prop}"
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[inline] public def get? [FromJson α] (obj : JsonObject) (prop : String) : Except String (Option α) :=
  match obj.getJson? prop with
  | none => pure none
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[macro_inline, expose] public def getD [FromJson α] (obj : JsonObject) (prop : String) (default : α) : Except String α := do
  return (← obj.get? prop).getD default
