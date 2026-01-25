/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Std.Data.HashMap
public import Std.Internal.Http.Internal

public section

/-!
# Headers

This module provides the `Headers` type, a case-insensitive wrapper around
`HashMap String (Array String)` for HTTP headers.
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
Case-insensitive HTTP headers collection. Header names are stored in lowercase
internally, and rendered in canonical form (e.g., `Content-Type`) when converted
to strings.
-/
structure Headers where

  /--
  The underlying map storing lowercase header names to their values.
  -/
  map : HashMap String (Array String) := .emptyWithCapacity
deriving Inhabited, Repr

namespace Headers

/--
An empty headers collection.
-/
def empty : Headers :=
  { map := .emptyWithCapacity }

/--
An empty headers collection. Same as `empty`.
-/
def emptyWithCapacity (n : Nat := 8) : Headers :=
  { map := .emptyWithCapacity n }

instance : EmptyCollection Headers := ⟨empty⟩

/--
Adds a header value, appending to any existing values for that name.
-/
def add (h : Headers) (key : String) (value : String) : Headers :=
  let k := key.toLower
  { map := h.map.alter k (fun values => some <| (values.getD #[]).push value) }

/--
Sets all values for a header name, replacing any existing values.
-/
def insert (h : Headers) (key : String) (values : Array String) : Headers :=
  { map := h.map.insert key.toLower values }

/--
Gets all values for a header name, or `none` if not present.
-/
def get? (h : Headers) (key : String) : Option (Array String) :=
  h.map.get? key.toLower

/--
Gets all values for a header name, or a default if not present.
-/
def getD (h : Headers) (key : String) (default : Array String := #[]) : Array String :=
  h.map.getD key.toLower default

/--
Converts a lowercase header key to canonical HTTP form (e.g., `content-type` → `Content-Type`).
-/
protected def toCanonical (key : String) : String :=
  key.splitOn "-"
  |> List.map (String.capitalize ∘ toString)
  |> String.intercalate "-"

/--
Renders headers as HTTP wire format with canonical header names.
-/
def toString (h : Headers) : String :=
  h.map.fold (init := "") fun acc key values =>
  values.foldl (init := acc) fun acc value =>
    acc ++ Headers.toCanonical key ++ ": " ++ value ++ "\r\n"

instance : ToString Headers where
  toString := Headers.toString

instance : Encode .v11 Headers where
  encode buffer h :=
    h.map.fold (init := buffer) fun buf key values =>
    values.foldl (init := buf) fun buf value =>
      buf.writeString (Headers.toCanonical key ++ ": " ++ value ++ "\r\n")

end Headers
end Std.Http
