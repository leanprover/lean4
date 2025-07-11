/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Data
import Std.Internal.Http.Encode

open Std

namespace Std
namespace Http
namespace Data

/--
A structure for managing HTTP headers as key-value pairs.
-/
structure Headers where
  data : HashMap String (String × String)
deriving Repr, Inhabited

namespace Headers

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline]
def get? (headers : Headers) (name : String) : Option String :=
  headers.data.get? name.toLower <&> Prod.snd

/--
Tries to retrieve the mapping for the given key, returning the default value `default` if no such mapping is present.
-/
@[inline]
def getD (headers : Headers) (name : String) (default : String) : String :=
  (headers.data.get? name.toLower <&> Prod.snd) |>.getD default

/--
Retrieves the mapping for the given key, panics if no such mapping is present.
-/
@[inline]
def get! (headers : Headers) (name : String) : String :=
  headers.data.get! name.toLower |> Prod.snd

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (name : String) (value : String) : Headers :=
  { data := headers.data.insert name.toLower (name, value) }

instance : ToString Headers where
  toString headers :=
    let pairs := headers.data.toList.map (fun (_, (k, v)) => s!"{k}: {v}")
    String.intercalate "\r\n" pairs

instance : Encode .v11 Headers where
  encode buffer := buffer.writeString ∘ toString

/--
Creates empty headers.
-/
def empty : Headers :=
  { data := HashMap.emptyWithCapacity }

/--
Creates headers from a list of key-value pairs.
-/
def fromList (pairs : List (String × String)) : Headers :=
  { data := HashMap.ofList (pairs.map (fun (k, v) => (k.toLower, (k, v)))) }

/--
Checks if a header with the given name exists.
-/
@[inline]
def contains (headers : Headers) (name : String) : Bool :=
  headers.data.contains name.toLower

/--
Removes a header with the given name.
-/
@[inline]
def erase (headers : Headers) (name : String) : Headers :=
  { data := headers.data.erase name.toLower }

/--
Gets the number of headers.
-/
@[inline]
def size (headers : Headers) : Nat :=
  headers.data.size

/--
Checks if the headers are empty.
-/
@[inline]
def isEmpty (headers : Headers) : Bool :=
  headers.data.isEmpty

/--
Merges two headers, with the second taking precedence for duplicate keys.
-/
def merge (headers1 headers2 : Headers) : Headers :=
  { data := headers2.data.fold (fun acc k v => acc.insert k.toLower v) headers1.data }
