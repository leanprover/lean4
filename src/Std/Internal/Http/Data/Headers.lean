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
  data : HashMap String (String × HashSet String)
deriving Repr, Inhabited

namespace Headers

/--
Splits a header value on commas, trims whitespace, puts into a HashSet.
-/
def splitValues (value : String) : HashSet String :=
  HashSet.ofList <| value.splitOn "," |>.map String.trim

/--
Tries to retrieve the header values for the given key, as a HashSet.
Returns `none` if the header is absent.
-/
@[inline]
def getSingle? (headers : Headers) (name : String) : Option String :=
  headers.data.get? name.toLower |>.map (List.head! ∘ HashSet.toList ∘ Prod.snd)

/--
Tries to retrieve the header values for the given key, as a HashSet.
Returns `none` if the header is absent.
-/
@[inline]
def get? (headers : Headers) (name : String) : Option (HashSet String) :=
  headers.data.get? name.toLower |>.map Prod.snd

/--
Like `get?`, but returns an empty HashSet if absent.
-/
@[inline]
def getD (headers : Headers) (name : String) : HashSet String :=
  headers.get? name |>.getD ∅

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! (headers : Headers) (name : String) : HashSet String :=
  headers.data.get! name.toLower |> Prod.snd

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (name : String) (value : String) : Headers :=
  let key := name.toLower
  let data := headers.data.get? key
  let words := splitValues value
  let hm := if let some (name, hm) := data then (name, hm.insertMany words) else (name, words)
  { data := headers.data.insert key hm }

instance : ToString Headers where
  toString headers :=
    let pairs := headers.data.toList.map (fun (_, (k, vs)) => s!"{k}: {String.intercalate ", " vs.toList}")
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
  { data := HashMap.ofList (pairs.map (fun (k, v) => (k.toLower, (k, splitValues v)))) }

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
