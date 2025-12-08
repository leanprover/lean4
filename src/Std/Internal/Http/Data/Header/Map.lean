/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Slice
public import Init.Data.String
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Std.Internal.Http.Data.Header.Name
public import Std.Internal.Http.Internal

public section

/-!
# Headers

This module defines the `Headers` type, which represents an efficient collection of HTTP header
name-value pairs. The implementation is optimized for fast lookups and insertions while providing
a convenient interface for managing HTTP headers in both requests and responses.
-/

namespace Std.Http

open Std Internal

set_option linter.all true


/--
A structure for managing HTTP headers as key-value pairs.
-/
structure Headers where
  /--
  The internal hashmap that stores all the data.
  -/
  data : HashMap HeaderName (Array HeaderValue)

deriving Repr, Inhabited

namespace Headers

/--
Retrieves the `HeaderValue` for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def get (headers : Headers) (name : HeaderName) : Option HeaderValue :=
  headers.data.get? name
  |>.map (.joinCommaSep)

/--
Retrieves all `HeaderValue` entries for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getAll? (headers : Headers) (name : HeaderName) : Option (Array HeaderValue) :=
  headers.data.get? name

/--
Checks if the entry is present in the `Headers`.
-/
@[inline]
def hasEntry (headers : Headers) (name : HeaderName) (value : String) : Bool :=
  headers.data.get? name
  |>.bind (·.find? (·.is value))
  |>.isSome

/--
Retrieves the last header value for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getLast? (headers : Headers) (name : HeaderName) : Option HeaderValue :=
  headers.data.get? name
  |>.bind (fun x => x[x.size - 1]?)


/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD (headers : Headers) (name : HeaderName) (d : HeaderValue) : HeaderValue :=
  headers.get name |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! (headers : Headers) (name : HeaderName) : HeaderValue :=
  headers.get name |>.get!

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (key : HeaderName) (value : HeaderValue) : Headers :=

  if let some headerValue := headers.data.get? key then
    { data := headers.data.insert key (headerValue.push value) }
  else
    { data := headers.data.insert key #[value] }

/--
Inserts a new key with an array of values.
-/
@[inline]
def insertMany (headers : Headers) (key : HeaderName) (value : Array HeaderValue) : Headers :=
  if let some headerValue := headers.data.get? key then
    { data := headers.data.insert key (headerValue ++ value) }
  else
    { data := headers.data.insert key value }

/--
Creates empty headers.
-/
def empty : Headers :=
  { data := ∅ }

/--
Creates headers from a list of key-value pairs.
-/
def ofList (pairs : List (HeaderName × HeaderValue)) : Headers :=
  { data := HashMap.ofList (pairs.map (fun (k, v) => (k, #[v]))) }

/--
Checks if a header with the given name exists.
-/
@[inline]
def contains (headers : Headers) (name : HeaderName) : Bool :=
  headers.data.contains name

/--
Removes a header with the given name.
-/
@[inline]
def erase (headers : Headers) (name : HeaderName) : Headers :=
  { data := headers.data.erase name }

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
  headers2.data.fold (fun acc k v => acc.insertMany k v) headers1

instance : ToString Headers where
  toString headers :=
    let pairs := headers.data.toArray.flatMap (fun (k, vs) => vs.map (k, ·))
    let pairs := pairs.map (fun (k, vs) => s!"{k}: {vs.value}")
    String.intercalate "\r\n" pairs.toList

instance : Encode .v11 Headers where
  encode buffer := buffer.writeString ∘ toString

end Std.Http.Headers
