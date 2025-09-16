/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.System.Promise
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.IO
public import Std.Internal.Async.Select
public import Std.Internal.Async.Basic

public import Std.Sync.Channel
public import Std.Sync.Broadcast

public section

open Std.Internal.Async.IO
open Std.Internal.IO.Async

/-!
This module provides `StreamMap`, a container that maps string keys to async streams.
It allows for dynamic management of multiple named streams with async operations.
-/

namespace Std

/--
This is an existential wrapper for AsyncStream that is used for the `.ofArray` function
with `CoeHead` so it's easier and we keep StreamMap on `Type 0`.
-/
inductive AnyAsyncStream (α : Type) where
  | mk : {t : Type} → [AsyncStream t α] → t → AnyAsyncStream α

def AnyAsyncStream.getSelector : AnyAsyncStream α → Selector α × IO Unit
  | AnyAsyncStream.mk stream => (AsyncStream.next stream, AsyncStream.stop stream)

instance [AsyncStream t α] : CoeHead t (AnyAsyncStream α) where
  coe := AnyAsyncStream.mk

/--
A map container that associates string keys with async streams.
Provides operations for adding, removing, and selecting from multiple streams.
-/
structure StreamMap (α : Type) where
  private mk ::
  private streams : Array (String × Selector α × IO Unit)

namespace StreamMap

/--
Create an empty StreamMap
-/
def empty {α} : StreamMap α :=
  { streams := #[] }

/--
Register a new async stream with the given name
-/
def register [AsyncStream t α] (sm : StreamMap α) (name : String) (reader : t) : StreamMap α :=
  let newSelector := AsyncStream.next reader
  let filteredStreams := sm.streams.filter (fun (n, _) => n != name)
  { sm with streams := filteredStreams.push (name, newSelector,  AsyncStream.stop reader) }

/--
Create a StreamMap from an array of named streams
-/
def ofArray {α} (streams : Array (String × AnyAsyncStream α)) : StreamMap α :=
  let arrayOfSelectors := streams.map (fun (name, sel) => (name, sel.getSelector))
  { streams := arrayOfSelectors }

/--
Get a combined selector that returns the stream name and value
-/
def selector (stream : StreamMap α) : Selector (String × α) :=
  let selectables := stream.streams.map fun (name, selector) => Selectable.case selector.fst (fun x => pure (name, x))
  Selectable.combine selectables

/--
Remove a stream by name
-/
def unregister (sm : StreamMap α) (name : String) : StreamMap α :=
  { sm with streams := sm.streams.filter (fun (n, _) => n != name) }

/--
Check if a stream with the given name exists
-/
def contains (sm : StreamMap α) (name : String) : Bool :=
  sm.streams.any (fun (n, _) => n == name)

/--
Get the number of registered streams
-/
def size (sm : StreamMap α) : Nat :=
  sm.streams.size

/--
Check if the StreamMap is empty
-/
def isEmpty (sm : StreamMap α) : Bool :=
  sm.streams.isEmpty

/--
Get all registered stream names
-/
def keys (sm : StreamMap α) : Array String :=
  sm.streams.map (·.1)

/--
Get a specific stream selector by name
-/
def get? (sm : StreamMap α) (name : String) : Option (Selector α) :=
  sm.streams.find? (fun (n, _) => n == name) |>.map (·.2.1)

/--
Filter streams based on their names
-/
def filterByName (sm : StreamMap α) (pred : String → Bool) : StreamMap α :=
  { streams := sm.streams.filter (fun (name, _) => pred name) }

/--
Convert to array of name-selector pairs
-/
def toArray (sm : StreamMap α) : Array (String × Selector α) :=
  sm.streams.map (fun (n, s, _) => (n, s))

/--
Cleanup function
-/
def close (sm : StreamMap α) : IO Unit :=
  sm.streams.forM (fun (_, _, cleanup) => cleanup)

end StreamMap
