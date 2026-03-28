/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.Data.Queue
public import Std.Internal.Async.IO

public section

open Std.Internal.Async.IO
open Std.Internal.IO.Async

/-!
This module provides `StreamMap`, a container that maps keys to async streams.
It allows for dynamic management of multiple named streams with async operations.
-/

namespace Std

/--
This is an existential wrapper for AsyncStream that is used for the `.ofArray` function
with `CoeDep` so it's easier and we keep StreamMap on `Type 0`.
-/
inductive AnyAsyncStream (α : Type) where
  | mk : {t : Type} → [AsyncStream t α] → t → AnyAsyncStream α

def AnyAsyncStream.getSelector : AnyAsyncStream α → Selector α × IO Unit
  | AnyAsyncStream.mk stream => (AsyncStream.next stream, AsyncStream.stop stream)

instance [AsyncStream t α] : CoeDep t x (AnyAsyncStream α) where
  coe := AnyAsyncStream.mk x

/--
A container that maps keys to async streams, enabling dynamic stream management
and unified selection operations across multiple named data sources.
-/
structure StreamMap (α : Type) (β : Type) where
  private mk ::
  private streams : Array (α × Selector β × IO Unit)

namespace StreamMap

/--
Create an empty StreamMap
-/
def empty {α} : StreamMap α β :=
  { streams := #[] }

/--
Register a new async stream with the given name
-/
def register [BEq α] [AsyncStream t β] (sm : StreamMap α β) (name : α) (reader : t) : StreamMap α β :=
  let newSelector := AsyncStream.next reader
  let filteredStreams := sm.streams.filter (fun (n, _) => n != name)
  { sm with streams := filteredStreams.push (name, newSelector, AsyncStream.stop reader) }

/--
Create a StreamMap from an array of named streams
-/
def ofArray [BEq α] (streams : Array (α × AnyAsyncStream β)) : StreamMap α β :=
  let arrayOfSelectors := streams.map (fun (name, sel) => (name, sel.getSelector))
  { streams := arrayOfSelectors }

/--
Get a combined selector that returns the stream name and value
-/
def selector (stream : StreamMap α β) : Async (Selector (α × β)) :=
  let selectables := stream.streams.map fun (name, selector) => Selectable.case selector.fst (fun x => pure (name, x))
  Selectable.combine selectables

/--
Wait for the first value inside of the stream map.
-/
def recv (stream : StreamMap α β) : Async (α × β) :=
  let selectables := stream.streams.map fun (name, selector) => Selectable.case selector.fst (fun x => pure (name, x))
  Selectable.one selectables

/--
Wait for the first value inside of the stream map.
-/
def tryRecv (stream : StreamMap α β) : Async (Option (α × β)) :=
  let selectables := stream.streams.map fun (name, selector) => Selectable.case selector.fst (fun x => pure (name, x))
  Selectable.tryOne selectables

/--
Remove a stream by name
-/
def unregister [BEq α] (sm : StreamMap α β) (name : α) : StreamMap α β :=
  { sm with streams := sm.streams.filter (fun (n, _) => n != name) }

/--
Check if a stream with the given name exists
-/
def contains [BEq α] (sm : StreamMap α β) (name : α) : Bool :=
  sm.streams.any (fun (n, _) => n == name)

/--
Get the number of registered streams
-/
def size (sm : StreamMap α β) : Nat :=
  sm.streams.size

/--
Check if the StreamMap is empty
-/
def isEmpty (sm : StreamMap α β) : Bool :=
  sm.streams.isEmpty

/--
Get all registered stream names
-/
def keys (sm : StreamMap α β) : Array α :=
  sm.streams.map (·.1)

/--
Get a specific stream selector by name
-/
def get? [BEq α] (sm : StreamMap α β) (name : α) : Option (Selector β) :=
  sm.streams.find? (fun (n, _) => n == name) |>.map (·.2.1)

/--
Filter streams based on their names
-/
def filterByName (sm : StreamMap α β) (pred : α → Bool) : StreamMap α β :=
  { streams := sm.streams.filter (fun (name, _) => pred name) }

/--
Convert to array of name-selector pairs
-/
def toArray (sm : StreamMap α β) : Array (α × Selector β) :=
  sm.streams.map (fun (n, s, _) => (n, s))

/--
Cleanup function
-/
def close (sm : StreamMap α β) : IO Unit :=
  sm.streams.forM (fun (_, _, cleanup) => cleanup)

end StreamMap
