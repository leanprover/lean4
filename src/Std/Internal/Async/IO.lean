/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.Select

public section

/-!
This module provides buffered asynchronous I/O operations for efficient reading and writing.
It implements buffered readers and writers to batch operations in memory buffers.
-/

namespace Std
namespace Internal
namespace Async
namespace IO

open Std.Internal.IO.Async

/--
Interface for asynchronous reading operations
-/
class AsyncRead (α : Type) (β : outParam Type) where
  read : α → Async β

/--
Interface for asynchronous writing operations
-/
class AsyncWrite (α : Type) (β : outParam Type) where
  write : α → β → Async Unit

/--
Interface for asynchronous streaming with selector-based iteration
-/
class AsyncStream (α : Type) (β : outParam Type) where
  next : α → Selector β

/--
Buffered reader that batches read operations for improved performance
-/
structure BufReader (t : Type) where
  reader : t
  buffer : ByteArray
  capacity : Nat
  used : Nat

/--
Buffered writer that batches write operations for improved performance
-/
structure BufWriter (t : Type) where
  reader : t
  buffer : ByteArray
  capacity : Nat
  used : Nat

namespace BufReader

/--
Create a new buffered reader with specified capacity
-/
def new [AsyncRead t ByteArray] (reader : t) (capacity : Nat := 8192) : BufReader t :=
  { reader := reader
  , buffer := ByteArray.emptyWithCapacity capacity
  , capacity := capacity
  , used := 0 }

end BufReader
end IO
end Async
end Internal
end Std
