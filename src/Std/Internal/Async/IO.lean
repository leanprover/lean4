/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.Select

public section

namespace Std
namespace Internal
namespace Async
namespace IO

open Std.Internal.IO.Async

/-!
This module provides buffered asynchronous I/O operations for efficient reading and writing.
-/

/--
Interface for asynchronous reading operations.
-/
class AsyncRead (α : Type) (β : Type) where
  read : α → Async β

/--
Interface for asynchronous writing operations.
-/
class AsyncWrite (α : Type) (β : Type) where
  write : α → β → Async Unit

  writeAll : α → Array β → Async Unit :=
    fun socket data => data.forM (write socket)

  flush : α → Async Unit :=
    fun _ => pure ()

/--
Interface for asynchronous streaming with selector-based iteration.
-/
class AsyncStream (α : Type) (β : outParam Type) where
  next : α → Selector β

  stop : α → IO Unit :=
    fun _ => pure ()

end IO
end Async
end Internal
end Std
