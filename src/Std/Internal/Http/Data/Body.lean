/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Version
import Std.Internal.Http.Data.Status
import Std.Sync

namespace Std
namespace Internal
namespace Http
namespace Data

structure ByteStream where
  data : Channel ByteArray
  want : IO.Ref Bool

inductive Body where
  | bytes (data : ByteArray)
  | channel (channel : ByteStream)
