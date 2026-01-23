/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Internal.ChunkedBuffer
public import Std.Internal.Http.Data.Version

public section

/-!
# Encode

Serializes types to a `ChunkedBuffer` containing their canonical HTTP representation for a specific
protocol version.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Serializes a type `t` to a `ChunkedBuffer` containing its canonical HTTP representation for protocol
version `v`.
-/
class Encode (v : Version) (t : Type) where
  /--
  Encodes a type `t` to a `ChunkedBuffer`.
  -/
  encode : ChunkedBuffer → t → ChunkedBuffer

instance : Encode .v11 Version where
  encode buffer := buffer.writeString ∘ toString

end Std.Http.Internal
