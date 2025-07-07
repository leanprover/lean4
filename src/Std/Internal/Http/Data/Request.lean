/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Version
import Std.Internal.Http.Data.Method
import Std.Sync

namespace Std
namespace Internal
namespace Http
namespace Data

/--

-/
structure Request (α : Type) where
  method : Method
  version : Version
  uri : String
  headers : Headers
  body : α

namespace Request
