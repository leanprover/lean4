/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Internal.Http.Encode
import Std.Internal.Http.Data.Status
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Version

namespace Std
namespace Http
namespace Data

structure Response (t : Type) where
  status : Status
  version : Version
  headers : Headers
  body : t
deriving Inhabited

instance : ToString (Response t) where
  toString r :=
    toString r.version ++ " " ++
    toString r.status.toCode ++ " " ++
    toString r.status ++ "\r\n" ++
    toString r.headers ++ "\r\n\r\n"
