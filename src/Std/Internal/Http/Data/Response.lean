/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Version
import Std.Internal.Http.Data.Status
import Std.Internal.Http.Data.Body
import Std.Sync

namespace Std
namespace Internal
namespace Http
namespace Data

structure Response where
  status : Status
  version : Version
  headers : Headers
  body : Body

instance : ToString Response where
  toString r :=
    let headerString := toString r.version ++ " " ++ toString r.status.toCode ++ " " ++ toString r.status ++ "\r\n" ++ toString r.headers
    headerString ++ "\r\n\r\n"
