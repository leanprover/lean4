/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Internal.Http.Encode
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Method
import Std.Internal.Http.Data.Version

namespace Std
namespace Http
namespace Data

structure Request (t : Type) where
  method : Method
  version : Version
  uri : String
  headers : Headers
  body : t

instance : ToString (Request t) where
  toString req :=
    toString req.method ++ " " ++
    req.uri ++ " " ++
    toString req.version ++
    "\r\n" ++
    toString req.headers ++ "\r\n\r\n"
