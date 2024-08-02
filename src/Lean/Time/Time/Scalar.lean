/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Time.Basic

namespace Lean
namespace Time

structure Scalar where
  second : Second.Offset
  nano : Nanosecond.Ordinal

namespace Scalar

def toSeconds (time : Scalar) : Second.Offset :=
  time.second

def toMinutes (time : Scalar) : Minute.Offset :=
  time.second.toMinutes

def toHours (time : Scalar) : Hour.Offset :=
  time.second.toHours

end Scalar
end Time
