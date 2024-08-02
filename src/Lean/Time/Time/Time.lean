/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Time.Basic

namespace Lean
namespace Time

structure Time where
  hour : Hour.Ordinal
  minute : Minute.Ordinal
  second : Second.Ordinal
  nano : Nanosecond.Ordinal
  deriving Repr, Inhabited, BEq

namespace Time

def toSeconds (time : Time) : Second.Offset :=
  time.hour.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.toOffset

def toMinutes (time : Time) : Minute.Offset :=
  time.hour.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.toOffset.toMinutes
