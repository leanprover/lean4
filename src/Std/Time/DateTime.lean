/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime.NaiveDateTime
import Std.Time.DateTime.Timestamp

namespace Std
namespace Time
namespace Timestamp

set_option linter.all true

/--
Converts a `NaiveDateTime` to a `Timestamp`
-/
@[inline]
def ofNaiveDateTime (naive : NaiveDateTime) : Timestamp :=
  naive.toTimestamp

/--
Converts a `Timestamp` to a `NaiveDateTime`
-/
@[inline]
def toNaiveDateTime (timestamp : Timestamp) : NaiveDateTime :=
  NaiveDateTime.ofTimestamp timestamp
