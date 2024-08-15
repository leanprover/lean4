/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime.Timestamp
import Std.Time.DateTime.LocalDateTime

namespace Std
namespace Time
namespace Timestamp

set_option linter.all true

/--
Converts a `LocalDateTime` to a `Timestamp`
-/
@[inline]
def ofLocalDateTime (Local : LocalDateTime) : Timestamp :=
  Local.toUTCTimestamp

/--
Converts a `Timestamp` to a `LocalDateTime`
-/
@[inline]
def toLocalDateTime (timestamp : Timestamp) : LocalDateTime :=
  LocalDateTime.ofUTCTimestamp timestamp
