/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.Time.Unit.Hour
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second
import Std.Time.Time.Unit.Nanosecond
import Std.Time.Time.Unit.Millisecond

/-!
This module defines various units used for measuring, counting, and converting between hours, minutes,
second, nanosecond, millisecond and nanoseconds.

The units are organized into types representing these time-related concepts, with operations provided
to facilitate conversions and manipulations between them.
-/

namespace Std
namespace Time
namespace Second.Offset
open Internal

set_option linter.all true

/--
Converts a `Second.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (offset : Second.Offset) : Minute.Offset :=
  offset.ediv 60

/--
Converts a `Second.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Second.Offset) : Hour.Offset :=
  offset.ediv 3600

end Second.Offset

namespace Minute.Offset

/--
Converts a `Minute.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Minute.Offset) : Hour.Offset :=
  offset.ediv 60

end Minute.Offset

end Time
end Std
