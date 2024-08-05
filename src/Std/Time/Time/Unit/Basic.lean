/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.UnitVal
import Std.Time.Time.Unit.Hour
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second
import Std.Time.Time.Unit.Nanosecond

namespace Std
namespace Time
namespace Second.Offset

set_option linter.all true

/-- Convert `Second.Offset` to `Minute.Offset` -/
@[inline]
def toMinutes (offset : Second.Offset) : Minute.Offset :=
  offset.div 60

/-- Convert `Second.Offset` to `Hour.Offset` -/
@[inline]
def toHours (offset : Second.Offset) : Hour.Offset :=
  offset.div 3600

end Second.Offset

namespace Minute.Offset

/-- Convert `Minute.Offset` to `Hour.Offset` -/
@[inline]
def toHours (offset : Minute.Offset) : Hour.Offset :=
  offset.div 60

end Minute.Offset

end Time
end Std
