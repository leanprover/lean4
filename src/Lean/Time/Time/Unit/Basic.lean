/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.UnitVal
import Lean.Time.Time.Unit.Hour
import Lean.Time.Time.Unit.Minute
import Lean.Time.Time.Unit.Second
import Lean.Time.Time.Unit.Nanosecond

set_option linter.all true

namespace Lean
namespace Time
namespace Second.Offset

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
