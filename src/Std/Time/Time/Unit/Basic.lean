/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Time.Unit.Hour
public import Std.Time.Time.Unit.Millisecond

public section

/-!
This module defines various units used for measuring, counting, and converting between hours, minutes,
second, nanosecond, millisecond and nanoseconds.

The units are organized into types representing these time-related concepts, with operations provided
to facilitate conversions and manipulations between them.
-/

namespace Std
namespace Time
open Internal

set_option linter.all true

namespace Nanosecond.Offset

/--
Converts a `Nanosecond.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (offset : Nanosecond.Offset) : Millisecond.Offset :=
  offset.div 1000000 |>.cast (by decide +kernel)

/--
Converts a `Millisecond.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def ofMilliseconds (offset : Millisecond.Offset) : Nanosecond.Offset :=
  offset.mul 1000000 |>.cast (by decide +kernel)

/--
Converts a `Nanosecond.Offset` to a `Second.Offset`.
-/
@[inline]
def toSeconds (offset : Nanosecond.Offset) : Second.Offset :=
  offset.div 1000000000 |>.cast (by decide +kernel)

/--
Converts a `Second.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def ofSeconds (offset : Second.Offset) : Nanosecond.Offset :=
  offset.mul 1000000000

/--
Converts a `Nanosecond.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (offset : Nanosecond.Offset) : Minute.Offset :=
  offset.div 60000000000 |>.cast (by decide +kernel)

/--
Converts a `Minute.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def ofMinutes (offset : Minute.Offset) : Nanosecond.Offset :=
  offset.mul 60000000000 |>.cast (by decide +kernel)

/--
Converts a `Nanosecond.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Nanosecond.Offset) : Hour.Offset :=
  offset.div 3600000000000 |>.cast (by decide +kernel)

/--
Converts an `Hour.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def ofHours (offset : Hour.Offset) : Nanosecond.Offset :=
  offset.mul 3600000000000 |>.cast (by decide +kernel)

end Nanosecond.Offset

namespace Millisecond.Offset

/--
Converts a `Millisecond.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (offset : Millisecond.Offset) : Nanosecond.Offset :=
  offset.mul 1000000 |>.cast (by decide +kernel)

/--
Converts a `Nanosecond.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def ofNanoseconds (offset : Nanosecond.Offset) : Millisecond.Offset :=
  offset.toMilliseconds

/--
Converts a `Millisecond.Offset` to a `Second.Offset`.
-/
@[inline]
def toSeconds (offset : Millisecond.Offset) : Second.Offset :=
  offset.div 1000 |>.cast (by decide +kernel)

/--
Converts a `Second.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def ofSeconds (offset : Second.Offset) : Millisecond.Offset :=
  offset.mul 1000

/--
Converts a `Millisecond.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (offset : Millisecond.Offset) : Minute.Offset :=
  offset.div 60000 |>.cast (by decide +kernel)

/--
Converts a `Minute.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def ofMinutes (offset : Minute.Offset) : Millisecond.Offset :=
  offset.mul 60000 |>.cast (by decide +kernel)

/--
Converts a `Millisecond.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Millisecond.Offset) : Hour.Offset :=
  offset.div 3600000 |>.cast (by decide +kernel)

/--
Converts an `Hour.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def ofHours (offset : Hour.Offset) : Millisecond.Offset :=
  offset.mul 3600000 |>.cast (by decide +kernel)

end Millisecond.Offset

namespace Second.Offset

/--
Converts a `Second.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (offset : Second.Offset) : Nanosecond.Offset :=
  offset.mul 1000000000

/--
Converts a `Nanosecond.Offset` to a `Second.Offset`.
-/
@[inline]
def ofNanoseconds (offset : Nanosecond.Offset) : Second.Offset :=
  offset.toSeconds

/--
Converts a `Second.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (offset : Second.Offset) : Millisecond.Offset :=
  offset.mul 1000

/--
Converts a `Millisecond.Offset` to a `Second.Offset`.
-/
@[inline]
def ofMilliseconds (offset : Millisecond.Offset) : Second.Offset :=
  offset.toSeconds

/--
Converts a `Second.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (offset : Second.Offset) : Minute.Offset :=
  offset.div 60 |>.cast (by decide +kernel)

/--
Converts a `Minute.Offset` to a `Second.Offset`.
-/
@[inline]
def ofMinutes (offset : Minute.Offset) : Second.Offset :=
  offset.mul 60 |>.cast (by decide +kernel)

/--
Converts a `Second.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Second.Offset) : Hour.Offset :=
  offset.div 3600 |>.cast (by decide +kernel)

/--
Converts an `Hour.Offset` to a `Second.Offset`.
-/
@[inline]
def ofHours (offset : Hour.Offset) : Second.Offset :=
  offset.mul 3600 |>.cast (by decide +kernel)

end Second.Offset

namespace Minute.Offset

/--
Converts a `Minute.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (offset : Minute.Offset) : Nanosecond.Offset :=
  offset.mul 60000000000 |>.cast (by decide +kernel)

/--
Converts a `Nanosecond.Offset` to a `Minute.Offset`.
-/
@[inline]
def ofNanoseconds (offset : Nanosecond.Offset) : Minute.Offset :=
  offset.toMinutes

/--
Converts a `Minute.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (offset : Minute.Offset) : Millisecond.Offset :=
  offset.mul 60000 |>.cast (by decide +kernel)

/--
Converts a `Millisecond.Offset` to a `Minute.Offset`.
-/
@[inline]
def ofMilliseconds (offset : Millisecond.Offset) : Minute.Offset :=
  offset.toMinutes

/--
Converts a `Minute.Offset` to a `Second.Offset`.
-/
@[inline]
def toSeconds (offset : Minute.Offset) : Second.Offset :=
  offset.mul 60 |>.cast (by decide +kernel)

/--
Converts a `Second.Offset` to a `Minute.Offset`.
-/
@[inline]
def ofSeconds (offset : Second.Offset) : Minute.Offset :=
  offset.toMinutes

/--
Converts a `Minute.Offset` to an `Hour.Offset`.
-/
@[inline]
def toHours (offset : Minute.Offset) : Hour.Offset :=
  offset.div 60 |>.cast (by decide +kernel)

/--
Converts an `Hour.Offset` to a `Minute.Offset`.
-/
@[inline]
def ofHours (offset : Hour.Offset) : Minute.Offset :=
  offset.mul 60 |>.cast (by decide +kernel)

end Minute.Offset

namespace Hour.Offset

/--
Converts an `Hour.Offset` to a `Nanosecond.Offset`.
-/
@[inline]
def toNanoseconds (offset : Hour.Offset) : Nanosecond.Offset :=
  offset.mul 3600000000000 |>.cast (by decide +kernel)

/--
Converts a `Nanosecond.Offset` to an `Hour.Offset`.
-/
@[inline]
def ofNanoseconds (offset : Nanosecond.Offset) : Hour.Offset :=
  offset.toHours

/--
Converts an `Hour.Offset` to a `Millisecond.Offset`.
-/
@[inline]
def toMilliseconds (offset : Hour.Offset) : Millisecond.Offset :=
  offset.mul 3600000 |>.cast (by decide +kernel)

/--
Converts a `Millisecond.Offset` to an `Hour.Offset`.
-/
@[inline]
def ofMilliseconds (offset : Millisecond.Offset) : Hour.Offset :=
  offset.toHours

/--
Converts an `Hour.Offset` to a `Second.Offset`.
-/
@[inline]
def toSeconds (offset : Hour.Offset) : Second.Offset :=
  offset.mul 3600 |>.cast (by decide +kernel)

/--
Converts a `Second.Offset` to an `Hour.Offset`.
-/
@[inline]
def ofSeconds (offset : Second.Offset) : Hour.Offset :=
  offset.toHours

/--
Converts an `Hour.Offset` to a `Minute.Offset`.
-/
@[inline]
def toMinutes (offset : Hour.Offset) : Minute.Offset :=
  offset.mul 60 |>.cast (by decide +kernel)

/--
Converts a `Minute.Offset` to an `Hour.Offset`.
-/
@[inline]
def ofMinutes (offset : Minute.Offset) : Hour.Offset :=
  offset.toHours

end Hour.Offset

end Time
end Std
