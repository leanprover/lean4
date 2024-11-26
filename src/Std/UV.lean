/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise

namespace UV

@[extern "lean_uv_initialize"]
opaque initUV : IO Unit

builtin_initialize initUV

namespace Loop

/--
Options for configuring the event loop behavior.
-/
structure Loop.Options where
  accumulateIdleTime : Bool := False
  blockSigProfSignal : Bool := False

/--
Configures the event loop with the specified options.
-/
@[extern "lean_uv_event_loop_configure"]
opaque configure (options : Loop.Options) : BaseIO Unit

/--
Gets the current timestamp from the event loop.
-/
@[extern "lean_uv_event_loop_now"]
opaque now : BaseIO UInt64

/--
Checks if the event loop is still active and processing events.
-/
@[extern "lean_uv_event_loop_alive"]
opaque alive : BaseIO Bool

end Loop

opaque Timer : Type := Unit

namespace Timer

/--
Creates a new timer associated with the given event loop and data.
-/
@[extern "lean_uv_timer_mk"]
opaque mk (timeout : UInt64) : IO Timer

/--
Starts a timer with the specified timeout interval (both in milliseconds).
-/
@[extern "lean_uv_timer_next"]
opaque next (timer : @& Timer) : IO (IO.Promise Nat)

/--
Stops the specified timer, preventing further callbacks.
-/
@[extern "lean_uv_timer_stop"]
opaque stop (timer : @& Timer) : IO Unit

end Timer
