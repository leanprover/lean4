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
opaque initSocket : IO Unit

builtin_initialize initSocket

/--
Structure representing an event loop with a reference and data of type α.
-/
opaque EventLoop : Type := Unit

namespace EventLoop

/--
Runs the event loop in the specified run mode.
-/
@[extern "lean_uv_event_loop_mk"]
opaque mk : IO EventLoop

/--
Run mode options for the event loop, controlling its execution behavior.
-/
inductive RunMode
  | Default
  | Once
  | NoWait

/--
Runs the event loop in the specified run mode.
-/
@[extern "lean_uv_event_loop_run"]
opaque run (loop : @& EventLoop) (runMode : RunMode) : IO Unit

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
opaque configure (loop : @& EventLoop) (options : Loop.Options) : BaseIO Unit

/--
Closes the event loop from running further events.
-/
@[extern "lean_uv_event_loop_close"]
opaque close (loop : @& EventLoop) : BaseIO Unit

/--
Stops the event loop from running further events.
-/
@[extern "lean_uv_event_loop_stop"]
opaque stop (loop : @& EventLoop) : BaseIO Unit

/--
Gets the current timestamp from the event loop.
-/
@[extern "lean_uv_event_loop_now"]
opaque now (loop : @& EventLoop) : BaseIO UInt64

/--
Checks if the event loop is still active and processing events.
-/
@[extern "lean_uv_event_loop_alive"]
opaque alive (loop : @& EventLoop) : BaseIO Bool

end EventLoop

opaque Timer : Type := Unit

namespace Timer

/--
Creates a new timer associated with the given event loop and data.
-/
@[extern "lean_uv_timer_mk"]
opaque mk (loop : @& EventLoop) (timeout : UInt64) : IO Timer

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
