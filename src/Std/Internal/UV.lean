/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise

namespace Std
namespace Internal
namespace UV

namespace Loop

/--
Options for configuring the event loop behavior.
-/
structure Loop.Options where
  /--
  Accumulate the amount of idle time the event loop spends in the event provider.
  -/
  accumulateIdleTime : Bool := False

  /--
  Block a SIGPROF signal when polling for new events. It's commonly used for unnecessary wakeups
  when using a sampling profiler.
  -/
  blockSigProfSignal : Bool := False

/--
Configures the event loop with the specified options.
-/
@[extern "lean_uv_event_loop_configure"]
opaque configure (options : Loop.Options) : BaseIO Unit

/--
Checks if the event loop is still active and processing events.
-/
@[extern "lean_uv_event_loop_alive"]
opaque alive : BaseIO Bool

end Loop

private opaque TimerImpl : NonemptyType.{0}

/--
`Timer`s are used to generate `IO.Promise`s that resolve after some time.

A `Timer` can be in one of 3 states:
- Right after construction it's initial.
- While it is ticking it's running.
- If it has stopped for some reason it's finished.

This together with whether it was set up as `repeating` with `Timer.new` determines the behavior
of all functions on `Timer`s.
-/
def Timer : Type := TimerImpl.type

instance : Nonempty Timer := TimerImpl.property

namespace Timer

/--
This creates a `Timer` in the initial state and doesn't run it yet.
- If `repeating` is `false` this constructs a timer that resolves once after `durationMs`
  milliseconds, counting from when it's run.
- If `repeating` is `true` this constructs a timer that resolves after multiples of `durationMs`
  milliseconds, counting from when it's run. Note that this includes the 0th multiple right after
  starting the timer.
-/
@[extern "lean_uv_timer_mk"]
opaque mk (timeout : UInt64) (repeating : Bool) : IO Timer

/--
This function has different behavior depending on the state and configuration of the `Timer`:
- if `repeating` is `false` and:
  - it is initial, run it and return a new `IO.Promise` that is set to resolve once `durationMs`
    milliseconds have elapsed. After this `IO.Promise` is resolved the `Timer` is finished.
  - it is running or finished, return the same `IO.Promise` that the first call to `next` returned.
- if `repeating` is `true` and:
  - it is initial, run it and return a new `IO.Promise` that resolves right away
    (as it is the 0th multiple of `durationMs`).
  - it is running, check whether the last returned `IO.Promise` is already resolved:
     - If it is, return a new `IO.Promise` that resolves upon finishing the next cycle
     - If it is not, return the last `IO.Promise`
     This ensures that the returned `IO.Promise` resolves at the next repetition of the timer.
Note that repeating timers can currently never finish.
-/

@[extern "lean_uv_timer_next"]
opaque next (timer : @& Timer) : IO (IO.Promise Unit)

/--
Resets the specified timer, preventing further callbacks.
-/
@[extern "lean_uv_timer_reset"]
opaque reset (timer : @& Timer) : IO Unit

end Timer
end UV
end Internal
end Std
