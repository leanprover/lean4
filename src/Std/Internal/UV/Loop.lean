/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise

@[expose] public section

namespace Std
namespace Internal
namespace UV
namespace Loop

/--
Options for configuring the event loop behavior.
-/
structure Options where
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

Fails with `UV_ECANCELED` once the event loop has been torn down at exit.
-/
@[extern "lean_uv_event_loop_configure"]
opaque configure (options : @& Options) : IO Unit

/--
Checks if the event loop is still active and processing events. Returns `false` once the event loop
has been torn down at exit.

The teardown runs in `lean_finalize_task_manager` and is final: an embedder that initializes a task
manager again afterwards gets no event loop, and every operation that needs one fails with
`UV_ECANCELED`.
-/
@[extern "lean_uv_event_loop_alive"]
opaque alive : BaseIO Bool

end Loop
end UV
end Internal
end Std
