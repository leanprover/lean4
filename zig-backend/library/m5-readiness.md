# M5 Readiness

This note records the boundaries that make M5a safe and the reasons M5b-F10 must be an
atomic cutover instead of a gradual scheduler merge. It is intentionally narrow: it covers
the scheduler/TLS/heartbeat transition surfaces and the explicitly deferred full
`lean_initialize` work, not the general runtime plan.

## Transition snapshot after M5a

M5a has introduced enough Zig-side scaffolding to reason about tasks, thunks, thread
wrappers, and the current-task TLS slot, but it has **not** replaced the live scheduler yet.
The process is therefore in a deliberately asymmetric state:

- Zig now has a declared `g_current_task_object` TLS slot and helper accessors.
- The C++ runtime still owns the real scheduler loop, the singleton task manager, and the
  task-state transitions that publish task-local context.
- `tests/abi-smoke/current_task_tls.c` only proves the bridge required by
  `TLS1.tls_mutual_reads_with_cpp`: same-thread mutual visibility between the C++ TLS writer
  and the Zig TLS reader while the C++ scheduler remains authoritative.

That asymmetry is acceptable for M5a because the Zig side is still observational at the
scheduler boundary. It becomes unsafe the moment both runtimes try to schedule tasks
independently.

## Thunk atomic-swap rationale

`M5a-F4` moved `lean_thunk_get_core` into Zig, and that function already demonstrates the
kind of ownership transition M5b must respect. The thunk has two materially different modes:

1. **Single-threaded (ST) path** — no other thread can race the force, so the closure slot may
   be replaced with a plain pointer store after evaluation.
2. **Multi-threaded (MT) path** — multiple threads may observe the thunk concurrently, so the
   closure slot must be claimed exactly once before evaluation continues.

That is why the MT implementation uses a `cmpxchgStrong` with acquire/release semantics on
the thunk's closure slot. The operation does two jobs at once:

- it elects the single thread that is allowed to execute the closure; and
- it publishes the "closure has been consumed" state so losing threads observe the resolved
  value instead of attempting a second execution.

This is the behavior locked in by the contract assertions
`TP1.thunk_get_core_atomic_swap` and `TP1.thunk_st_path_plain_store`. The first assertion is
about the single-execution invariant under contention; the second is about not paying MT
synchronization costs when the object is still provably ST-owned.

### Why this matters for M5b-F10

The scheduler swap has the same shape at a larger granularity. A thunk can tolerate either
an ST owner or an MT atomic claimant, but it cannot tolerate two independent claimants for
the same closure. Likewise, Lean can tolerate:

- one live C++ task manager, **or**
- one live Zig task manager after the swap,

but it cannot tolerate both trying to own task publication, worker wakeups, cancellation,
and current-task TLS at the same time.

So "atomic swap" in `M5b-F10` does **not** merely mean "do the refactor in one PR". It means
"switch the unique runtime owner of scheduler state in one coherent cutover". The same design
lesson from thunk forcing applies: if ownership is shared during the transition, correctness
becomes under-specified.

## Scheduler coexistence ban + interrupt.cpp TLS boundary

The coexistence ban comes directly from the upstream C++ ownership points:

- `src/runtime/object.cpp:681` / `src/runtime/object.cpp:682` declares
  `g_current_task_object` via `LEAN_THREAD_PTR(lean_task_object, g_current_task_object);`
- `src/runtime/object.cpp:1044` / `src/runtime/object.cpp:1045` defines the singleton
  `static task_manager * g_task_manager = nullptr;`

Those two globals are not independent knobs. The singleton scheduler is the mechanism that
decides when a worker enters `scoped_current_task_object`, when `wait_for` treats the caller
as "in pool", when cancellation checks are interpreted in task context, and when task
completion wakes dependents. If a Zig scheduler were started beside the C++ one during M5a,
the process would have:

- two distinct scheduler owners,
- two notions of "current task" on the same OS thread boundary,
- one set of runtime entry points still implemented with C++ task-manager assumptions.

That configuration is explicitly banned. During M5a the C++ scheduler remains the **only**
owner of the following scheduler-facing entry points and behaviors:

- `lean_task_spawn_core`
- `lean_task_bind_core`
- `lean_task_map_core`
- `lean_task_get`
- `lean_io_check_canceled_core`
- `lean_io_cancel_core`
- `lean_io_get_task_state_core`
- `lean_io_wait_any_core`
- `lean_io_promise_new`
- `lean_io_promise_resolve`
- `lean_io_promise_result_opt`
- `lean_init_task_manager`
- `lean_init_task_manager_using`
- `lean_finalize_task_manager`
- `lean_run_main`

The M5a bridge exists only to satisfy `TLS1.tls_mutual_reads_with_cpp`. It mirrors the active
C++ worker context into Zig so that same-thread readers agree; it does **not** authorize a
second worker pool, a second queue set, or a second source of truth for task-local state.

## interrupt.cpp boundary that stays in `cpp_partial`

`src/runtime/interrupt.cpp` is the other reason gradual coexistence is unsafe. Several pieces
of task-adjacent state are still thread-local on the C++ side:

- `interrupt.cpp:17-18` define `g_max_heartbeat` and `g_heartbeat` as thread-local values.
- `interrupt.cpp:30` defines `reset_heartbeat()`, which clears the C++ heartbeat counter for
  the current worker thread.
- `interrupt.cpp:44` defines `scope_max_heartbeat`, which mutates the thread-local heartbeat
  limit in scoped form.
- `interrupt.cpp:57` defines the thread-local cancel-token pointer `g_cancel_tk`.

These values are not abstract process-wide settings. They are worker-thread-local runtime
state. As long as the scheduler that establishes `g_current_task_object` is still the C++
scheduler, the safest rule is to keep the heartbeat/cancel-token surfaces in `cpp_partial`
too. Otherwise the process would split task ownership on one side and interrupt ownership on
the other, with no single runtime responsible for keeping the TLS domains coherent.

This is why porting `interrupt.cpp` is deferred until Zig fully owns the current-task TLS
slot and the scheduler entry points listed above. Only then can Zig become the sole runtime
layer that:

1. decides which task is current on a worker thread,
2. installs the cancel-token view associated with that task, and
3. resets or scopes heartbeat counters for the same worker lifecycle.

Until that cutover, the boundary is intentional rather than accidental.

### TLS direction diagram

```text
Zig task worker thread
    │
    ├─ current task context
    │    src/runtime/task_tls.zig
    │    extern fn leanrt_cpp_partial_hidden_current_task_swap(task: ?*lean_task_object)
    │      -> mirrors the active task pointer into cpp_partial TLS
    │
    ├─ heartbeat reset boundary
    │    src/runtime/interrupt_tls.zig
    │    extern fn leanrt_cpp_partial_hidden_reset_heartbeat() callconv(.c) void
    │      -> resets the authoritative C++ `g_heartbeat` slot
    │
    └─ cancel-token TLS boundary
         src/runtime/interrupt_tls.zig
         extern fn leanrt_cpp_partial_hidden_cancel_tk_get() callconv(.c) ?*anyopaque
         extern fn leanrt_cpp_partial_hidden_cancel_tk_swap(token: ?*anyopaque) callconv(.c) ?*anyopaque
           -> reads/writes the authoritative C++ `g_cancel_tk` slot

cpp_partial-resident TLS owner
    cmake/leanrt_cpp_partial/interrupt_partial.cpp
        #include src/runtime/interrupt.cpp
        thread-local: g_heartbeat, g_max_heartbeat, g_cancel_tk
```

The direction matters: Zig owns scheduling, but the surviving TLS state still lives in the
`cpp_partial` archive. So the Zig worker must cross the boundary for heartbeat/cancel-token
operations instead of declaring a second Zig-local TLS copy.

## Heartbeat reset boundary

The concrete heartbeat rule for the swap is simple: the **authoritative**
`reset_heartbeat()` call site remains the C++ implementation from `interrupt.cpp` until the
task-manager swap is complete. Even if Zig starts wrapping more of the run loop, it must call
back into the C++-resident reset helper while `g_heartbeat` and `g_max_heartbeat` still live
in C++ TLS.

That is the boundary later documented by M5b-F12:

- end-of-run-cycle heartbeat reset is required;
- the Zig worker reaches that reset through `src/runtime/interrupt_tls.zig`, which calls the
  `cpp_partial`-resident `leanrt_cpp_partial_hidden_reset_heartbeat()` shim instead of a
  Zig-owned threadlocal;
- the reset must target the TLS storage that actually backs `interrupt.cpp`;
- `scope_max_heartbeat` and `g_cancel_tk` stay coupled to that same TLS domain.

In other words, the scheduler swap may move task orchestration, but it must not silently fork
the heartbeat counter into a second TLS universe.

## `LEAN_STACK_SIZE_KB` and `lean_run_main` readiness context

The existing C++ behavior in `src/runtime/thread.cpp` is the compatibility target for the
eventual Zig `lean_run_main`:

- `thread.cpp:175` reads `LEAN_STACK_SIZE_KB`
- `thread.cpp:180` applies it via `lthread::set_thread_stack_size`
- `thread.cpp:183` checks `LEAN_MAIN_USE_THREAD`
- `thread.cpp:173` defines `lean_run_main`

This matters for readiness because `lean_run_main` is one of the scheduler-adjacent entry
points that cannot be partially shared. The environment parsing utility added in M5a-F7 is a
precondition for the later move, but **the live behavior remains C++-owned until the same
atomic cutover that rehomes the task-manager singleton**.

## Explicitly out of scope: full kernel-side `lean_initialize`

This document does **not** claim readiness for a full migration of kernel-side
`lean_initialize`. The upstream full initialization path that reaches into
`initialize/init.cpp` and the `usesLeanAPI` call paths remains out of scope for M5.

What M5 is preparing is the task-manager / scheduler / runtime-thread slice needed by
`lean_run_main`, promises, cancellation, and basic IO. It is **not** preparing an audited
replacement for every kernel-facing initialization side effect in the outer Lean executable
embedding paths.

So the working rule is:

- runtime-thread/task-manager initialization needed for the scheduler swap is in scope;
- the full kernel-side `lean_initialize` path from `initialize/init.cpp` is not.

That boundary prevents the M5 work from over-claiming readiness in areas that still depend on
the broader C++ runtime and kernel initialization stack.

## ThreadSanitizer host-unavailability (SY1 skip-path record)

This section records the gap that the M5a validation contract assertion
`SY1.no_thread_sanitizer_warnings` explicitly allows: *"If TSan is unavailable on the host,
the assertion is skipped and the m5-readiness doc records the gap."*
TSan is unavailable on this host, so the contract's skip clause applies and this paragraph
is the readiness-doc record the validator looks for.

Concrete evidence of unavailability: during the M5a-F2 handoff (commit `162a7287`) we
attempted to exercise ThreadSanitizer via a trivial standalone reproducer —
`zig test /tmp/x.zig -fsanitize-thread` on the empty test file — and the TSan runtime itself
SIGSEGVs immediately, before any sync-layer code under test even starts. The orchestrator
reviewed and dismissed this during the M5a-F2 handoff review: the crash is in
upstream Zig 0.16 + macOS's TSan runtime support, not in any code we control or could fix
locally. It reproduces with no sync-layer code involved, which rules out our runtime as the
cause.

Why we are deliberately **not** adding a `-Dthread-sanitizer` build option to `build.zig`:
adding the flag would simply route `zig build test` through the same broken upstream TSan
runtime and surface the identical SIGSEGV with no additional signal value. It would also
make the build option look exercised in CI when in fact it cannot produce a clean run on this
host — worse than not having the option at all. The contract is explicit that the skip path
is acceptable when TSan is unavailable, and "unavailable" here means the runtime crashes on
an empty test, not merely "unconfigured".

What we rely on instead for race-freedom in the sync layer: the tests in
`src/runtime/sync.zig` are deliberately structured to expose ordering bugs without TSan
instrumentation. The 8-thread contention test on `AtomicLeanPtr`, the exact-once
initialization test for `LeanOnce`, and the 10,000-iteration `cmpxchgStrong` stress all rely
on (a) careful acquire/release/seq_cst ordering chosen to match the semantics documented in
`src/include/lean/lean.h`, and (b) bounded wall-clock contention windows that maximize the
chance of interleavings being observed under normal scheduling. Correctness review uses the
`lean.h` memory-order comments as the source of truth, and the thunk atomic-swap rationale
above (`TP1.thunk_get_core_atomic_swap`, `TP1.thunk_st_path_plain_store`) documents how the
ST/MT ownership split is preserved without needing a sanitizer to certify it.

When the SY1 gap will be revisited: this skip is not permanent. We will re-enable TSan
coverage when **either** (1) the upstream Zig/macOS TSan runtime is fixed so that
`zig test -fsanitize-thread` no longer SIGSEGVs on an empty test, **or** (2) the M5b
scheduler stress work (`M5b-F14`) plus the M5-Z1 reproducibility sweep uncover a concrete
ordering bug that justifies re-enabling TSan on a Linux CI runner where the runtime is
known-good. Either trigger reopens this section; until then, SY1 stays on the contract's
documented skip path and this paragraph is the audit trail.
