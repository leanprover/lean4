# M5b TLS boundary

M5b keeps the interrupt/heartbeat TLS state in `libleanrt_cpp_partial.a` even after the Zig
task manager takes over scheduling. The retained C++ source is
`cmake/leanrt_cpp_partial/interrupt_partial.cpp`, which includes
`/Users/davirian/dev/active/lean4/src/runtime/interrupt.cpp` so the authoritative thread-local
slots stay in one place:

- `g_heartbeat`
- `g_max_heartbeat`
- `g_cancel_tk`

## Zig → cpp_partial boundary

```text
src/runtime/task_tls.zig
  extern fn leanrt_cpp_partial_hidden_current_task_swap(
      task: ?*lean_task_object,
  ) callconv(.c) ?*lean_task_object

src/runtime/interrupt_tls.zig
  extern fn leanrt_cpp_partial_hidden_reset_heartbeat() callconv(.c) void
  extern fn leanrt_cpp_partial_hidden_cancel_tk_get() callconv(.c) ?*anyopaque
  extern fn leanrt_cpp_partial_hidden_cancel_tk_swap(
      token: ?*anyopaque,
  ) callconv(.c) ?*anyopaque
```

Directionally:

```text
Zig worker/task manager
    ├─ owns scheduling + task execution
    ├─ mirrors current-task TLS through `leanrt_cpp_partial_hidden_current_task_swap`
    ├─ resets heartbeats through `leanrt_cpp_partial_hidden_reset_heartbeat()`
    └─ reads/writes cancel-token TLS through `leanrt_cpp_partial_hidden_cancel_tk_*`

cpp_partial / interrupt.cpp
    └─ owns the actual interrupt-side TLS storage (`g_heartbeat`, `g_max_heartbeat`, `g_cancel_tk`)

cpp_partial / object_partial.cpp
    └─ keeps the mirrored C++ `g_current_task_object` slot in sync with Zig's `task_tls.zig`
```

## Why `reset_heartbeat()` must cross the boundary

`src/runtime/object.cpp:815` and `:839` reset the C++ heartbeat TLS around task execution. The
Zig scheduler mirrors that by calling the `cpp_partial`-resident
`leanrt_cpp_partial_hidden_reset_heartbeat()` shim from `src/runtime/interrupt_tls.zig`; it
does **not** declare a second Zig `threadlocal` heartbeat counter for scheduler control flow.

That keeps the surviving interrupt/tactic glue on the same TLS domain that still powers
`scope_max_heartbeat` and `g_cancel_tk`.
