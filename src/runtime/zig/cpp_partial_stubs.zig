// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

// Weak stubs for C++ runtime functions the Zig runtime still references
// during the transition to a self-contained Zig backend. These symbols are
// overridden when the C++ Lean runtime is linked, and provide no-op fallbacks
// when linking only the Zig runtime.

const std = @import("std");

export fn leanrt_cpp_partial_hidden_current_task_swap(task: ?*anyopaque) callconv(.c) ?*anyopaque {
    return task;
}

export fn leanrt_cpp_partial_hidden_lean_finalize_thread() callconv(.c) void {}

export fn leanrt_cpp_partial_hidden_lean_free_object_impl(o: *anyopaque) callconv(.c) void {
    std.c.free(o);
}

export fn leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl() callconv(.c) void {}

export fn leanrt_cpp_partial_hidden_lean_initialize_runtime_module() callconv(.c) void {}

export fn leanrt_cpp_partial_hidden_lean_initialize_thread() callconv(.c) void {}

export fn leanrt_cpp_partial_hidden_lean_setup_args(argc: c_int, argv: [*c][*c]u8) callconv(.c) [*c][*c]u8 {
    _ = argc;
    return argv;
}

export fn leanrt_cpp_partial_hidden_reset_heartbeat() callconv(.c) void {}

export fn leanrt_cpp_partial_hidden_cancel_tk_get() callconv(.c) ?*anyopaque {
    return null;
}

export fn leanrt_cpp_partial_hidden_cancel_tk_swap(token: ?*anyopaque) callconv(.c) ?*anyopaque {
    return token;
}
