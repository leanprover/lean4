const builtin = @import("builtin");
const std = @import("std");

const cpp_partial = if (builtin.is_test)
    struct {
        fn leanrt_cpp_partial_hidden_reset_heartbeat() callconv(.c) void {}

        fn leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl() callconv(.c) void {}

        fn leanrt_cpp_partial_hidden_cancel_tk_get() callconv(.c) ?*anyopaque {
            return null;
        }

        fn leanrt_cpp_partial_hidden_cancel_tk_swap(token: ?*anyopaque) callconv(.c) ?*anyopaque {
            return token;
        }
    }
else
    struct {
        extern fn leanrt_cpp_partial_hidden_reset_heartbeat() callconv(.c) void;
        extern fn leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl() callconv(.c) void;
        extern fn leanrt_cpp_partial_hidden_cancel_tk_get() callconv(.c) ?*anyopaque;
        extern fn leanrt_cpp_partial_hidden_cancel_tk_swap(token: ?*anyopaque) callconv(.c) ?*anyopaque;
    };

pub const HeartbeatBoundarySnapshot = extern struct {
    pre_spawn_before_reset: usize,
    pre_spawn: usize,
    post_spawn_before_reset: usize,
    post_spawn: usize,
    post_run_before_reset: usize,
    post_run: usize,
};

const HeartbeatBoundary = enum {
    pre_spawn,
    post_spawn,
    post_run,
};

const HeartbeatBoundaryState = struct {
    pre_spawn_before_reset: std.atomic.Value(usize) = .init(0),
    pre_spawn: std.atomic.Value(usize) = .init(0),
    post_spawn_before_reset: std.atomic.Value(usize) = .init(0),
    post_spawn: std.atomic.Value(usize) = .init(0),
    post_run_before_reset: std.atomic.Value(usize) = .init(0),
    post_run: std.atomic.Value(usize) = .init(0),

    fn reset(self: *HeartbeatBoundaryState) void {
        self.pre_spawn_before_reset.store(0, .seq_cst);
        self.pre_spawn.store(0, .seq_cst);
        self.post_spawn_before_reset.store(0, .seq_cst);
        self.post_spawn.store(0, .seq_cst);
        self.post_run_before_reset.store(0, .seq_cst);
        self.post_run.store(0, .seq_cst);
    }

    fn record(self: *HeartbeatBoundaryState, boundary: HeartbeatBoundary, before: usize) void {
        switch (boundary) {
            .pre_spawn => {
                self.pre_spawn_before_reset.store(before, .seq_cst);
                self.pre_spawn.store(0, .seq_cst);
            },
            .post_spawn => {
                self.post_spawn_before_reset.store(before, .seq_cst);
                self.post_spawn.store(0, .seq_cst);
            },
            .post_run => {
                self.post_run_before_reset.store(before, .seq_cst);
                self.post_run.store(0, .seq_cst);
            },
        }
    }

    fn snapshot(self: *const HeartbeatBoundaryState) HeartbeatBoundarySnapshot {
        return .{
            .pre_spawn_before_reset = self.pre_spawn_before_reset.load(.seq_cst),
            .pre_spawn = self.pre_spawn.load(.seq_cst),
            .post_spawn_before_reset = self.post_spawn_before_reset.load(.seq_cst),
            .post_spawn = self.post_spawn.load(.seq_cst),
            .post_run_before_reset = self.post_run_before_reset.load(.seq_cst),
            .post_run = self.post_run.load(.seq_cst),
        };
    }
};

var g_heartbeat_boundary_state = HeartbeatBoundaryState{};
threadlocal var g_heartbeat_probe: usize = 0;

fn resetHeartbeatAt(boundary: HeartbeatBoundary) void {
    const before = g_heartbeat_probe;
    if (!builtin.is_test) {
        cpp_partial.leanrt_cpp_partial_hidden_reset_heartbeat();
    }
    g_heartbeat_probe = 0;
    g_heartbeat_boundary_state.record(boundary, before);
}

pub fn resetHeartbeatBeforeSpawn() void {
    resetHeartbeatAt(.pre_spawn);
}

pub fn resetHeartbeatAfterSpawn() void {
    resetHeartbeatAt(.post_spawn);
}

pub fn resetHeartbeatAfterWorkerRun() void {
    resetHeartbeatAt(.post_run);
}

pub fn noteHeartbeatPulseForTest(iterations: usize) void {
    for (0..iterations) |_| {
        if (!builtin.is_test) {
            cpp_partial.leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl();
        }
        g_heartbeat_probe += 1;
    }
}

pub fn resetHeartbeatBoundaryState() void {
    g_heartbeat_boundary_state.reset();
    g_heartbeat_probe = 0;
}

pub fn heartbeatBoundarySnapshot() HeartbeatBoundarySnapshot {
    return g_heartbeat_boundary_state.snapshot();
}

pub fn currentCancelToken() ?*anyopaque {
    return cpp_partial.leanrt_cpp_partial_hidden_cancel_tk_get();
}

pub fn swapCancelToken(token: ?*anyopaque) ?*anyopaque {
    return cpp_partial.leanrt_cpp_partial_hidden_cancel_tk_swap(token);
}
