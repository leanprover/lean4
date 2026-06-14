const std = @import("std");

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
threadlocal var g_cancel_token: ?*anyopaque = null;

fn resetHeartbeatAt(boundary: HeartbeatBoundary) void {
    const before = g_heartbeat_probe;
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
    g_heartbeat_probe += iterations;
}

pub fn resetHeartbeatBoundaryState() void {
    g_heartbeat_boundary_state.reset();
    g_heartbeat_probe = 0;
}

pub fn heartbeatBoundarySnapshot() HeartbeatBoundarySnapshot {
    return g_heartbeat_boundary_state.snapshot();
}

pub fn currentCancelToken() ?*anyopaque {
    return g_cancel_token;
}

pub fn swapCancelToken(token: ?*anyopaque) ?*anyopaque {
    const prev = g_cancel_token;
    g_cancel_token = token;
    return prev;
}
