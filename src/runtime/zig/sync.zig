// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const builtin = @import("builtin");
const std = @import("std");
const testing = std.testing;
const lean = @import("lean_object.zig");
const c = @cImport({
    @cInclude("pthread.h");
    @cInclude("sys/time.h");
});

fn checkPThread(comptime name: []const u8, rc: std.c.E) void {
    if (rc != .SUCCESS) {
        std.debug.panic("{s} failed with errno {}", .{ name, @intFromEnum(rc) });
    }
}

fn checkErrno(comptime name: []const u8, rc: c_int) void {
    if (rc != 0) {
        std.debug.panic("{s} failed with errno {}", .{ name, rc });
    }
}

fn wallClockNanos() u64 {
    var tv: c.timeval = undefined;
    checkErrno("gettimeofday", c.gettimeofday(&tv, null));
    return @as(u64, @intCast(tv.tv_sec)) * std.time.ns_per_s +
        @as(u64, @intCast(tv.tv_usec)) * std.time.ns_per_us;
}

pub const AtomicLeanPtr = struct {
    value: std.atomic.Value(usize),

    fn encode(ptr: ?*lean.lean_object) usize {
        return if (ptr) |value| @intFromPtr(value) else 0;
    }

    fn decode(bits: usize) ?*lean.lean_object {
        return if (bits == 0) null else @ptrFromInt(bits);
    }

    pub fn init(value: ?*lean.lean_object) AtomicLeanPtr {
        return .{ .value = std.atomic.Value(usize).init(encode(value)) };
    }

    pub fn load(self: *const AtomicLeanPtr, comptime order: std.builtin.AtomicOrder) ?*lean.lean_object {
        return decode(self.value.load(order));
    }

    pub fn store(self: *AtomicLeanPtr, value: ?*lean.lean_object, comptime order: std.builtin.AtomicOrder) void {
        self.value.store(encode(value), order);
    }

    pub fn cmpxchgStrong(self: *AtomicLeanPtr, expected: ?*lean.lean_object, desired: ?*lean.lean_object) ?*lean.lean_object {
        return if (self.value.cmpxchgStrong(encode(expected), encode(desired), .acq_rel, .acquire)) |current|
            decode(current)
        else
            null;
    }
};

pub fn atomicLeanPtr(slot: *?*anyopaque) *AtomicLeanPtr {
    return @ptrCast(@alignCast(slot));
}

pub const Mutex = struct {
    raw: std.c.pthread_mutex_t = std.c.PTHREAD_MUTEX_INITIALIZER,

    pub fn init() Mutex {
        return .{};
    }

    pub fn deinit(self: *Mutex) void {
        checkPThread("pthread_mutex_destroy", std.c.pthread_mutex_destroy(&self.raw));
    }

    pub fn lock(self: *Mutex) void {
        checkPThread("pthread_mutex_lock", std.c.pthread_mutex_lock(&self.raw));
    }

    pub fn unlock(self: *Mutex) void {
        checkPThread("pthread_mutex_unlock", std.c.pthread_mutex_unlock(&self.raw));
    }
};

pub const Condvar = struct {
    raw: std.c.pthread_cond_t = std.c.PTHREAD_COND_INITIALIZER,

    pub fn init() Condvar {
        return .{};
    }

    pub fn deinit(self: *Condvar) void {
        checkPThread("pthread_cond_destroy", std.c.pthread_cond_destroy(&self.raw));
    }

    pub fn wait(self: *Condvar, mutex: *Mutex) void {
        checkPThread("pthread_cond_wait", std.c.pthread_cond_wait(&self.raw, &mutex.raw));
    }

    pub fn signal(self: *Condvar) void {
        checkPThread("pthread_cond_signal", std.c.pthread_cond_signal(&self.raw));
    }

    pub fn broadcast(self: *Condvar) void {
        checkPThread("pthread_cond_broadcast", std.c.pthread_cond_broadcast(&self.raw));
    }
};

pub const Once = struct {
    raw: c.pthread_once_t = onceInitValue(),

    fn onceInitValue() c.pthread_once_t {
        return switch (builtin.os.tag) {
            .driverkit, .ios, .maccatalyst, .macos, .tvos, .visionos, .watchos => .{
                .__sig = 0x30B1BCBA,
                .__opaque = [_]u8{0} ** 8,
            },
            else => std.mem.zeroes(c.pthread_once_t),
        };
    }

    pub fn init() Once {
        return .{};
    }

    pub fn call(self: *Once, initializer: *const fn () callconv(.c) void) void {
        checkErrno("pthread_once", c.pthread_once(&self.raw, initializer));
    }
};

const ContentionState = struct {
    mutex: Mutex,
    condvar: Condvar,
    ready: bool = false,
    waiting: usize = 0,
    counter: usize = 0,
};

fn contentionWaiter(state: *ContentionState) void {
    state.mutex.lock();
    defer state.mutex.unlock();

    state.waiting += 1;
    while (!state.ready) {
        state.condvar.wait(&state.mutex);
    }
    state.counter += 1;
}

fn contentionBroadcaster(state: *ContentionState) void {
    while (true) {
        state.mutex.lock();
        if (state.waiting == 2) {
            state.ready = true;
            state.counter += 1;
            state.condvar.broadcast();
            state.mutex.unlock();
            return;
        }
        state.mutex.unlock();
        std.Thread.yield() catch {};
    }
}

test "mutex and condvar contention completes within one second" {
    var state = ContentionState{
        .mutex = Mutex.init(),
        .condvar = Condvar.init(),
    };
    defer state.condvar.deinit();
    defer state.mutex.deinit();

    const started = wallClockNanos();

    const waiter_a = try std.Thread.spawn(.{}, contentionWaiter, .{&state});
    const waiter_b = try std.Thread.spawn(.{}, contentionWaiter, .{&state});
    const broadcaster = try std.Thread.spawn(.{}, contentionBroadcaster, .{&state});

    waiter_a.join();
    waiter_b.join();
    broadcaster.join();

    const elapsed = wallClockNanos() - started;
    try testing.expect(elapsed < std.time.ns_per_s);
    try testing.expectEqual(@as(usize, 3), state.counter);
}

var g_once_counter = std.atomic.Value(usize).init(0);
var g_once_start = std.atomic.Value(bool).init(false);

fn onceInitializer() callconv(.c) void {
    _ = g_once_counter.fetchAdd(1, .acq_rel);
}

fn onceWorker(once: *Once) void {
    while (!g_once_start.load(.acquire)) {
        std.atomic.spinLoopHint();
    }
    once.call(&onceInitializer);
}

test "once runs initializer exactly once" {
    g_once_counter.store(0, .release);
    g_once_start.store(false, .release);

    var once = Once.init();
    var workers: [8]std.Thread = undefined;

    for (&workers) |*worker| {
        worker.* = try std.Thread.spawn(.{}, onceWorker, .{&once});
    }

    g_once_start.store(true, .release);
    for (workers) |worker| worker.join();

    try testing.expectEqual(@as(usize, 1), g_once_counter.load(.acquire));
}

const CasState = struct {
    slot: AtomicLeanPtr,
    next_index: std.atomic.Value(usize),
    objects: *[10_001]lean.lean_object,
    seen: *[10_001]u8,
};

fn casWorker(state: *CasState) void {
    while (true) {
        const index = state.next_index.fetchAdd(1, .acq_rel);
        if (index >= 10_000) return;

        const expected = &state.objects[index];
        const desired = &state.objects[index + 1];
        while (state.slot.cmpxchgStrong(expected, desired) != null) {
            std.atomic.spinLoopHint();
        }

        std.debug.assert(state.slot.load(.acquire) != null);
        state.seen[index + 1] = 1;
    }
}

test "atomic cmpxchgStrong uses acquire release ordering" {
    var objects: [10_001]lean.lean_object = undefined;
    for (&objects, 0..) |*object, index| {
        object.* = .{
            .m_rc = @intCast(index + 1),
            .m_cs_sz = 0,
            .m_other = 0,
            .m_tag = 0,
        };
    }

    var seen = [_]u8{0} ** 10_001;
    var state = CasState{
        .slot = AtomicLeanPtr.init(&objects[0]),
        .next_index = std.atomic.Value(usize).init(0),
        .objects = &objects,
        .seen = &seen,
    };

    var threads: [4]std.Thread = undefined;
    for (&threads) |*thread| {
        thread.* = try std.Thread.spawn(.{}, casWorker, .{&state});
    }
    for (threads) |thread| thread.join();

    try testing.expectEqual(@as(?*lean.lean_object, &objects[10_000]), state.slot.load(.acquire));
    for (seen[1..]) |value| {
        try testing.expectEqual(@as(u8, 1), value);
    }
}
