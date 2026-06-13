// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const builtin = @import("builtin");
const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const sync = @import("sync.zig");
const c = @cImport({
    @cInclude("pthread.h");
    @cInclude("unistd.h");
});
const libc = struct {
    extern "c" fn getenv(name: [*:0]const u8) ?[*:0]u8;
    extern "c" fn setenv(name: [*:0]const u8, value: [*:0]const u8, overwrite: c_int) c_int;
    extern "c" fn unsetenv(name: [*:0]const u8) c_int;
};

const delegated_runtime = struct {
    extern fn leanrt_cpp_partial_hidden_lean_initialize_thread() callconv(.c) void;
    extern fn leanrt_cpp_partial_hidden_lean_finalize_thread() callconv(.c) void;
};

threadlocal var g_thread_initialized = false;
var g_live_spawn_contexts = std.atomic.Value(usize).init(0);

pub const default_stack_size_kb: usize = 8192;
const min_stack_size_kb: usize = 64;
const max_stack_size_kb: usize = 65536;

pub const SpawnConfig = struct {
    stack_size: usize = 0,
    allocator: ?std.mem.Allocator = null,
    name: ?[]const u8 = null,
};

pub fn defaultStackSizeBytes() usize {
    return default_stack_size_kb * 1024;
}

fn warnInvalidStackSize(raw: []const u8) void {
    if (builtin.is_test) return;
    std.debug.print(
        "warning: ignoring invalid LEAN_STACK_SIZE_KB='{s}'; expected decimal KB in [{}, {}]\n",
        .{ raw, min_stack_size_kb, max_stack_size_kb },
    );
}

pub fn parseStackSizeKB(env: ?[]const u8) ?usize {
    const raw = env orelse return null;
    if (raw.len == 0) return null;

    const kb = std.fmt.parseUnsigned(usize, raw, 10) catch {
        warnInvalidStackSize(raw);
        return null;
    };
    if (kb < min_stack_size_kb or kb > max_stack_size_kb) {
        warnInvalidStackSize(raw);
        return null;
    }
    return kb * 1024;
}

pub fn stackSizeBytesFromEnv() ?usize {
    const raw = libc.getenv("LEAN_STACK_SIZE_KB") orelse return null;
    return parseStackSizeKB(std.mem.span(raw));
}

fn effectiveStackSize(requested: usize) usize {
    if (requested != 0) return requested;
    return stackSizeBytesFromEnv() orelse defaultStackSizeBytes();
}

pub fn resetTestState() void {
    g_thread_initialized = false;
    g_live_spawn_contexts.store(0, .release);
}

pub fn threadInitialized() bool {
    return g_thread_initialized;
}

pub fn initializeThreadSubsystems() void {
    if (g_thread_initialized) return;

    alloc.initializeThreadAllocator();
    if (!builtin.is_test) {
        delegated_runtime.leanrt_cpp_partial_hidden_lean_initialize_thread();
    }
    g_thread_initialized = true;
}

pub fn finalizeThreadSubsystems() void {
    if (!g_thread_initialized) return;

    alloc.finalizeThreadAllocator();
    if (!builtin.is_test) {
        delegated_runtime.leanrt_cpp_partial_hidden_lean_finalize_thread();
    }
    g_thread_initialized = false;
}

pub export fn lean_initialize_thread() callconv(.c) void {
    initializeThreadSubsystems();
}

pub export fn lean_finalize_thread() callconv(.c) void {
    finalizeThreadSubsystems();
}

fn setCurrentThreadName(name: [:0]const u8) void {
    if (builtin.os.tag == .macos) {
        const rc = c.pthread_setname_np(name.ptr);
        if (rc != 0) {
            std.debug.panic("pthread_setname_np failed with errno {}", .{rc});
        }
    }
}

fn invokeThreadFunction(comptime function: anytype, args: anytype) void {
    const return_type = @typeInfo(@TypeOf(function)).@"fn".return_type orelse @compileError("thread function must have a return type");
    switch (@typeInfo(return_type)) {
        .noreturn => @call(.auto, function, args),
        .error_union => _ = @call(.auto, function, args) catch |err| {
            std.debug.panic("spawned thread function failed: {}", .{err});
        },
        else => _ = @call(.auto, function, args),
    }
}

pub fn spawn(config: SpawnConfig, comptime function: anytype, args: anytype) std.Thread.SpawnError!std.Thread {
    const allocator = config.allocator orelse std.heap.c_allocator;
    const Context = struct {
        allocator: std.mem.Allocator,
        name: ?[:0]u8,
        args: @TypeOf(args),

        fn deinit(self: *@This()) void {
            defer _ = g_live_spawn_contexts.fetchSub(1, .acq_rel);
            const allocator_local = self.allocator;
            if (self.name) |name| allocator_local.free(name);
            allocator_local.destroy(self);
        }

        fn entry(self: *@This()) void {
            defer self.deinit();
            initializeThreadSubsystems();
            defer finalizeThreadSubsystems();
            if (self.name) |name| setCurrentThreadName(name);
            invokeThreadFunction(function, self.args);
        }
    };

    const ctx = try allocator.create(Context);
    errdefer allocator.destroy(ctx);

    const name = if (config.name) |thread_name| try allocator.dupeZ(u8, thread_name) else null;
    errdefer if (name) |owned_name| allocator.free(owned_name);

    _ = g_live_spawn_contexts.fetchAdd(1, .acq_rel);
    errdefer _ = g_live_spawn_contexts.fetchSub(1, .acq_rel);

    ctx.* = .{
        .allocator = allocator,
        .name = name,
        .args = args,
    };

    return std.Thread.spawn(.{
        .stack_size = effectiveStackSize(config.stack_size),
        .allocator = config.allocator,
    }, Context.entry, .{ctx});
}

const NameState = struct {
    mutex: sync.Mutex = .{},
    observed_name: [64]u8 = [_]u8{0} ** 64,
    name_status: c_int = 0,
    saw_initialized: bool = false,
};

fn copyZ(buf: []u8, src: [*:0]const u8) void {
    const len = std.mem.len(src);
    @memcpy(buf[0..len], src[0..len]);
    if (len < buf.len) buf[len] = 0;
}

fn nameWorker(state: *NameState) void {
    var buffer: [64]u8 = [_]u8{0} ** 64;
    state.mutex.lock();
    defer state.mutex.unlock();

    if (builtin.os.tag == .macos) {
        state.name_status = c.pthread_getname_np(c.pthread_self(), &buffer, buffer.len);
        if (state.name_status == 0) {
            copyZ(&state.observed_name, @ptrCast(&buffer));
        }
    }
    state.saw_initialized = threadInitialized();
}

test "spawn sets thread name on darwin and initializes thread state" {
    resetTestState();

    var state = NameState{};
    defer state.mutex.deinit();

    const thread_handle = try spawn(.{
        .name = "lean-worker-test",
        .stack_size = 256 * 1024,
    }, nameWorker, .{&state});
    thread_handle.join();

    try testing.expect(state.saw_initialized);
    if (builtin.os.tag == .macos) {
        try testing.expectEqual(@as(c_int, 0), state.name_status);
        try testing.expectEqualStrings("lean-worker-test", std.mem.sliceTo(&state.observed_name, 0));
    }
}

const StackState = struct {
    mutex: sync.Mutex = .{},
    observed_stack_size: usize = 0,
};

fn stackWorker(state: *StackState) void {
    state.mutex.lock();
    defer state.mutex.unlock();
    if (builtin.os.tag == .macos) {
        state.observed_stack_size = c.pthread_get_stacksize_np(c.pthread_self());
    }
}

test "spawn respects requested stack size on darwin" {
    if (builtin.os.tag != .macos) return error.SkipZigTest;

    const page_size = @as(usize, @intCast(c.getpagesize()));
    const requested_sizes = [_]usize{ 256 * 1024, 8 * 1024 * 1024 };
    for (requested_sizes) |requested| {
        var state = StackState{};
        defer state.mutex.deinit();

        const thread_handle = try spawn(.{ .stack_size = requested }, stackWorker, .{&state});
        thread_handle.join();

        try testing.expect(state.observed_stack_size + page_size >= requested);
        try testing.expect(state.observed_stack_size <= requested + page_size);
    }
}

fn noopWorker(counter: *std.atomic.Value(usize)) void {
    _ = counter.fetchAdd(1, .acq_rel);
}

test "spawn join remains usable over one thousand iterations" {
    resetTestState();
    var counter = std.atomic.Value(usize).init(0);
    var i: usize = 0;
    while (i < 1000) : (i += 1) {
        const thread_handle = try spawn(.{ .stack_size = 256 * 1024 }, noopWorker, .{&counter});
        thread_handle.join();
    }
    try testing.expectEqual(@as(usize, 1000), counter.load(.acquire));
    try testing.expectEqual(@as(usize, 0), g_live_spawn_contexts.load(.acquire));
}

const StackEnvSnapshot = struct {
    value: ?[:0]u8,
};

fn captureLeanStackSizeEnv() !StackEnvSnapshot {
    const current = libc.getenv("LEAN_STACK_SIZE_KB");
    if (current) |value| {
        return .{ .value = try testing.allocator.dupeZ(u8, std.mem.span(value)) };
    }
    return .{ .value = null };
}

fn restoreLeanStackSizeEnv(snapshot: StackEnvSnapshot) !void {
    defer if (snapshot.value) |value| testing.allocator.free(value);
    if (snapshot.value) |value| {
        if (libc.setenv("LEAN_STACK_SIZE_KB", value.ptr, 1) != 0) {
            return error.SetEnvFailed;
        }
    } else if (libc.unsetenv("LEAN_STACK_SIZE_KB") != 0) {
        return error.UnsetEnvFailed;
    }
}

test "parseStackSizeKB handles missing valid invalid and default cases" {
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB(null));
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB(""));
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB("0"));
    try testing.expectEqual(@as(?usize, 64 * 1024), parseStackSizeKB("64"));
    try testing.expectEqual(@as(?usize, 1024 * 1024), parseStackSizeKB("1024"));
    try testing.expectEqual(@as(?usize, 65536 * 1024), parseStackSizeKB("65536"));
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB("65537"));
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB("abc"));
    try testing.expectEqual(@as(?usize, null), parseStackSizeKB("12345678901234567890"));
    try testing.expectEqual(@as(usize, 8192 * 1024), defaultStackSizeBytes());
}

test "spawn uses LEAN_STACK_SIZE_KB when stack size is omitted" {
    if (builtin.os.tag != .macos) return error.SkipZigTest;

    const snapshot = try captureLeanStackSizeEnv();
    defer restoreLeanStackSizeEnv(snapshot) catch @panic("failed to restore LEAN_STACK_SIZE_KB");

    if (libc.setenv("LEAN_STACK_SIZE_KB", "512", 1) != 0) {
        return error.SetEnvFailed;
    }

    var state = StackState{};
    defer state.mutex.deinit();

    const page_size = @as(usize, @intCast(c.getpagesize()));
    const thread_handle = try spawn(.{}, stackWorker, .{&state});
    thread_handle.join();

    try testing.expect(state.observed_stack_size + page_size >= 512 * 1024);
    try testing.expect(state.observed_stack_size <= 512 * 1024 + page_size);
}
