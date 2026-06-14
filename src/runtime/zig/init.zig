const std = @import("std");
const testing = std.testing;
const builtin = @import("builtin");
const c = @cImport({
    @cInclude("pthread.h");
    @cInclude("unistd.h");
});
const alloc = @import("alloc.zig");
const io_errno = @import("io_errno.zig");
const io_min = @import("io_min.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const task_manager = @import("task_manager.zig");
const thread = @import("thread.zig");
const runtime_options = @import("runtime_options");

const export_allocator_symbols = runtime_options.export_allocator_symbols;
const libc = struct {
    extern "c" fn getenv(name: [*:0]const u8) ?[*:0]u8;
    extern "c" fn setenv(name: [*:0]const u8, value: [*:0]const u8, overwrite: c_int) c_int;
    extern "c" fn unsetenv(name: [*:0]const u8) c_int;
};
const MainFn = *const fn (argc: c_int, argv: [*c][*c]u8) callconv(.c) ?*anyopaque;
const RunMainContext = struct {
    main_fn: MainFn,
    argc: c_int,
    argv: [*c][*c]u8,
    result: ?*anyopaque = null,
};

var g_runtime_initialized = false;
var g_initializing = true;
var g_task_manager_initialized = false;

fn initializeRcSubsystem() void {}

pub fn resetTestState() void {
    g_runtime_initialized = false;
    g_initializing = true;
    g_task_manager_initialized = false;
    task_manager.destroyRuntimeManager();
    alloc.initializeThreadAllocator();
    thread.resetTestState();
}

pub fn runtimeInitialized() bool {
    return g_runtime_initialized;
}

pub fn threadInitialized() bool {
    return thread.threadInitialized();
}

pub fn isInitializing() bool {
    return g_initializing;
}

pub fn markEndInitialization() void {
    g_initializing = false;
}

pub fn initializeRuntimeSubsystems() void {
    if (g_runtime_initialized) return;
    if (export_allocator_symbols) {
        alloc.initializeRuntimeAllocator();
        initializeRcSubsystem();
        io_errno.initializeDecodeCache();
    }
    g_runtime_initialized = true;
    g_initializing = true;
}

pub fn initializeThreadSubsystems() void {
    if (!g_runtime_initialized) initializeRuntimeSubsystems();
    thread.initializeThreadSubsystems();
}

pub fn finalizeThreadSubsystems() void {
    thread.finalizeThreadSubsystems();
}

pub fn lean_notify_assert(file_name: [*c]const u8, line: c_int, condition: [*c]const u8) callconv(.c) void {
    std.debug.print(
        "LEAN ASSERTION VIOLATION\nFile: {s}\nLine: {}\nCondition: {s}\n",
        .{ file_name, line, condition },
    );
    std.process.abort();
}

fn panicTaskManagerAlreadyInitialized() noreturn {
    io_min.lean_panic(
        "lean task manager already initialized; call lean_finalize_task_manager() before re-initializing",
        false,
    );
    unreachable;
}

pub export fn lean_init_task_manager() callconv(.c) void {
    lean_init_task_manager_using(task_manager.maxStdWorkersFromEnv());
}

pub export fn lean_init_task_manager_using(num_workers: c_uint) callconv(.c) void {
    if (g_task_manager_initialized) {
        panicTaskManagerAlreadyInitialized();
    }
    if (!task_manager.createRuntimeManager(num_workers)) {
        @panic("failed to initialize lean task manager");
    }
    g_task_manager_initialized = true;
}

pub export fn lean_finalize_task_manager() callconv(.c) void {
    task_manager.destroyRuntimeManager();
    g_task_manager_initialized = false;
}

fn leanMainUseThreadDisabled() bool {
    const raw = libc.getenv("LEAN_MAIN_USE_THREAD") orelse return false;
    return std.mem.eql(u8, std.mem.span(raw), "0");
}

fn runMainStackSizeBytes() ?usize {
    const size_bytes = thread.stackSizeBytesFromEnv() orelse return null;
    const rounded = size_bytes / (4 * 1024) * (4 * 1024);
    if (rounded == 0) return null;
    return rounded;
}

fn runMainWorker(context: *RunMainContext) void {
    context.result = context.main_fn(context.argc, context.argv);
}

pub export fn lean_run_main(main_fn: MainFn, argc: c_int, argv: [*c][*c]u8) callconv(.c) ?*anyopaque {
    if (leanMainUseThreadDisabled()) {
        return main_fn(argc, argv);
    }

    var context = RunMainContext{
        .main_fn = main_fn,
        .argc = argc,
        .argv = argv,
    };
    const worker = thread.spawn(.{
        .stack_size = runMainStackSizeBytes() orelse 0,
    }, runMainWorker, .{&context}) catch |err| {
        std.debug.panic("failed to spawn lean_run_main worker thread: {}", .{err});
    };
    worker.join();
    return context.result;
}

pub export fn lean_initialize_runtime_module() callconv(.c) void {
    initializeRuntimeSubsystems();
}

pub export fn lean_initialize() callconv(.c) void {
    initializeRuntimeSubsystems();
    initializeThreadSubsystems();
}

pub export fn lean_setup_args(argc: c_int, argv: [*c][*c]u8) callconv(.c) [*c][*c]u8 {
    _ = argc;
    return argv;
}

test "runtime module and thread initialization enable allocation" {
    resetTestState();
    lean_initialize_runtime_module();
    try testing.expect(runtimeInitialized());
    try testing.expect(isInitializing());

    initializeThreadSubsystems();
    try testing.expect(threadInitialized());

    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_object));
    try testing.expect(@intFromPtr(ptr) != 0);
    alloc.lean_free_object(ptr);
}

test "lean_initialize initializes runtime and thread" {
    resetTestState();
    lean_initialize();
    try testing.expect(runtimeInitialized());
    try testing.expect(threadInitialized());
}

test "lean_finalize_thread clears thread-local initialization state" {
    resetTestState();
    lean_initialize_runtime_module();
    initializeThreadSubsystems();
    finalizeThreadSubsystems();
    try testing.expect(!threadInitialized());
}

test "lean_setup_args returns argv unchanged" {
    var argv = [_][*:0]u8{
        @constCast("lean"),
        @constCast("--version"),
    };
    const result = lean_setup_args(2, @ptrCast(&argv));
    try testing.expectEqual(@intFromPtr(&argv[0]), @intFromPtr(result));
    try testing.expectEqual(@as(u8, 'l'), @as([*]u8, @ptrCast(result[0]))[0]);
    try testing.expectEqual(@as(u8, '-'), @as([*]u8, @ptrCast(result[1]))[0]);
}

test "lean_init_task_manager_using activates the runtime manager with the requested worker count" {
    resetTestState();
    lean_init_task_manager_using(3);
    defer lean_finalize_task_manager();

    try testing.expect(task_manager.runtimeManager() != null);
    const manager = task_manager.runtimeManager().?;
    const snapshot = manager.snapshot();
    try testing.expectEqual(@as(c_uint, 3), snapshot.max_std_workers);
}

test "lean_finalize_task_manager clears runtime manager state and allows reinitialization" {
    resetTestState();
    lean_init_task_manager_using(1);
    lean_finalize_task_manager();
    try testing.expect(task_manager.runtimeManager() == null);

    lean_init_task_manager_using(2);
    defer lean_finalize_task_manager();

    try testing.expect(task_manager.runtimeManager() != null);
    const manager = task_manager.runtimeManager().?;
    const snapshot = manager.snapshot();
    try testing.expectEqual(@as(c_uint, 2), snapshot.max_std_workers);
}

test "lean_init_task_manager_using zero keeps the runtime manager disabled until finalize" {
    resetTestState();
    lean_init_task_manager_using(0);
    try testing.expect(task_manager.runtimeManager() == null);
    lean_finalize_task_manager();
    try testing.expect(task_manager.runtimeManager() == null);
}

const RunMainEnvSnapshot = struct {
    main_use_thread: ?[:0]u8,
    stack_size_kb: ?[:0]u8,

    fn capture() !RunMainEnvSnapshot {
        return .{
            .main_use_thread = try duplicateEnvVar("LEAN_MAIN_USE_THREAD"),
            .stack_size_kb = try duplicateEnvVar("LEAN_STACK_SIZE_KB"),
        };
    }

    fn restore(self: RunMainEnvSnapshot) !void {
        defer {
            if (self.main_use_thread) |value| testing.allocator.free(value);
            if (self.stack_size_kb) |value| testing.allocator.free(value);
        }

        try restoreEnvVar("LEAN_MAIN_USE_THREAD", self.main_use_thread);
        try restoreEnvVar("LEAN_STACK_SIZE_KB", self.stack_size_kb);
    }
};

fn duplicateEnvVar(name: [*:0]const u8) !?[:0]u8 {
    const current = libc.getenv(name) orelse return null;
    return try testing.allocator.dupeZ(u8, std.mem.span(current));
}

fn restoreEnvVar(name: [*:0]const u8, value: ?[:0]u8) !void {
    if (value) |owned| {
        if (libc.setenv(name, owned.ptr, 1) != 0) {
            return error.SetEnvFailed;
        }
        return;
    }
    if (libc.unsetenv(name) != 0) {
        return error.UnsetEnvFailed;
    }
}

const RunMainThreadProbe = struct {
    caller_tid: c.pthread_t,
    observed_tid: c.pthread_t = undefined,
    observed_stack_size: usize = 0,
    observed_argc: c_int = 0,
};

var g_run_main_thread_probe: ?*RunMainThreadProbe = null;

fn runMainProbeOk(argc: c_int, _argv: [*c][*c]u8) callconv(.c) ?*anyopaque {
    _ = _argv;
    const probe = g_run_main_thread_probe orelse @panic("missing lean_run_main test probe");
    probe.observed_tid = c.pthread_self();
    if (builtin.os.tag == .macos) {
        probe.observed_stack_size = c.pthread_get_stacksize_np(c.pthread_self());
    }
    probe.observed_argc = argc;
    return io_min.lean_io_result_mk_ok(object.lean_box(17));
}

fn runMainProbeError(_argc: c_int, _argv: [*c][*c]u8) callconv(.c) ?*anyopaque {
    _ = _argc;
    _ = _argv;
    return io_min.lean_io_result_mk_error(object.lean_box(23));
}

fn expectResultTag(result: *anyopaque, expected_ok: bool, expected_payload: usize) !void {
    if (expected_ok) {
        try testing.expect(io_min.lean_io_result_is_ok(result));
        try testing.expectEqual(object.lean_box(expected_payload), io_min.lean_io_result_get_value(result));
        return;
    }
    try testing.expect(io_min.lean_io_result_is_error(result));
    try testing.expectEqual(object.lean_box(expected_payload), io_min.lean_io_result_get_error(result));
}

test "lean_run_main spawns a worker thread by default and propagates the IO result" {
    resetTestState();
    lean_initialize();

    const env = try RunMainEnvSnapshot.capture();
    defer env.restore() catch @panic("failed to restore lean_run_main environment");
    _ = libc.unsetenv("LEAN_MAIN_USE_THREAD");
    _ = libc.unsetenv("LEAN_STACK_SIZE_KB");

    var argv = [_][*:0]u8{ @constCast("lean"), @constCast("--threaded") };
    var probe = RunMainThreadProbe{ .caller_tid = c.pthread_self() };
    g_run_main_thread_probe = &probe;
    defer g_run_main_thread_probe = null;

    const result = lean_run_main(runMainProbeOk, 2, @ptrCast(&argv)) orelse @panic("lean_run_main returned null");
    defer alloc.lean_free_object(result);

    try expectResultTag(result, true, 17);
    try testing.expectEqual(@as(c_int, 0), c.pthread_equal(probe.caller_tid, probe.observed_tid));
    try testing.expectEqual(@as(c_int, 2), probe.observed_argc);
}

test "lean_run_main honors LEAN_MAIN_USE_THREAD=0 and returns error results unchanged" {
    resetTestState();
    lean_initialize();

    const env = try RunMainEnvSnapshot.capture();
    defer env.restore() catch @panic("failed to restore lean_run_main environment");
    try testing.expectEqual(@as(c_int, 0), libc.setenv("LEAN_MAIN_USE_THREAD", "0", 1));
    _ = libc.unsetenv("LEAN_STACK_SIZE_KB");

    var argv = [_][*:0]u8{ @constCast("lean"), @constCast("--inline") };
    var probe = RunMainThreadProbe{ .caller_tid = c.pthread_self() };
    g_run_main_thread_probe = &probe;
    defer g_run_main_thread_probe = null;

    const ok_result = lean_run_main(runMainProbeOk, 2, @ptrCast(&argv)) orelse @panic("lean_run_main returned null");
    defer alloc.lean_free_object(ok_result);
    try expectResultTag(ok_result, true, 17);
    try testing.expectEqual(@as(c_int, 1), c.pthread_equal(probe.caller_tid, probe.observed_tid));

    const err_result = lean_run_main(runMainProbeError, 0, null) orelse @panic("lean_run_main returned null");
    defer alloc.lean_free_object(err_result);
    try expectResultTag(err_result, false, 23);
}

test "lean_run_main rounds LEAN_STACK_SIZE_KB for its worker thread and keeps the default when unset" {
    if (builtin.os.tag != .macos) return error.SkipZigTest;

    resetTestState();
    lean_initialize();

    const env = try RunMainEnvSnapshot.capture();
    defer env.restore() catch @panic("failed to restore lean_run_main environment");
    _ = libc.unsetenv("LEAN_MAIN_USE_THREAD");

    var probe = RunMainThreadProbe{ .caller_tid = c.pthread_self() };
    g_run_main_thread_probe = &probe;
    defer g_run_main_thread_probe = null;

    try testing.expectEqual(@as(c_int, 0), libc.setenv("LEAN_STACK_SIZE_KB", "66", 1));
    const rounded_result = lean_run_main(runMainProbeOk, 0, null) orelse @panic("lean_run_main returned null");
    defer alloc.lean_free_object(rounded_result);
    try expectResultTag(rounded_result, true, 17);

    const page_size = @as(usize, @intCast(c.getpagesize()));
    try testing.expect(probe.observed_stack_size + page_size >= 64 * 1024);
    try testing.expect(probe.observed_stack_size <= 64 * 1024 + page_size);

    try testing.expectEqual(@as(c_int, 0), libc.unsetenv("LEAN_STACK_SIZE_KB"));
    const default_result = lean_run_main(runMainProbeOk, 0, null) orelse @panic("lean_run_main returned null");
    defer alloc.lean_free_object(default_result);
    try expectResultTag(default_result, true, 17);
    try testing.expect(probe.observed_stack_size + page_size >= thread.defaultStackSizeBytes());
    try testing.expect(probe.observed_stack_size <= thread.defaultStackSizeBytes() + page_size);
}
