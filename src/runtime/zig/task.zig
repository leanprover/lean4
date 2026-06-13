const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const apply = @import("apply.zig");
const ctor = @import("ctor.zig");
const interrupt_tls = @import("interrupt_tls.zig");
const lean = @import("lean_object.zig");
const io_min = @import("io_min.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const task_manager = @import("task_manager.zig");
const task_tls = @import("task_tls.zig");
const libc_c = @cImport({
    @cInclude("unistd.h");
});

fn taskPtr(t: *anyopaque) *lean.lean_task_object {
    return @ptrCast(@alignCast(t));
}

fn promisePtr(p: *anyopaque) *lean.lean_promise_object {
    return @ptrCast(@alignCast(p));
}

fn closurePtr(o: *anyopaque) *lean.lean_closure_object {
    return @ptrCast(@alignCast(o));
}

fn closureSlots(o: *lean.lean_closure_object) [*]?*anyopaque {
    return @ptrCast(&o.m_objs);
}

fn opaqueFunPtr(fun: anytype) ?*anyopaque {
    return @ptrCast(@constCast(fun));
}

fn taskValue(task: *lean.lean_task_object) ?*anyopaque {
    return @atomicLoad(?*anyopaque, &task.m_value, .seq_cst);
}

fn waitAnyCheck(task_list: *anyopaque) ?*anyopaque {
    var it: *anyopaque = task_list;
    while (!object.lean_is_scalar(it)) {
        const head = ctor.lean_ctor_get(it, 0) orelse @panic("task list head missing task");
        if (taskValue(taskPtr(head)) != null) {
            return head;
        }
        it = ctor.lean_ctor_get(it, 1) orelse @panic("task list tail missing");
    }
    return null;
}

fn mkClosure2_1(fun: ?*anyopaque, a: *anyopaque) *anyopaque {
    const closure = closurePtr(alloc.lean_alloc_closure(fun, 2, 1));
    closureSlots(closure)[0] = a;
    return @ptrCast(closure);
}

fn mkClosure3_2(fun: ?*anyopaque, a1: *anyopaque, a2: *anyopaque) *anyopaque {
    const closure = closurePtr(alloc.lean_alloc_closure(fun, 3, 2));
    const slots = closureSlots(closure);
    slots[0] = a1;
    slots[1] = a2;
    return @ptrCast(closure);
}

fn setTaskHeader(task: *lean.lean_task_object) void {
    task.m_header = .{
        .m_rc = -1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanTask,
    };
}

fn allocTaskImp(closure: ?*anyopaque, prio: c_uint, keep_alive: bool) *lean.lean_task_imp {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_task_imp));
    const imp: *lean.lean_task_imp = @ptrCast(@alignCast(ptr));
    imp.* = .{
        .m_closure = closure,
        .m_head_dep = null,
        .m_next_dep = null,
        .m_prio = prio,
        .m_canceled = 0,
        .m_keep_alive = @intFromBool(keep_alive),
        .m_deleted = 0,
    };
    return imp;
}

fn freeTaskImp(imp: *lean.lean_task_imp) void {
    if (imp.m_closure) |closure| {
        rc.lean_dec(closure);
    }
    alloc.lean_free_small_object(@ptrCast(imp));
}

fn allocTask(closure: *anyopaque, prio: c_uint, keep_alive: bool) *lean.lean_task_object {
    rc.lean_mark_mt(closure);
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_task_object));
    const task = taskPtr(ptr);
    alloc.noteTaskObjectAllocation();
    setTaskHeader(task);
    @atomicStore(?*anyopaque, &task.m_value, null, .seq_cst);
    task.m_imp = allocTaskImp(closure, prio, keep_alive);
    return task;
}

fn freeTask(task: *lean.lean_task_object) void {
    if (task.m_imp) |imp| {
        freeTaskImp(imp);
        task.m_imp = null;
    } else {
        rc.lean_dec(@atomicLoad(?*anyopaque, &task.m_value, .seq_cst));
    }
    alloc.noteTaskObjectFree();
    alloc.lean_free_small_object(@ptrCast(task));
}

fn allocFinishedTask(value: *anyopaque) *lean.lean_task_object {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_task_object));
    const task = taskPtr(ptr);
    alloc.noteTaskObjectAllocation();
    task.m_header = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanTask,
    };
    task.m_value = value;
    task.m_imp = null;
    return task;
}

fn allocPromiseTask() *lean.lean_task_object {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_task_object));
    const task = taskPtr(ptr);
    alloc.noteTaskObjectAllocation();
    setTaskHeader(task);
    @atomicStore(?*anyopaque, &task.m_value, null, .seq_cst);
    task.m_imp = allocTaskImp(null, 0, false);
    return task;
}

fn allocPromiseObject() *lean.lean_promise_object {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_promise_object));
    const promise: *lean.lean_promise_object = @ptrCast(@alignCast(ptr));
    promise.* = .{
        .m_header = .{
            .m_rc = 1,
            .m_cs_sz = 0,
            .m_other = 0,
            .m_tag = lean.LeanPromise,
        },
        .m_result = allocPromiseTask(),
    };
    return promise;
}

fn allocPlainObject() *anyopaque {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_object));
    const hdr: *lean.lean_object = @ptrCast(@alignCast(ptr));
    hdr.* = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = 0,
    };
    return ptr;
}

fn asLeanObject(ptr: *anyopaque) *lean.lean_object {
    return @ptrCast(@alignCast(ptr));
}

const TaskMarkMtSnapshot = task_manager.TaskMarkMtSnapshot;
const HeartbeatBoundarySnapshot = interrupt_tls.HeartbeatBoundarySnapshot;

fn mkOptionSome(value: *anyopaque) *anyopaque {
    const some = alloc.lean_alloc_ctor(1, 1, 0);
    ctor.lean_ctor_set(some, 0, value);
    return some;
}

fn resolvePromiseTask(task: *lean.lean_task_object, value: *anyopaque) void {
    if (task_manager.runtimeManager()) |manager| {
        manager.resolve(task, value);
        return;
    }

    if (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null) {
        rc.lean_dec(value);
        return;
    }

    const imp = task.m_imp orelse {
        rc.lean_dec(value);
        return;
    };

    if (imp.m_head_dep != null) {
        @panic("cannot resolve promise without task manager when dependents are pending");
    }

    rc.lean_mark_mt(value);
    task_manager.notePublishedValue(value);
    @atomicStore(?*anyopaque, &task.m_value, value, .seq_cst);
    task.m_imp = null;
    alloc.lean_free_small_object(@ptrCast(imp));
}

pub export fn leanrt_test_alloc_task(closure: *anyopaque, prio: c_uint, keep_alive: bool) callconv(.c) *anyopaque {
    return @ptrCast(allocTask(closure, prio, keep_alive));
}

pub export fn leanrt_test_free_task(task: *anyopaque) callconv(.c) void {
    freeTask(taskPtr(task));
}

pub export fn leanrt_test_runtime_task_manager_init(num_workers: c_uint) callconv(.c) bool {
    return task_manager.createRuntimeManager(num_workers);
}

pub export fn leanrt_test_runtime_task_manager_finalize() callconv(.c) void {
    task_manager.destroyRuntimeManager();
}

pub export fn leanrt_test_runtime_task_manager_active() callconv(.c) bool {
    return task_manager.runtimeManager() != null;
}

pub export fn leanrt_test_runtime_task_wait(task: *anyopaque) callconv(.c) bool {
    return task_manager.waitForRuntimeTask(taskPtr(task));
}

fn sleepTask(ms_obj: *anyopaque, _: *anyopaque) callconv(.c) ?*anyopaque {
    const sleep_ms: u32 = @intCast(object.lean_unbox(ms_obj));
    _ = libc_c.usleep(sleep_ms * 1000);
    return object.lean_box(@intCast(sleep_ms));
}

pub export fn leanrt_test_runtime_spawn_sleep_task(prio: c_uint, sleep_ms: c_uint) callconv(.c) ?*anyopaque {
    if (task_manager.runtimeManager() == null) {
        return null;
    }
    const closure = closurePtr(alloc.lean_alloc_closure(opaqueFunPtr(&sleepTask), 2, 1));
    closureSlots(closure)[0] = object.lean_box(sleep_ms).?;
    return lean_task_spawn_core(@ptrCast(closure), prio, false);
}

pub export fn leanrt_test_io_cancel_chain() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    g_cancel_root_started.store(false, .release);
    g_cancel_root_saw_cancel.store(false, .release);
    g_cancel_middle_saw_cancel.store(false, .release);
    g_cancel_leaf_saw_cancel.store(false, .release);

    const root_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareRoot)), 1, 0);
    const root_obj = lean_task_spawn_core(root_closure, 0, false);
    rc.lean_inc(root_obj);

    const middle_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareMiddle)), 1, 0);
    const middle_obj = lean_task_bind_core(root_obj, middle_closure, 0, false, false);
    rc.lean_inc(middle_obj);

    const leaf_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareLeaf)), 1, 0);
    const leaf_obj = lean_task_bind_core(middle_obj, leaf_closure, 0, false, false);
    defer rc.lean_dec(root_obj);
    defer rc.lean_dec(middle_obj);
    defer rc.lean_dec(leaf_obj);

    spinUntilTrue(&g_cancel_root_started);
    lean_io_cancel_core(root_obj);
    if (!leanrt_test_runtime_task_wait(leaf_obj)) {
        return false;
    }

    return g_cancel_root_saw_cancel.load(.acquire) and
        g_cancel_middle_saw_cancel.load(.acquire) and
        g_cancel_leaf_saw_cancel.load(.acquire);
}

pub export fn leanrt_test_io_task_state_progression() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    g_state_blocker_started.store(false, .release);
    g_state_blocker_release.store(false, .release);
    g_state_target_started.store(false, .release);
    g_state_target_release.store(false, .release);

    const blocker_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&stateBlocker)), 1, 0);
    const blocker = lean_task_spawn_core(blocker_closure, 0, false);
    defer rc.lean_dec(blocker);
    spinUntilTrue(&g_state_blocker_started);

    const target_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&stateTarget)), 1, 0);
    const target = lean_task_spawn_core(target_closure, 0, false);
    defer rc.lean_dec(target);

    if (lean_io_get_task_state_core(target) != 0) {
        return false;
    }

    g_state_blocker_release.store(true, .release);
    spinUntilTrue(&g_state_target_started);
    if (lean_io_get_task_state_core(target) != 1) {
        return false;
    }

    g_state_target_release.store(true, .release);
    if (!leanrt_test_runtime_task_wait(target)) {
        return false;
    }
    return lean_io_get_task_state_core(target) == 2;
}

pub export fn leanrt_test_io_wait_any_returns_first() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(2)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    const producers = [_]?*anyopaque{
        opaqueFunPtr(&delayedWaitAny80),
        opaqueFunPtr(&delayedWaitAny20),
        opaqueFunPtr(&delayedWaitAny60),
        opaqueFunPtr(&delayedWaitAny40),
        opaqueFunPtr(&delayedWaitAny100),
    };
    var task_ptrs: [producers.len]*anyopaque = undefined;
    for (producers, 0..) |producer, i| {
        const closure = alloc.lean_alloc_closure(producer, 1, 0);
        const task_obj = lean_task_spawn_core(closure, 0, false);
        rc.lean_inc(task_obj);
        task_ptrs[i] = task_obj;
    }
    defer {
        for (task_ptrs) |task_obj| {
            rc.lean_dec(task_obj);
        }
    }

    const list = makeTaskList(&task_ptrs);
    defer rc.lean_dec(list);

    const winner = lean_io_wait_any_core(list);
    if (winner != task_ptrs[1]) {
        return false;
    }
    for (task_ptrs) |task_obj| {
        if (!leanrt_test_runtime_task_wait(task_obj)) {
            return false;
        }
    }
    return true;
}

pub export fn leanrt_test_promise_drop_resolves_none() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    const result_task_obj = lean_io_promise_result_opt(promise_obj);
    defer rc.lean_dec(result_task_obj);

    rc.lean_dec(promise_obj);
    if (!waitForTaskValue(taskPtr(result_task_obj), 100)) {
        return false;
    }
    return lean_task_get(result_task_obj) == object.lean_box(0);
}

pub export fn leanrt_test_promise_double_resolve_idempotent() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    defer rc.lean_dec(promise_obj);

    const result_task_obj = lean_io_promise_result_opt(promise_obj);
    defer rc.lean_dec(result_task_obj);

    _ = lean_io_promise_resolve(object.lean_box(33).?, promise_obj);
    _ = lean_io_promise_resolve(object.lean_box(44).?, promise_obj);
    if (!waitForTaskValue(taskPtr(result_task_obj), 100)) {
        return false;
    }

    const option = lean_task_get(result_task_obj);
    if (object.lean_is_scalar(option) or object.lean_obj_tag(option) != 1) {
        return false;
    }
    return object.lean_unbox(ctor.lean_ctor_get(option, 0)) == 33;
}

pub export fn leanrt_test_promise_rc_balanced() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();

    alloc.resetTestCounters();
    for (0..1000) |i| {
        const promise_obj = lean_io_promise_new();
        const result_task_obj = lean_io_promise_result_opt(promise_obj);
        _ = lean_io_promise_resolve(object.lean_box(i).?, promise_obj);
        if (!waitForTaskValue(taskPtr(result_task_obj), 100)) {
            rc.lean_dec(promise_obj);
            rc.lean_dec(result_task_obj);
            return false;
        }
        rc.lean_dec(promise_obj);
        rc.lean_dec(result_task_obj);
    }
    return alloc.testAllocCount() == alloc.testFreeCount();
}

pub export fn lean_task_spawn_core(c: *anyopaque, prio: c_uint, keep_alive: bool) callconv(.c) *anyopaque {
    if (task_manager.runtimeManager()) |manager| {
        const task = allocTask(c, prio, keep_alive);
        manager.enqueue(task) catch @panic("failed to enqueue task");
        return @ptrCast(task);
    }
    const value = apply.lean_apply_1(c, object.lean_box(0).?) orelse @panic("task spawn fast-path returned null");
    return lean_task_pure(value);
}

export fn lean_task_pure(a: *anyopaque) callconv(.c) *anyopaque {
    return @ptrCast(allocFinishedTask(a));
}

fn taskGetOwn(t: *anyopaque) *anyopaque {
    const task = taskPtr(t);
    if (taskValue(task) == null) {
        const manager = task_manager.runtimeManager() orelse @panic("task manager unavailable");
        manager.waitForCompletion(task);
    }
    const value = taskValue(task) orelse @panic("task_get_own observed unfinished task");
    rc.lean_inc(value);
    rc.lean_dec(t);
    return value;
}

fn taskBindFn2(t: *anyopaque, _: *anyopaque) callconv(.c) ?*anyopaque {
    const task = taskPtr(t);
    const value = taskValue(task) orelse @panic("bind continuation resumed before nested task resolved");
    rc.lean_inc(value);
    rc.lean_dec_ref(t);
    return value;
}

fn taskBindFn1(x: *anyopaque, f: *anyopaque, _: *anyopaque) callconv(.c) ?*anyopaque {
    const source = taskPtr(x);
    const value = taskValue(source) orelse @panic("bind source task must be resolved before continuation runs");
    rc.lean_inc(value);
    rc.lean_dec_ref(x);

    const new_task_obj = apply.lean_apply_1(f, value) orelse @panic("bind continuation returned null");
    if (object.lean_is_scalar(new_task_obj) or object.lean_ptr_tag(new_task_obj) != lean.LeanTask) {
        @panic("bind continuation must return a task");
    }

    const new_task = taskPtr(new_task_obj);
    if (taskValue(new_task)) |resolved| {
        rc.lean_inc(resolved);
        rc.lean_dec_ref(new_task_obj);
        return resolved;
    }

    const current = task_tls.get() orelse @panic("task bind continuation requires current task tls");
    const current_imp = current.m_imp orelse @panic("current bind task must still be pending");
    if (current_imp.m_closure != null) @panic("current bind task already has a continuation closure");
    const closure = mkClosure2_1(opaqueFunPtr(&taskBindFn2), new_task_obj);
    rc.lean_mark_mt(closure);
    current_imp.m_closure = closure;
    return null;
}

fn taskMapFn(f: *anyopaque, t: *anyopaque, _: *anyopaque) callconv(.c) ?*anyopaque {
    const task = taskPtr(t);
    const value = taskValue(task) orelse @panic("map source task must be resolved before continuation runs");
    rc.lean_inc(value);
    rc.lean_dec_ref(t);
    return apply.lean_apply_1(f, value);
}

pub export fn lean_task_bind_core(x: *anyopaque, f: *anyopaque, prio: c_uint, sync: bool, keep_alive: bool) callconv(.c) *anyopaque {
    const manager = task_manager.runtimeManager();

    if (manager == null or (sync and taskValue(taskPtr(x)) != null)) {
        return apply.lean_apply_1(f, taskGetOwn(x)) orelse @panic("bind fast-path returned null");
    }

    const closure = mkClosure3_2(opaqueFunPtr(&taskBindFn1), x, f);
    const new_task = allocTask(closure, if (sync) task_manager.LEAN_SYNC_PRIO else prio, keep_alive);
    manager.?.addDependency(taskPtr(x), new_task) catch @panic("failed to register bind dependency");
    return @ptrCast(new_task);
}

pub export fn lean_task_map_core(f: *anyopaque, t: *anyopaque, prio: c_uint, sync: bool, keep_alive: bool) callconv(.c) *anyopaque {
    const manager = task_manager.runtimeManager();

    if (manager == null or (sync and taskValue(taskPtr(t)) != null)) {
        const value = apply.lean_apply_1(f, taskGetOwn(t)) orelse @panic("task map fast-path returned null");
        return lean_task_pure(value);
    }

    const closure = mkClosure3_2(opaqueFunPtr(&taskMapFn), f, t);
    const new_task = allocTask(closure, if (sync) task_manager.LEAN_SYNC_PRIO else prio, keep_alive);
    manager.?.addDependency(taskPtr(t), new_task) catch @panic("failed to register map dependency");
    return @ptrCast(new_task);
}

pub export fn lean_task_get(t: *anyopaque) callconv(.c) *anyopaque {
    const task = taskPtr(t);
    if (taskValue(task)) |value| {
        return value;
    }

    if (task_manager.runtimeManager()) |manager| {
        manager.waitForGet(task);
        return taskValue(task) orelse @panic("lean_task_get observed unfinished task after wait");
    }

    @panic("task manager unavailable for pending task");
}

pub export fn lean_io_check_canceled_core() callconv(.c) bool {
    if (task_tls.get()) |current| {
        const imp = current.m_imp orelse @panic("current task tls must point at a running task");
        return imp.m_canceled != 0 or (task_manager.runtimeManager() != null and task_manager.runtimeManager().?.shuttingDown());
    }
    return false;
}

pub export fn lean_io_cancel_core(t: *anyopaque) callconv(.c) void {
    const task = taskPtr(t);
    if (taskValue(task) != null) {
        return;
    }
    if (task_manager.runtimeManager()) |manager| {
        manager.cancel(task);
        return;
    }
    if (task.m_imp) |imp| {
        imp.m_canceled = 1;
    }
}

pub export fn lean_io_get_task_state_core(t: *anyopaque) callconv(.c) u8 {
    const task = taskPtr(t);
    if (task.m_imp == null) {
        return 2;
    }
    if (task_manager.runtimeManager()) |manager| {
        return manager.getTaskState(task);
    }
    return if (task.m_imp.?.m_closure != null) 0 else 1;
}

pub export fn lean_io_wait_any_core(task_list: *anyopaque) callconv(.c) *anyopaque {
    if (task_manager.runtimeManager()) |manager| {
        return manager.waitAny(task_list);
    }
    if (waitAnyCheck(task_list)) |winner| {
        return winner;
    }
    io_min.lean_panic(
        "`IO.waitAny` called with pending tasks before the task manager is running",
        false,
    );
    unreachable;
}

pub export fn lean_io_promise_new() callconv(.c) *anyopaque {
    if (task_manager.runtimeManager() == null) {
        io_min.lean_panic(
            "`IO.Promise.new` called before the task manager is running; this typically happens when called before `lean_run_main` starts the runtime",
            false,
        );
        unreachable;
    }
    return @ptrCast(allocPromiseObject());
}

pub export fn lean_io_promise_resolve(value: *anyopaque, promise: *anyopaque) callconv(.c) *anyopaque {
    const promise_obj = promisePtr(promise);
    const task = promise_obj.m_result orelse @panic("promise missing backing task");
    resolvePromiseTask(task, mkOptionSome(value));
    return object.lean_box(0).?;
}

pub export fn lean_io_promise_result_opt(promise: *anyopaque) callconv(.c) *anyopaque {
    const task = promisePtr(promise).m_result orelse @panic("promise missing backing task");
    rc.lean_inc_ref(@ptrCast(task));
    return @ptrCast(task);
}

pub export fn leanrt_task_deactivate_task_impl(task_obj: *lean.lean_task_object) callconv(.c) void {
    if (task_obj.m_imp) |imp| {
        var it = imp.m_head_dep;
        imp.m_head_dep = null;
        imp.m_canceled = 1;
        imp.m_deleted = 1;
        while (it) |dep| {
            const dep_imp = dep.m_imp;
            const next = if (dep_imp) |value| value.m_next_dep else null;
            freeTask(dep);
            it = next;
        }
    }
    freeTask(task_obj);
}

pub export fn leanrt_task_deactivate_promise_impl(promise: *anyopaque) callconv(.c) void {
    const promise_obj = promisePtr(promise);
    const task = promise_obj.m_result orelse @panic("promise missing backing task");
    resolvePromiseTask(task, object.lean_box(0).?);
    rc.lean_dec_ref(@ptrCast(task));
    alloc.lean_free_small_object(promise);
}

fn spawnReturnsFortyTwo(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    return object.lean_box(42);
}

var g_bind_release = std.atomic.Value(bool).init(false);
var g_bind_runs = std.atomic.Value(usize).init(0);
var g_dep_chain_release = std.atomic.Value(bool).init(false);
var g_map_release = std.atomic.Value(bool).init(false);
var g_pending_outer_release = std.atomic.Value(bool).init(false);
var g_pending_inner_release = std.atomic.Value(bool).init(false);
var g_pending_inner_started = std.atomic.Value(usize).init(0);
var g_pending_bind_runs = std.atomic.Value(usize).init(0);
var g_cancel_root_started = std.atomic.Value(bool).init(false);
var g_cancel_root_saw_cancel = std.atomic.Value(bool).init(false);
var g_cancel_middle_saw_cancel = std.atomic.Value(bool).init(false);
var g_cancel_leaf_saw_cancel = std.atomic.Value(bool).init(false);
var g_state_blocker_started = std.atomic.Value(bool).init(false);
var g_state_blocker_release = std.atomic.Value(bool).init(false);
var g_state_target_started = std.atomic.Value(bool).init(false);
var g_state_target_release = std.atomic.Value(bool).init(false);

fn spinUntilTrue(flag: *std.atomic.Value(bool)) void {
    while (!flag.load(.acquire)) {
        std.atomic.spinLoopHint();
        std.Thread.yield() catch {};
    }
}

fn spinUntilCount(counter: *std.atomic.Value(usize), expected: usize) void {
    while (counter.load(.acquire) < expected) {
        std.atomic.spinLoopHint();
        std.Thread.yield() catch {};
    }
}

fn waitForTaskValue(task: *lean.lean_task_object, timeout_ms: u64) bool {
    var remaining_polls: u64 = timeout_ms * 200;
    const delay = std.c.timespec{ .sec = 0, .nsec = 500_000 };
    while (taskValue(task) == null) {
        if (remaining_polls == 0) {
            return false;
        }
        remaining_polls -= 1;
        std.atomic.spinLoopHint();
        std.Thread.yield() catch {};
        _ = std.c.nanosleep(&delay, null);
    }
    return true;
}

fn blockingBindProducer(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    spinUntilTrue(&g_bind_release);
    return object.lean_box(5);
}

fn blockingMapProducer(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    spinUntilTrue(&g_map_release);
    return object.lean_box(42);
}

fn mapAddOne(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    return object.lean_box(object.lean_unbox(value) + 1);
}

fn bindToFinishedTask(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 5) @panic("unexpected bind input");
    _ = g_bind_runs.fetchAdd(1, .acq_rel);
    return lean_task_pure(object.lean_box(42).?);
}

fn blockingDepChainRoot(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    spinUntilTrue(&g_dep_chain_release);
    return object.lean_box(9);
}

fn bindReturnEleven(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 9) @panic("unexpected dep-chain input");
    return lean_task_pure(object.lean_box(11).?);
}

fn bindReturnTwelve(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 9) @panic("unexpected dep-chain input");
    return lean_task_pure(object.lean_box(12).?);
}

fn bindReturnThirteen(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 9) @panic("unexpected dep-chain input");
    return lean_task_pure(object.lean_box(13).?);
}

fn blockingPendingOuter(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    spinUntilTrue(&g_pending_outer_release);
    return object.lean_box(7);
}

fn blockingPendingInner(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    _ = g_pending_inner_started.fetchAdd(1, .acq_rel);
    spinUntilTrue(&g_pending_inner_release);
    return object.lean_box(13);
}

fn bindToPendingTask(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 7) @panic("unexpected pending bind input");
    _ = g_pending_bind_runs.fetchAdd(1, .acq_rel);
    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingPendingInner)), 1, 0);
    return lean_task_spawn_core(closure, 0, false);
}

fn cancelAwareRoot(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    g_cancel_root_started.store(true, .release);
    while (!lean_io_check_canceled_core()) {
        std.atomic.spinLoopHint();
        std.Thread.yield() catch {};
    }
    g_cancel_root_saw_cancel.store(true, .release);
    return object.lean_box(10);
}

fn cancelAwareMiddle(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 10) @panic("unexpected cancel middle input");
    g_cancel_middle_saw_cancel.store(lean_io_check_canceled_core(), .release);
    return lean_task_pure(object.lean_box(20).?);
}

fn cancelAwareLeaf(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_unbox(value) != 20) @panic("unexpected cancel leaf input");
    g_cancel_leaf_saw_cancel.store(lean_io_check_canceled_core(), .release);
    return lean_task_pure(object.lean_box(30).?);
}

fn stateBlocker(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    g_state_blocker_started.store(true, .release);
    spinUntilTrue(&g_state_blocker_release);
    return object.lean_box(1);
}

fn stateTarget(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    g_state_target_started.store(true, .release);
    spinUntilTrue(&g_state_target_release);
    return object.lean_box(2);
}

fn delayedWaitAny20(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    const delay = std.c.timespec{ .sec = 0, .nsec = 20 * std.time.ns_per_ms };
    _ = std.c.nanosleep(&delay, null);
    return object.lean_box(20);
}

fn delayedWaitAny40(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    const delay = std.c.timespec{ .sec = 0, .nsec = 40 * std.time.ns_per_ms };
    _ = std.c.nanosleep(&delay, null);
    return object.lean_box(40);
}

fn delayedWaitAny60(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    const delay = std.c.timespec{ .sec = 0, .nsec = 60 * std.time.ns_per_ms };
    _ = std.c.nanosleep(&delay, null);
    return object.lean_box(60);
}

fn delayedWaitAny80(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    const delay = std.c.timespec{ .sec = 0, .nsec = 80 * std.time.ns_per_ms };
    _ = std.c.nanosleep(&delay, null);
    return object.lean_box(80);
}

fn delayedWaitAny100(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    const delay = std.c.timespec{ .sec = 0, .nsec = 100 * std.time.ns_per_ms };
    _ = std.c.nanosleep(&delay, null);
    return object.lean_box(100);
}

fn makeTaskList(tasks: []const *anyopaque) *anyopaque {
    var list = object.lean_box(0).?;
    var i = tasks.len;
    while (i > 0) {
        i -= 1;
        const cons = alloc.lean_alloc_ctor(1, 2, 0);
        ctor.lean_ctor_set(cons, 0, tasks[i]);
        ctor.lean_ctor_set(cons, 1, list);
        list = cons;
    }
    return list;
}

fn delayedRelease(flag: *std.atomic.Value(bool)) void {
    const delay = std.c.timespec{
        .sec = 0,
        .nsec = 50 * std.time.ns_per_ms,
    };
    _ = std.c.nanosleep(&delay, null);
    flag.store(true, .release);
}

fn chainGetProducer(depth_obj: ?*anyopaque, _: ?*anyopaque) callconv(.c) ?*anyopaque {
    const depth = object.lean_unbox(depth_obj);
    if (depth == 0) {
        return object.lean_box(0);
    }

    const closure = closurePtr(alloc.lean_alloc_closure(opaqueFunPtr(&chainGetProducer), 2, 1));
    closureSlots(closure)[0] = object.lean_box(depth - 1);
    const child_task = lean_task_spawn_core(@ptrCast(closure), 0, false);
    defer rc.lean_dec(child_task);

    const value = lean_task_get(child_task);
    return object.lean_box(object.lean_unbox(value) + 1);
}

fn heapTaskResult(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    return allocPlainObject();
}

fn mapToHeapTask(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    rc.lean_dec(value);
    return allocPlainObject();
}

fn bindToHeapTask(value: ?*anyopaque) callconv(.c) ?*anyopaque {
    rc.lean_dec(value);
    return lean_task_pure(allocPlainObject());
}

fn heartbeatPulseTask(_: ?*anyopaque) callconv(.c) ?*anyopaque {
    interrupt_tls.noteHeartbeatPulseForTest(7);
    return object.lean_box(7);
}

fn heapTaskValueIsMarked(task_obj: *anyopaque) bool {
    const value = taskValue(taskPtr(task_obj)) orelse return false;
    return !object.lean_is_scalar(value) and asLeanObject(value).m_rc < 0;
}

fn markMtSnapshot() TaskMarkMtSnapshot {
    return task_manager.taskMarkMtSnapshot();
}

fn snapshotShowsAllMarked(min_closures: c_uint, min_values: c_uint) bool {
    const snapshot = markMtSnapshot();
    return snapshot.dequeued_closures >= min_closures and
        snapshot.published_values >= min_values and
        snapshot.all_dequeued_closures_marked and
        snapshot.all_published_values_marked and
        snapshot.last_dequeued_closure_rc < 0 and
        snapshot.last_published_value_rc < 0;
}

fn heartbeatSnapshotShowsExpected(expect_post_run: bool) bool {
    const snapshot = interrupt_tls.heartbeatBoundarySnapshot();
    return snapshot.pre_spawn_before_reset == 0 and
        snapshot.pre_spawn == 0 and
        snapshot.post_spawn_before_reset > 0 and
        snapshot.post_spawn == 0 and
        (!expect_post_run or snapshot.post_run_before_reset == 0) and
        snapshot.post_run == 0;
}

pub export fn leanrt_test_task_heartbeat_snapshot(out: *HeartbeatBoundarySnapshot) callconv(.c) void {
    out.* = interrupt_tls.heartbeatBoundarySnapshot();
}

pub export fn leanrt_test_task_heartbeat_standard_smoke() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    interrupt_tls.resetHeartbeatBoundaryState();

    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heartbeatPulseTask)), 1, 0);
    const task = lean_task_spawn_core(closure, 0, false);
    defer rc.lean_dec(task);

    if (!leanrt_test_runtime_task_wait(task)) {
        return false;
    }
    return heartbeatSnapshotShowsExpected(true);
}

pub export fn leanrt_test_task_heartbeat_dedicated_smoke() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    interrupt_tls.resetHeartbeatBoundaryState();

    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heartbeatPulseTask)), 1, 0);
    const task = lean_task_spawn_core(closure, @as(c_uint, task_manager.LEAN_MAX_PRIO + 1), false);
    defer rc.lean_dec(task);

    if (!leanrt_test_runtime_task_wait(task)) {
        return false;
    }
    return heartbeatSnapshotShowsExpected(false);
}

pub export fn leanrt_test_task_mark_mt_spawn_smoke() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    task_manager.resetTaskMarkMtState();

    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heapTaskResult)), 1, 0);
    const task = lean_task_spawn_core(closure, 0, false);
    defer rc.lean_dec(task);

    if (!leanrt_test_runtime_task_wait(task)) {
        return false;
    }
    return heapTaskValueIsMarked(task) and snapshotShowsAllMarked(1, 1);
}

pub export fn leanrt_test_task_mark_mt_map_smoke() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    task_manager.resetTaskMarkMtState();

    const producer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heapTaskResult)), 1, 0);
    const producer_task = lean_task_spawn_core(producer_closure, 0, false);
    const map_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&mapToHeapTask)), 1, 0);
    const mapped_task = lean_task_map_core(map_closure, producer_task, 0, false, false);
    defer rc.lean_dec(mapped_task);

    if (!leanrt_test_runtime_task_wait(mapped_task)) {
        return false;
    }
    return heapTaskValueIsMarked(mapped_task) and snapshotShowsAllMarked(2, 2);
}

pub export fn leanrt_test_task_mark_mt_bind_smoke() callconv(.c) bool {
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    task_manager.resetTaskMarkMtState();

    const producer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heapTaskResult)), 1, 0);
    const producer_task = lean_task_spawn_core(producer_closure, 0, false);
    const bind_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindToHeapTask)), 1, 0);
    const bound_task = lean_task_bind_core(producer_task, bind_closure, 0, false, false);
    defer rc.lean_dec(bound_task);

    if (!leanrt_test_runtime_task_wait(bound_task)) {
        return false;
    }
    return heapTaskValueIsMarked(bound_task) and snapshotShowsAllMarked(2, 2);
}

pub export fn leanrt_test_task_mark_mt_spawn_stress(iterations: c_uint) callconv(.c) bool {
    if (iterations == 0) {
        return true;
    }
    if (!leanrt_test_runtime_task_manager_init(1)) {
        return false;
    }
    defer leanrt_test_runtime_task_manager_finalize();
    task_manager.resetTaskMarkMtState();

    var i: c_uint = 0;
    while (i < iterations) : (i += 1) {
        const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&heapTaskResult)), 1, 0);
        const task_obj = lean_task_spawn_core(closure, 0, false);
        if (!leanrt_test_runtime_task_wait(task_obj) or !heapTaskValueIsMarked(task_obj)) {
            rc.lean_dec(task_obj);
            return false;
        }
        rc.lean_dec(task_obj);
    }
    return snapshotShowsAllMarked(iterations, iterations);
}

test "task layouts match lean.h" {
    try testing.expectEqual(@as(usize, 32), @sizeOf(lean.lean_task_imp));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_task_imp, "m_closure"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_task_imp, "m_head_dep"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_task_imp, "m_next_dep"));
    try testing.expectEqual(@as(usize, 24), @offsetOf(lean.lean_task_imp, "m_prio"));
    try testing.expectEqual(@as(usize, 28), @offsetOf(lean.lean_task_imp, "m_canceled"));
    try testing.expectEqual(@as(usize, 29), @offsetOf(lean.lean_task_imp, "m_keep_alive"));
    try testing.expectEqual(@as(usize, 30), @offsetOf(lean.lean_task_imp, "m_deleted"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_task_object));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_task_object, "m_header"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_task_object, "m_value"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_task_object, "m_imp"));

    try testing.expectEqual(@as(usize, 16), @sizeOf(lean.lean_promise_object));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_promise_object, "m_header"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_promise_object, "m_result"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_thunk_object));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_thunk_object, "m_header"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_thunk_object, "m_value"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_thunk_object, "m_closure"));
}

test "lean_task_pure returns a finished task with rc one" {
    const value = object.lean_box(0).?;
    const task = taskPtr(lean_task_pure(value));
    defer rc.lean_dec(@ptrCast(task));

    try testing.expectEqual(@as(i32, 1), task.m_header.m_rc);
    try testing.expectEqual(lean.LeanTask, task.m_header.m_tag);
    try testing.expectEqual(@as(?*anyopaque, value), task.m_value);
    try testing.expectEqual(@as(?*lean.lean_task_imp, null), task.m_imp);
}

test "lean_task_pure releases its owned value when the task is freed" {
    const value = allocPlainObject();
    const task = lean_task_pure(value);

    alloc.resetTestCounters();
    rc.lean_dec(task);

    try testing.expectEqual(@as(usize, 2), alloc.testFreeCount());
}

test "lean_task_get returns a borrowed fast-path value without changing rc" {
    const value = allocPlainObject();
    const task = lean_task_pure(value);
    defer rc.lean_dec(task);

    try testing.expectEqual(@as(i32, 1), asLeanObject(value).m_rc);
    const result = lean_task_get(task);
    try testing.expectEqual(@as(*anyopaque, value), result);
    try testing.expectEqual(@as(i32, 1), asLeanObject(value).m_rc);
}

test "current task tls getter reflects the zig threadlocal slot" {
    const task = taskPtr(lean_task_pure(object.lean_box(7).?));
    defer rc.lean_dec(@ptrCast(task));

    const prev = task_tls.swap(task);
    defer _ = task_tls.swap(prev);

    try testing.expectEqual(@as(?*lean.lean_task_object, task), task_tls.get());
}

test "allocTask preserves pending task layout for spawn" {
    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&spawnReturnsFortyTwo)), 1, 0);
    const task = allocTask(closure, 2, false);
    defer freeTask(task);

    try testing.expectEqual(@as(i32, -1), task.m_header.m_rc);
    try testing.expectEqual(lean.LeanTask, task.m_header.m_tag);
    try testing.expectEqual(@as(?*anyopaque, null), @atomicLoad(?*anyopaque, &task.m_value, .seq_cst));
    try testing.expect(task.m_imp != null);
    try testing.expectEqual(@as(?*anyopaque, closure), task.m_imp.?.m_closure);
    try testing.expectEqual(@as(c_uint, 2), task.m_imp.?.m_prio);
}

test "lean_task_spawn_core resolves spawned closures through the zig manager" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&spawnReturnsFortyTwo)), 1, 0);
    const task = taskPtr(lean_task_spawn_core(closure, 0, false));
    defer rc.lean_dec(@ptrCast(task));

    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(task)));
    try testing.expectEqual(@as(?*lean.lean_task_imp, null), task.m_imp);
    try testing.expectEqual(@as(usize, 42), object.lean_unbox(@atomicLoad(?*anyopaque, &task.m_value, .seq_cst)));
}

test "lean_task_get blocks on pending runtime tasks and returns the produced value" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_map_release.store(false, .release);

    const producer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingMapProducer)), 1, 0);
    const task = taskPtr(lean_task_spawn_core(producer_closure, 0, false));
    defer rc.lean_dec(@ptrCast(task));

    const releaser = try std.Thread.spawn(.{}, delayedRelease, .{&g_map_release});
    const value = lean_task_get(@ptrCast(task));
    releaser.join();

    try testing.expectEqual(@as(usize, 42), object.lean_unbox(value));
}

test "lean_task_get from a worker spawns replacement workers and restores max workers after waiting" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const root_closure = closurePtr(alloc.lean_alloc_closure(opaqueFunPtr(&chainGetProducer), 2, 1));
    closureSlots(root_closure)[0] = object.lean_box(4);
    const task = taskPtr(lean_task_spawn_core(@ptrCast(root_closure), 0, false));
    defer rc.lean_dec(@ptrCast(task));

    const value = lean_task_get(@ptrCast(task));
    const snapshot = task_manager.runtimeManager().?.snapshot();

    try testing.expectEqual(@as(usize, 4), object.lean_unbox(value));
    try testing.expect(snapshot.worker_count >= 2);
    try testing.expectEqual(@as(c_uint, 1), snapshot.max_std_workers);
}

test "lean_task_map_core maps pure tasks like direct apply" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const pure_task = lean_task_pure(object.lean_box(8).?);
    const map_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&mapAddOne)), 1, 0);
    const mapped = taskPtr(lean_task_map_core(map_closure, pure_task, 0, true, false));
    defer rc.lean_dec(@ptrCast(mapped));

    try testing.expectEqual(@as(?*lean.lean_task_imp, null), mapped.m_imp);
    try testing.expectEqual(@as(usize, 9), object.lean_unbox(@atomicLoad(?*anyopaque, &mapped.m_value, .seq_cst)));
}

test "lean_task_map_core links dependent tasks and resolves mapped values" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_map_release.store(false, .release);

    const producer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingMapProducer)), 1, 0);
    const producer_obj = lean_task_spawn_core(producer_closure, 0, false);
    const producer = taskPtr(producer_obj);
    rc.lean_inc(producer_obj);

    const map_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&mapAddOne)), 1, 0);
    const mapped = taskPtr(lean_task_map_core(map_closure, producer_obj, 0, false, false));
    defer rc.lean_dec(@ptrCast(producer));
    defer rc.lean_dec(@ptrCast(mapped));

    try testing.expectEqual(@as(?*lean.lean_task_object, mapped), producer.m_imp.?.m_head_dep);
    try testing.expectEqual(@as(?*lean.lean_task_object, null), mapped.m_imp.?.m_next_dep);

    g_map_release.store(true, .release);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(mapped)));
    try testing.expectEqual(@as(usize, 43), object.lean_unbox(@atomicLoad(?*anyopaque, &mapped.m_value, .seq_cst)));
}

test "lean_task_bind_core links dependent tasks and resolves after source completes" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_bind_release.store(false, .release);
    g_bind_runs.store(0, .release);

    const producer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingBindProducer)), 1, 0);
    const producer_obj = lean_task_spawn_core(producer_closure, 0, false);
    const producer = taskPtr(producer_obj);
    rc.lean_inc(producer_obj);

    const bind_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindToFinishedTask)), 1, 0);
    const bound = taskPtr(lean_task_bind_core(producer_obj, bind_closure, 0, false, false));
    defer rc.lean_dec(@ptrCast(producer));
    defer rc.lean_dec(@ptrCast(bound));

    try testing.expectEqual(@as(?*lean.lean_task_object, bound), producer.m_imp.?.m_head_dep);
    try testing.expectEqual(@as(?*lean.lean_task_object, null), bound.m_imp.?.m_next_dep);

    g_bind_release.store(true, .release);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(bound)));
    try testing.expectEqual(@as(usize, 1), g_bind_runs.load(.acquire));
    try testing.expectEqual(@as(usize, 42), object.lean_unbox(@atomicLoad(?*anyopaque, &bound.m_value, .seq_cst)));
}

test "lean_task_bind_core keeps dependent pending when continuation returns unfinished task" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_pending_outer_release.store(false, .release);
    g_pending_inner_release.store(false, .release);
    g_pending_inner_started.store(0, .release);
    g_pending_bind_runs.store(0, .release);

    const outer_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingPendingOuter)), 1, 0);
    const outer_obj = lean_task_spawn_core(outer_closure, 0, false);
    const outer = taskPtr(outer_obj);
    rc.lean_inc(outer_obj);

    const bind_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindToPendingTask)), 1, 0);
    const bound = taskPtr(lean_task_bind_core(outer_obj, bind_closure, 0, false, false));
    defer rc.lean_dec(@ptrCast(outer));
    defer rc.lean_dec(@ptrCast(bound));

    g_pending_outer_release.store(true, .release);
    spinUntilCount(&g_pending_inner_started, 1);

    try testing.expectEqual(@as(usize, 1), g_pending_bind_runs.load(.acquire));
    try testing.expectEqual(@as(?*anyopaque, null), @atomicLoad(?*anyopaque, &bound.m_value, .seq_cst));
    try testing.expect(bound.m_imp != null);
    try testing.expect(bound.m_imp.?.m_closure != null);

    g_pending_inner_release.store(true, .release);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(bound)));
    try testing.expectEqual(@as(usize, 13), object.lean_unbox(@atomicLoad(?*anyopaque, &bound.m_value, .seq_cst)));
}

test "spawned closures and produced heap values are mark_mt before observation" {
    try testing.expect(leanrt_test_task_mark_mt_spawn_smoke());

    const snapshot = markMtSnapshot();
    try testing.expectEqual(@as(c_uint, 1), snapshot.dequeued_closures);
    try testing.expectEqual(@as(c_uint, 1), snapshot.published_values);
}

test "map and bind continuations publish only mt-marked heap values" {
    try testing.expect(leanrt_test_task_mark_mt_map_smoke());
    var snapshot = markMtSnapshot();
    try testing.expect(snapshot.dequeued_closures >= 2);
    try testing.expect(snapshot.published_values >= 2);

    try testing.expect(leanrt_test_task_mark_mt_bind_smoke());
    snapshot = markMtSnapshot();
    try testing.expect(snapshot.dequeued_closures >= 2);
    try testing.expect(snapshot.published_values >= 2);
}

test "spawn stress keeps mark_mt guarantees across one thousand heap results" {
    try testing.expect(leanrt_test_task_mark_mt_spawn_stress(1000));

    const snapshot = markMtSnapshot();
    try testing.expectEqual(@as(c_uint, 1000), snapshot.dequeued_closures);
    try testing.expectEqual(@as(c_uint, 1000), snapshot.published_values);
}

test "heartbeat boundary resets around standard and dedicated task execution" {
    try testing.expect(leanrt_test_task_heartbeat_standard_smoke());
    try testing.expect(leanrt_test_task_heartbeat_dedicated_smoke());
}

test "dependent chain stays singly linked in reverse registration order" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_dep_chain_release.store(false, .release);

    const root_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&blockingDepChainRoot)), 1, 0);
    const root_obj = lean_task_spawn_core(root_closure, 0, false);
    const root = taskPtr(root_obj);
    rc.lean_inc(root_obj);
    rc.lean_inc(root_obj);
    rc.lean_inc(root_obj);

    const bind_b = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindReturnEleven)), 1, 0);
    const task_b = taskPtr(lean_task_bind_core(root_obj, bind_b, 0, false, false));
    const bind_c = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindReturnTwelve)), 1, 0);
    const task_c = taskPtr(lean_task_bind_core(root_obj, bind_c, 0, false, false));
    const bind_d = alloc.lean_alloc_closure(@ptrCast(@constCast(&bindReturnThirteen)), 1, 0);
    const task_d = taskPtr(lean_task_bind_core(root_obj, bind_d, 0, false, false));
    defer rc.lean_dec(@ptrCast(root));
    defer rc.lean_dec(@ptrCast(task_b));
    defer rc.lean_dec(@ptrCast(task_c));
    defer rc.lean_dec(@ptrCast(task_d));

    try testing.expectEqual(@as(?*lean.lean_task_object, task_d), root.m_imp.?.m_head_dep);
    try testing.expectEqual(@as(?*lean.lean_task_object, task_c), task_d.m_imp.?.m_next_dep);
    try testing.expectEqual(@as(?*lean.lean_task_object, task_b), task_c.m_imp.?.m_next_dep);
    try testing.expectEqual(@as(?*lean.lean_task_object, null), task_b.m_imp.?.m_next_dep);

    g_dep_chain_release.store(true, .release);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(task_b)));
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(task_c)));
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(task_d)));
}

test "cancel propagates through a three-deep bind chain" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_cancel_root_started.store(false, .release);
    g_cancel_root_saw_cancel.store(false, .release);
    g_cancel_middle_saw_cancel.store(false, .release);
    g_cancel_leaf_saw_cancel.store(false, .release);

    const root_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareRoot)), 1, 0);
    const root_obj = lean_task_spawn_core(root_closure, 0, false);
    const root = taskPtr(root_obj);
    rc.lean_inc(root_obj);

    const middle_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareMiddle)), 1, 0);
    const middle_obj = lean_task_bind_core(root_obj, middle_closure, 0, false, false);
    const middle = taskPtr(middle_obj);
    rc.lean_inc(middle_obj);
    const leaf_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&cancelAwareLeaf)), 1, 0);
    const leaf = taskPtr(lean_task_bind_core(middle_obj, leaf_closure, 0, false, false));
    defer rc.lean_dec(@ptrCast(root));
    defer rc.lean_dec(@ptrCast(middle));
    defer rc.lean_dec(@ptrCast(leaf));

    spinUntilTrue(&g_cancel_root_started);
    lean_io_cancel_core(root_obj);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(leaf)));

    try testing.expect(g_cancel_root_saw_cancel.load(.acquire));
    try testing.expect(g_cancel_middle_saw_cancel.load(.acquire));
    try testing.expect(g_cancel_leaf_saw_cancel.load(.acquire));
}

test "task state progresses waiting running finished" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    g_state_blocker_started.store(false, .release);
    g_state_blocker_release.store(false, .release);
    g_state_target_started.store(false, .release);
    g_state_target_release.store(false, .release);

    const blocker_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&stateBlocker)), 1, 0);
    const blocker = taskPtr(lean_task_spawn_core(blocker_closure, 0, false));
    defer rc.lean_dec(@ptrCast(blocker));
    spinUntilTrue(&g_state_blocker_started);

    const target_closure = alloc.lean_alloc_closure(@ptrCast(@constCast(&stateTarget)), 1, 0);
    const target = taskPtr(lean_task_spawn_core(target_closure, 0, false));
    defer rc.lean_dec(@ptrCast(target));

    try testing.expectEqual(@as(u8, 0), lean_io_get_task_state_core(@ptrCast(target)));

    g_state_blocker_release.store(true, .release);
    spinUntilTrue(&g_state_target_started);
    try testing.expectEqual(@as(u8, 1), lean_io_get_task_state_core(@ptrCast(target)));

    g_state_target_release.store(true, .release);
    try testing.expect(leanrt_test_runtime_task_wait(@ptrCast(target)));
    try testing.expectEqual(@as(u8, 2), lean_io_get_task_state_core(@ptrCast(target)));
}

test "wait_any returns the first finished task from the input list" {
    try testing.expect(leanrt_test_runtime_task_manager_init(2));
    defer leanrt_test_runtime_task_manager_finalize();

    const producers = [_]?*anyopaque{
        opaqueFunPtr(&delayedWaitAny80),
        opaqueFunPtr(&delayedWaitAny20),
        opaqueFunPtr(&delayedWaitAny60),
        opaqueFunPtr(&delayedWaitAny40),
        opaqueFunPtr(&delayedWaitAny100),
    };
    var task_ptrs: [producers.len]*anyopaque = undefined;
    for (producers, 0..) |producer, i| {
        const closure = alloc.lean_alloc_closure(producer, 1, 0);
        const task_obj = lean_task_spawn_core(closure, 0, false);
        rc.lean_inc(task_obj);
        task_ptrs[i] = task_obj;
    }
    defer {
        for (task_ptrs) |task_obj| {
            rc.lean_dec(task_obj);
        }
    }

    const list = makeTaskList(&task_ptrs);
    defer rc.lean_dec(list);

    const winner = lean_io_wait_any_core(list);
    try testing.expectEqual(task_ptrs[1], winner);
}

test "lean_io_promise_new returns a promise backed by a pending task" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    defer rc.lean_dec(promise_obj);

    const promise: *lean.lean_promise_object = @ptrCast(@alignCast(promise_obj));
    const task = promise.m_result orelse @panic("promise missing backing task");

    try testing.expectEqual(lean.LeanPromise, promise.m_header.m_tag);
    try testing.expectEqual(lean.LeanTask, task.m_header.m_tag);
    try testing.expectEqual(@as(?*anyopaque, null), @atomicLoad(?*anyopaque, &task.m_value, .seq_cst));
    try testing.expect(task.m_imp != null);
}

test "lean_io_promise_result_opt keeps the backing task alive and resolves to some" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    defer rc.lean_dec(promise_obj);

    const result_task_obj = lean_io_promise_result_opt(promise_obj);
    defer rc.lean_dec(result_task_obj);

    const unit = lean_io_promise_resolve(object.lean_box(7).?, promise_obj);
    try testing.expectEqual(object.lean_box(0), unit);
    try testing.expect(leanrt_test_runtime_task_wait(result_task_obj));

    const option = lean_task_get(result_task_obj);
    try testing.expect(!object.lean_is_scalar(option));
    try testing.expectEqual(@as(u8, 1), object.lean_obj_tag(option));
    try testing.expectEqual(@as(usize, 7), object.lean_unbox(ctor.lean_ctor_get(option, 0)));
}

test "dropping an unresolved promise resolves result_opt to none" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    const result_task_obj = lean_io_promise_result_opt(promise_obj);
    defer rc.lean_dec(result_task_obj);

    rc.lean_dec(promise_obj);
    try testing.expect(leanrt_test_runtime_task_wait(result_task_obj));
    try testing.expectEqual(object.lean_box(0), lean_task_get(result_task_obj));
}

test "lean_io_promise_resolve is idempotent and preserves the first resolved value" {
    try testing.expect(leanrt_test_runtime_task_manager_init(1));
    defer leanrt_test_runtime_task_manager_finalize();

    const promise_obj = lean_io_promise_new();
    defer rc.lean_dec(promise_obj);

    const result_task_obj = lean_io_promise_result_opt(promise_obj);
    defer rc.lean_dec(result_task_obj);

    _ = lean_io_promise_resolve(object.lean_box(11).?, promise_obj);
    _ = lean_io_promise_resolve(object.lean_box(13).?, promise_obj);
    try testing.expect(leanrt_test_runtime_task_wait(result_task_obj));

    const option = lean_task_get(result_task_obj);
    try testing.expect(!object.lean_is_scalar(option));
    try testing.expectEqual(@as(u8, 1), object.lean_obj_tag(option));
    try testing.expectEqual(@as(usize, 11), object.lean_unbox(ctor.lean_ctor_get(option, 0)));
}
