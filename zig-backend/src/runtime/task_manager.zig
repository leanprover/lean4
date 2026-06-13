// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const apply = @import("apply.zig");
const ctor = @import("ctor.zig");
const interrupt_tls = @import("interrupt_tls.zig");
const io_min = @import("io_min.zig");
const rc = @import("rc.zig");
const sync = @import("sync.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const task_manager_export = @import("task_manager_export.zig");
const task_tls = @import("task_tls.zig");

const libc = struct {
    extern "c" fn getenv(name: [*:0]const u8) ?[*:0]u8;
    extern "c" fn setenv(name: [*:0]const u8, value: [*:0]const u8, overwrite: c_int) c_int;
    extern "c" fn unsetenv(name: [*:0]const u8) c_int;
};

/// `object.cpp` fixes the standard-priority queue indices to `0..8`.
/// Tasks above this threshold are routed to the dedicated-worker path, and
/// `LEAN_SYNC_PRIO` is a sentinel for immediate inline execution.
pub const LEAN_MAX_PRIO: usize = 8;
pub const LEAN_SYNC_PRIO: c_uint = std.math.maxInt(c_uint);
pub const priority_queue_count: usize = LEAN_MAX_PRIO + 1;

const RunKind = enum {
    @"inline",
    standard,
    dedicated,
};

/// C ABI snapshot for `tests/abi-smoke/task_pool_shape.c`.
pub const TaskManagerSnapshot = extern struct {
    queue_count: c_uint,
    lock_count: c_uint,
    condvar_count: c_uint,
    worker_count: c_uint,
    max_std_workers: c_uint,
    idle_workers: c_uint,
    dedicated_started: c_uint,
    dedicated_finished: c_uint,
    inline_runs: c_uint,
    standard_runs: c_uint,
    dedicated_runs: c_uint,
    max_prio_seen: c_uint,
    queue_lengths: [priority_queue_count]c_uint,
};

pub const RuntimeFinalizeSummary = extern struct {
    joined_standard_workers: c_uint,
    dedicated_started: c_uint,
    dedicated_finished: c_uint,
    pending_dedicated_workers: c_uint,
    saw_shutdown: bool,
    manager_active_after_finalize: bool,
};

pub const TaskMarkMtSnapshot = extern struct {
    dequeued_closures: c_uint,
    published_values: c_uint,
    all_dequeued_closures_marked: bool,
    all_published_values_marked: bool,
    last_dequeued_closure_rc: i32,
    last_published_value_rc: i32,
};

const TaskMarkMtState = struct {
    dequeued_closures: std.atomic.Value(c_uint) = .init(0),
    published_values: std.atomic.Value(c_uint) = .init(0),
    all_dequeued_closures_marked: std.atomic.Value(bool) = .init(true),
    all_published_values_marked: std.atomic.Value(bool) = .init(true),
    last_dequeued_closure_rc: std.atomic.Value(i32) = .init(0),
    last_published_value_rc: std.atomic.Value(i32) = .init(0),

    fn reset(self: *TaskMarkMtState) void {
        self.dequeued_closures.store(0, .seq_cst);
        self.published_values.store(0, .seq_cst);
        self.all_dequeued_closures_marked.store(true, .seq_cst);
        self.all_published_values_marked.store(true, .seq_cst);
        self.last_dequeued_closure_rc.store(0, .seq_cst);
        self.last_published_value_rc.store(0, .seq_cst);
    }

    fn noteDequeuedClosure(self: *TaskMarkMtState, closure: *anyopaque) void {
        const rc_value = @as(*lean.lean_object, @ptrCast(@alignCast(closure))).m_rc;
        _ = self.dequeued_closures.fetchAdd(1, .seq_cst);
        self.last_dequeued_closure_rc.store(rc_value, .seq_cst);
        if (rc_value >= 0) {
            self.all_dequeued_closures_marked.store(false, .seq_cst);
        }
    }

    fn notePublishedValue(self: *TaskMarkMtState, value: *anyopaque) void {
        if (object.lean_is_scalar(value)) {
            return;
        }
        const rc_value = @as(*lean.lean_object, @ptrCast(@alignCast(value))).m_rc;
        _ = self.published_values.fetchAdd(1, .seq_cst);
        self.last_published_value_rc.store(rc_value, .seq_cst);
        if (rc_value >= 0) {
            self.all_published_values_marked.store(false, .seq_cst);
        }
    }

    fn snapshot(self: *const TaskMarkMtState) TaskMarkMtSnapshot {
        return .{
            .dequeued_closures = self.dequeued_closures.load(.seq_cst),
            .published_values = self.published_values.load(.seq_cst),
            .all_dequeued_closures_marked = self.all_dequeued_closures_marked.load(.seq_cst),
            .all_published_values_marked = self.all_published_values_marked.load(.seq_cst),
            .last_dequeued_closure_rc = self.last_dequeued_closure_rc.load(.seq_cst),
            .last_published_value_rc = self.last_published_value_rc.load(.seq_cst),
        };
    }
};

var g_task_mark_mt_state = TaskMarkMtState{};

pub fn resetTaskMarkMtState() void {
    g_task_mark_mt_state.reset();
}

pub fn notePublishedValue(value: *anyopaque) void {
    g_task_mark_mt_state.notePublishedValue(value);
}

pub fn taskMarkMtSnapshot() TaskMarkMtSnapshot {
    return g_task_mark_mt_state.snapshot();
}

const SyntheticTask = struct {
    task: lean.lean_task_object,
    imp: lean.lean_task_imp,

    fn create(prio: c_uint) !*SyntheticTask {
        const synthetic = try std.heap.c_allocator.create(SyntheticTask);
        synthetic.* = .{
            .task = .{
                .m_header = .{
                    .m_rc = 1,
                    .m_cs_sz = 0,
                    .m_other = 0,
                    .m_tag = lean.LeanTask,
                },
                .m_value = null,
                .m_imp = &synthetic.imp,
            },
            .imp = .{
                .m_closure = null,
                .m_head_dep = null,
                .m_next_dep = null,
                .m_prio = prio,
                .m_canceled = 0,
                .m_keep_alive = 0,
                .m_deleted = 0,
            },
        };
        return synthetic;
    }

    fn destroy(self: *SyntheticTask) void {
        std.heap.c_allocator.destroy(self);
    }

    fn taskPtr(self: *SyntheticTask) *lean.lean_task_object {
        return &self.task;
    }

    fn fromTask(task: *lean.lean_task_object) *SyntheticTask {
        return @fieldParentPtr("task", task);
    }
};

fn closureSlots(o: *lean.lean_closure_object) [*]?*anyopaque {
    return @ptrCast(&o.m_objs);
}

fn pendingDependencyTask(closure: *anyopaque) *lean.lean_task_object {
    const closure_obj: *lean.lean_closure_object = @ptrCast(@alignCast(closure));
    const nested_task = closureSlots(closure_obj)[0] orelse @panic("pending bind closure missing nested task");
    if (object.lean_is_scalar(nested_task) or object.lean_ptr_tag(nested_task) != lean.LeanTask) {
        @panic("pending bind closure captured non-task dependency");
    }
    return @ptrCast(@alignCast(nested_task));
}

fn taskValue(task: *lean.lean_task_object) ?*anyopaque {
    return @atomicLoad(?*anyopaque, &task.m_value, .seq_cst);
}

fn freeTaskImp(imp: *lean.lean_task_imp) void {
    if (imp.m_closure) |closure| {
        rc.lean_dec(closure);
    }
    alloc.lean_free_small_object(@ptrCast(imp));
}

fn freeTaskObject(task: *lean.lean_task_object) void {
    if (task.m_imp) |imp| {
        freeTaskImp(imp);
        task.m_imp = null;
    } else if (taskValue(task)) |value| {
        rc.lean_dec(value);
    }
    alloc.noteTaskObjectFree();
    alloc.lean_free_small_object(@ptrCast(task));
}

fn waitAnyCheck(task_list: *anyopaque) ?*anyopaque {
    var it: *anyopaque = task_list;
    while (!object.lean_is_scalar(it)) {
        const head = ctor.lean_ctor_get(it, 0) orelse @panic("task list head missing task");
        if (taskValue(@ptrCast(@alignCast(head))) != null) {
            return head;
        }
        it = ctor.lean_ctor_get(it, 1) orelse @panic("task list tail missing");
    }
    return null;
}

pub const TaskManager = struct {
    allocator: std.mem.Allocator,
    m_mutex: sync.Mutex = .{},
    m_condvar: sync.Condvar = .{},
    m_dedicated_finished_cv: sync.Condvar = .{},
    /// Standard workers are created lazily. This array stays empty until the
    /// first non-`LEAN_SYNC_PRIO` task in the `0..LEAN_MAX_PRIO` range arrives.
    m_workers: std.ArrayList(std.Thread) = .empty,
    /// Foundation-only queue shape: indices `0..LEAN_MAX_PRIO` are standard
    /// worker priorities; `prio > LEAN_MAX_PRIO` routes to the dedicated path.
    m_priority_deques: [priority_queue_count]std.ArrayList(*lean.lean_task_object),
    m_queue_size: usize = 0,
    m_max_prio: usize = 0,
    m_idle_workers: usize = 0,
    m_max_std_workers: c_uint,
    m_num_dedicated_workers: usize = 0,
    m_dedicated_started: c_uint = 0,
    m_dedicated_finished: c_uint = 0,
    m_inline_runs: c_uint = 0,
    m_standard_runs: c_uint = 0,
    m_dedicated_runs: c_uint = 0,
    m_shutting_down: bool = false,

    pub fn create(allocator: std.mem.Allocator, max_std_workers: c_uint) !*TaskManager {
        const manager = try allocator.create(TaskManager);
        manager.* = .{
            .allocator = allocator,
            .m_priority_deques = undefined,
            .m_max_std_workers = max_std_workers,
        };
        for (&manager.m_priority_deques) |*queue| {
            queue.* = .empty;
        }
        return manager;
    }

    pub fn destroy(self: *TaskManager) RuntimeFinalizeSummary {
        self.shutdown();
        const joined_standard_workers: c_uint = @intCast(self.m_workers.items.len);
        for (self.m_workers.items) |*worker| {
            worker.join();
        }
        self.m_mutex.lock();
        while (self.m_num_dedicated_workers != 0) {
            self.m_dedicated_finished_cv.wait(&self.m_mutex);
        }
        const summary = RuntimeFinalizeSummary{
            .joined_standard_workers = joined_standard_workers,
            .dedicated_started = self.m_dedicated_started,
            .dedicated_finished = self.m_dedicated_finished,
            .pending_dedicated_workers = @intCast(self.m_num_dedicated_workers),
            .saw_shutdown = self.m_shutting_down,
            .manager_active_after_finalize = false,
        };
        self.m_mutex.unlock();
        self.m_workers.deinit(self.allocator);
        for (&self.m_priority_deques) |*queue| {
            queue.deinit(self.allocator);
        }
        self.m_dedicated_finished_cv.deinit();
        self.m_condvar.deinit();
        self.m_mutex.deinit();
        self.allocator.destroy(self);
        return summary;
    }

    pub fn snapshot(self: *TaskManager) TaskManagerSnapshot {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        var shape = TaskManagerSnapshot{
            .queue_count = priority_queue_count,
            .lock_count = 1,
            .condvar_count = 2,
            .worker_count = @intCast(self.m_workers.items.len),
            .max_std_workers = self.m_max_std_workers,
            .idle_workers = @intCast(self.m_idle_workers),
            .dedicated_started = self.m_dedicated_started,
            .dedicated_finished = self.m_dedicated_finished,
            .inline_runs = self.m_inline_runs,
            .standard_runs = self.m_standard_runs,
            .dedicated_runs = self.m_dedicated_runs,
            .max_prio_seen = @intCast(self.m_max_prio),
            .queue_lengths = [_]c_uint{0} ** priority_queue_count,
        };
        for (self.m_priority_deques, 0..) |queue, index| {
            shape.queue_lengths[index] = @intCast(queue.items.len);
        }
        return shape;
    }

    pub fn enqueue(self: *TaskManager, task: *lean.lean_task_object) !void {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        try self.enqueueLocked(task);
    }

    pub fn addDependency(self: *TaskManager, source: *lean.lean_task_object, dep: *lean.lean_task_object) !void {
        std.debug.assert(@atomicLoad(?*anyopaque, &dep.m_value, .seq_cst) == null);
        if (@atomicLoad(?*anyopaque, &source.m_value, .seq_cst) != null) {
            try self.enqueue(dep);
            return;
        }

        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        std.debug.assert(@atomicLoad(?*anyopaque, &dep.m_value, .seq_cst) == null);
        if (@atomicLoad(?*anyopaque, &source.m_value, .seq_cst) != null) {
            try self.enqueueLocked(dep);
            return;
        }

        const source_imp = source.m_imp orelse @panic("pending dependency source must have task imp");
        const dep_imp = dep.m_imp orelse @panic("pending dependency target must have task imp");
        dep_imp.m_next_dep = source_imp.m_head_dep;
        source_imp.m_head_dep = dep;
    }

    pub fn resolve(self: *TaskManager, task: *lean.lean_task_object, value: *anyopaque) void {
        if (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null) {
            rc.lean_dec(value);
            return;
        }

        self.m_mutex.lock();
        if (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null) {
            self.m_mutex.unlock();
            rc.lean_dec(value);
            return;
        }

        const imp = task.m_imp orelse {
            self.m_mutex.unlock();
            rc.lean_dec(value);
            return;
        };
        self.resolveTaskLocked(task, imp, value);
        self.m_mutex.unlock();
    }

    fn enqueueLocked(self: *TaskManager, task: *lean.lean_task_object) !void {
        const prio = task.m_imp.?.m_prio;
        if (prio == LEAN_SYNC_PRIO) {
            self.runTaskLocked(task, .@"inline");
            return;
        }
        if (prio > LEAN_MAX_PRIO) {
            try self.spawnDedicatedWorkerLocked(task);
            return;
        }

        const index: usize = @intCast(prio);
        if (index > self.m_max_prio) {
            self.m_max_prio = index;
        }
        try self.m_priority_deques[index].append(self.allocator, task);
        self.m_queue_size += 1;
        if (self.m_idle_workers == 0 and self.m_workers.items.len < self.m_max_std_workers) {
            try self.spawnStandardWorkerLocked();
        } else {
            self.m_condvar.signal();
        }
    }

    pub fn waitForCompletion(self: *TaskManager, task: *lean.lean_task_object) void {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        while (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) == null) {
            self.m_condvar.wait(&self.m_mutex);
        }
    }

    pub fn waitAny(self: *TaskManager, task_list: *anyopaque) *anyopaque {
        if (waitAnyCheck(task_list)) |winner| {
            return winner;
        }

        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        while (true) {
            if (waitAnyCheck(task_list)) |winner| {
                return winner;
            }
            self.m_condvar.wait(&self.m_mutex);
        }
    }

    pub fn waitForGet(self: *TaskManager, task: *lean.lean_task_object) void {
        if (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null) {
            return;
        }

        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        if (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null) {
            return;
        }

        const current = task_tls.get();
        const current_imp = if (current) |current_task| current_task.m_imp else null;
        if (current_imp != null and current_imp.?.m_prio == LEAN_SYNC_PRIO) {
            self.m_mutex.unlock();
            defer self.m_mutex.lock();
            io_min.lean_panic("`Task.get` called from a `(sync := true)` task", false);
            unreachable;
        }

        const in_pool = current_imp != null and current_imp.?.m_prio <= LEAN_MAX_PRIO;
        if (in_pool) {
            self.m_max_std_workers += 1;

            if (self.m_idle_workers == 0 and self.m_workers.items.len < self.m_max_std_workers) {
                self.spawnStandardWorkerLocked() catch @panic("failed to spawn replacement worker");
            } else if (self.m_idle_workers > 0) {
                self.m_condvar.signal();
            }
        }

        while (@atomicLoad(?*anyopaque, &task.m_value, .seq_cst) == null) {
            self.m_condvar.wait(&self.m_mutex);
        }

        if (in_pool) {
            self.m_max_std_workers -= 1;
        }
    }

    pub fn cancel(self: *TaskManager, task: *lean.lean_task_object) void {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        if (task.m_imp) |imp| {
            imp.m_canceled = 1;
        }
    }

    /// Test hook mirroring `object.cpp`'s deleted-task transition for a dropped
    /// continuation: mark the task deleted, release its continuation closure,
    /// but keep the task object alive until the scheduler or dependency owner
    /// observes the deleted state and frees it.
    pub fn markDeleted(self: *TaskManager, task: *lean.lean_task_object) bool {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        if (taskValue(task) != null) {
            return false;
        }
        const imp = task.m_imp orelse return false;
        if (imp.m_deleted != 0) {
            return true;
        }

        const closure = imp.m_closure;
        var it = imp.m_head_dep;
        imp.m_closure = null;
        imp.m_head_dep = null;
        imp.m_canceled = 1;
        imp.m_deleted = 1;

        self.m_mutex.unlock();
        defer self.m_mutex.lock();

        while (it) |dep| {
            const dep_imp = dep.m_imp orelse @panic("deleted dependent must remain pending");
            const next = dep_imp.m_next_dep;
            dep_imp.m_next_dep = null;
            freeTaskObject(dep);
            it = next;
        }
        if (closure) |value| {
            rc.lean_dec(value);
        }
        return true;
    }

    pub fn shuttingDown(self: *TaskManager) bool {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();
        return self.m_shutting_down;
    }

    pub fn getTaskState(self: *TaskManager, task: *lean.lean_task_object) u8 {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();

        if (task.m_imp) |imp| {
            return if (imp.m_closure != null) 0 else 1;
        }
        return 2;
    }

    fn shutdown(self: *TaskManager) void {
        self.m_mutex.lock();
        self.m_shutting_down = true;
        self.m_condvar.broadcast();
        self.m_mutex.unlock();
    }

    fn spawnStandardWorkerLocked(self: *TaskManager) !void {
        const worker = try std.Thread.spawn(.{}, standardWorkerMain, .{self});
        try self.m_workers.append(self.allocator, worker);
    }

    fn spawnDedicatedWorkerLocked(self: *TaskManager, task: *lean.lean_task_object) !void {
        self.m_num_dedicated_workers += 1;
        self.m_dedicated_started += 1;
        const worker = try std.Thread.spawn(.{}, dedicatedWorkerMain, .{ self, task });
        worker.detach();
    }

    fn standardWorkerMain(self: *TaskManager) void {
        self.m_mutex.lock();
        self.m_idle_workers += 1;
        defer {
            self.m_idle_workers -= 1;
            self.m_mutex.unlock();
        }

        while (true) {
            while (self.m_queue_size == 0 and !self.m_shutting_down) {
                self.m_condvar.wait(&self.m_mutex);
            }
            if (self.m_shutting_down and self.m_queue_size == 0) {
                break;
            }
            if (!self.m_shutting_down and self.m_workers.items.len - self.m_idle_workers >= self.m_max_std_workers) {
                self.m_condvar.wait(&self.m_mutex);
                continue;
            }
            const task = self.dequeueLocked() orelse continue;
            self.m_idle_workers -= 1;
            self.runTaskLocked(task, .standard);
            self.m_idle_workers += 1;
            interrupt_tls.resetHeartbeatAfterWorkerRun();
        }
    }

    fn dedicatedWorkerMain(self: *TaskManager, task: *lean.lean_task_object) void {
        self.m_mutex.lock();
        defer self.m_mutex.unlock();
        self.runTaskLocked(task, .dedicated);
        self.m_num_dedicated_workers -= 1;
        self.m_dedicated_finished += 1;
        self.m_dedicated_finished_cv.broadcast();
    }

    fn dequeueLocked(self: *TaskManager) ?*lean.lean_task_object {
        if (self.m_queue_size == 0) {
            return null;
        }

        var prio = self.m_max_prio;
        while (true) {
            var queue = &self.m_priority_deques[prio];
            if (queue.items.len > 0) {
                const task = queue.orderedRemove(0);
                self.m_queue_size -= 1;
                self.recomputeMaxPrioLocked();
                return task;
            }
            if (prio == 0) break;
            prio -= 1;
        }
        return null;
    }

    fn recomputeMaxPrioLocked(self: *TaskManager) void {
        var prio = self.m_max_prio;
        while (prio > 0 and self.m_priority_deques[prio].items.len == 0) {
            prio -= 1;
        }
        self.m_max_prio = prio;
    }

    fn runTaskLocked(self: *TaskManager, task: *lean.lean_task_object, kind: RunKind) void {
        switch (kind) {
            .@"inline" => self.m_inline_runs += 1,
            .standard => self.m_standard_runs += 1,
            .dedicated => self.m_dedicated_runs += 1,
        }

        const imp = task.m_imp orelse return;
        if (imp.m_deleted != 0) {
            freeTaskObject(task);
            return;
        }
        const closure = imp.m_closure;
        if (closure == null) {
            task.m_imp = null;
            @atomicStore(?*anyopaque, &task.m_value, object.lean_box(@intFromEnum(kind) + 1), .seq_cst);
            self.m_condvar.broadcast();
            return;
        }

        interrupt_tls.resetHeartbeatBeforeSpawn();
        defer interrupt_tls.resetHeartbeatAfterSpawn();

        g_task_mark_mt_state.noteDequeuedClosure(closure.?);
        imp.m_closure = null;
        const value = blk: {
            const prev_task = task_tls.swap(task);
            self.m_mutex.unlock();
            defer {
                _ = task_tls.swap(prev_task);
                self.m_mutex.lock();
            }
            break :blk apply.lean_apply_1(closure.?, object.lean_box(0).?);
        };
        if (imp.m_deleted != 0) {
            self.m_mutex.unlock();
            defer self.m_mutex.lock();
            if (value) |finished| {
                rc.lean_dec(finished);
            }
            freeTaskObject(task);
            return;
        }
        if (value) |finished| {
            self.resolveTaskLocked(task, imp, finished);
            return;
        }

        const rebound = imp.m_closure orelse @panic("pending task must reinstall its continuation closure");
        const nested_task = pendingDependencyTask(rebound);
        self.m_mutex.unlock();
        defer self.m_mutex.lock();
        self.addDependency(nested_task, task) catch @panic("failed to re-register pending bind dependency");
    }

    fn resolveTaskLocked(self: *TaskManager, task: *lean.lean_task_object, imp: *lean.lean_task_imp, value: *anyopaque) void {
        rc.lean_mark_mt(value);
        g_task_mark_mt_state.notePublishedValue(value);
        @atomicStore(?*anyopaque, &task.m_value, value, .seq_cst);
        task.m_imp = null;
        self.handleFinishedLocked(imp);
        alloc.lean_free_small_object(@ptrCast(imp));
        self.m_condvar.broadcast();
    }

    fn handleFinishedLocked(self: *TaskManager, imp: *lean.lean_task_imp) void {
        var it = imp.m_head_dep;
        imp.m_head_dep = null;
        while (it) |dep| {
            const dep_imp = dep.m_imp orelse @panic("dependent task must remain pending");
            if (imp.m_canceled != 0) {
                dep_imp.m_canceled = 1;
            }
            const next = dep_imp.m_next_dep;
            dep_imp.m_next_dep = null;
            if (dep_imp.m_deleted != 0) {
                freeTaskObject(dep);
            } else {
                self.enqueueLocked(dep) catch @panic("failed to enqueue dependent task");
            }
            it = next;
        }
    }
};

const ContentionState = struct {
    manager: *TaskManager,
    expected_waiters: usize,
    waiting: usize = 0,
    awakened: usize = 0,
    broadcaster_ran: bool = false,
    ready: bool = false,
};

fn contentionWaiter(state: *ContentionState) void {
    state.manager.m_mutex.lock();
    defer state.manager.m_mutex.unlock();

    state.waiting += 1;
    state.manager.m_condvar.broadcast();
    while (!state.ready) {
        state.manager.m_condvar.wait(&state.manager.m_mutex);
    }
    state.awakened += 1;
}

fn contentionBroadcaster(state: *ContentionState) void {
    state.manager.m_mutex.lock();
    defer state.manager.m_mutex.unlock();

    while (state.waiting < state.expected_waiters) {
        state.manager.m_condvar.wait(&state.manager.m_mutex);
    }
    state.ready = true;
    state.broadcaster_ran = true;
    state.manager.m_condvar.broadcast();
}

var g_test_manager: ?*TaskManager = null;
var g_runtime_manager: ?*TaskManager = null;
var g_last_runtime_finalize_summary = RuntimeFinalizeSummary{
    .joined_standard_workers = 0,
    .dedicated_started = 0,
    .dedicated_finished = 0,
    .pending_dedicated_workers = 0,
    .saw_shutdown = false,
    .manager_active_after_finalize = false,
};

pub fn defaultWorkerCount() c_uint {
    return @intCast(std.Thread.getCpuCount() catch 1);
}

fn parseWorkerCount(raw: []const u8) c_uint {
    return std.fmt.parseUnsigned(c_uint, raw, 10) catch defaultWorkerCount();
}

pub fn maxStdWorkersFromEnv() c_uint {
    const raw = libc.getenv("LEAN_NUM_THREADS") orelse return defaultWorkerCount();
    const slice = std.mem.span(raw);
    if (slice.len == 0) {
        return defaultWorkerCount();
    }
    return parseWorkerCount(slice);
}

fn ensureTestManager(max_std_workers: c_uint) bool {
    if (g_test_manager != null) {
        return true;
    }
    g_test_manager = TaskManager.create(std.heap.c_allocator, max_std_workers) catch return false;
    return true;
}

fn withSyntheticTask(prio: c_uint, comptime runner: fn (*TaskManager, *lean.lean_task_object) bool) bool {
    const manager = g_test_manager orelse return false;
    const synthetic = SyntheticTask.create(prio) catch return false;
    defer synthetic.destroy();
    return runner(manager, synthetic.taskPtr());
}

fn runSyntheticTaskAndWait(manager: *TaskManager, task: *lean.lean_task_object) bool {
    const prio = task.m_imp.?.m_prio;
    if (prio <= LEAN_MAX_PRIO and prio != LEAN_SYNC_PRIO and manager.m_max_std_workers == 0) {
        return false;
    }
    manager.enqueue(task) catch return false;
    manager.waitForCompletion(task);
    return @atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null;
}

pub fn createRuntimeManager(num_workers: c_uint) bool {
    destroyRuntimeManager();
    if (num_workers == 0) {
        task_manager_export.set(null);
        return true;
    }
    g_runtime_manager = TaskManager.create(std.heap.c_allocator, num_workers) catch return false;
    task_manager_export.set(@ptrCast(g_runtime_manager));
    return true;
}

pub fn destroyRuntimeManager() void {
    g_last_runtime_finalize_summary = .{
        .joined_standard_workers = 0,
        .dedicated_started = 0,
        .dedicated_finished = 0,
        .pending_dedicated_workers = 0,
        .saw_shutdown = false,
        .manager_active_after_finalize = false,
    };
    if (g_runtime_manager) |manager| {
        g_last_runtime_finalize_summary = manager.destroy();
        g_runtime_manager = null;
    }
    task_manager_export.set(null);
}

pub fn runtimeManager() ?*TaskManager {
    return g_runtime_manager;
}

pub fn waitForRuntimeTask(task: *lean.lean_task_object) bool {
    const manager = g_runtime_manager orelse return false;
    manager.waitForCompletion(task);
    return @atomicLoad(?*anyopaque, &task.m_value, .seq_cst) != null;
}

pub export fn leanrt_test_task_manager_reset() callconv(.c) void {
    if (g_test_manager) |manager| {
        _ = manager.destroy();
        g_test_manager = null;
    }
}

pub export fn leanrt_test_task_manager_default_worker_count() callconv(.c) c_uint {
    return defaultWorkerCount();
}

pub export fn leanrt_test_task_manager_init_from_env() callconv(.c) bool {
    return ensureTestManager(maxStdWorkersFromEnv());
}

pub export fn leanrt_test_runtime_task_manager_snapshot(out: *TaskManagerSnapshot) callconv(.c) void {
    out.* = if (g_runtime_manager) |manager|
        manager.snapshot()
    else
        .{
            .queue_count = priority_queue_count,
            .lock_count = 0,
            .condvar_count = 0,
            .worker_count = 0,
            .max_std_workers = 0,
            .idle_workers = 0,
            .dedicated_started = 0,
            .dedicated_finished = 0,
            .inline_runs = 0,
            .standard_runs = 0,
            .dedicated_runs = 0,
            .max_prio_seen = 0,
            .queue_lengths = [_]c_uint{0} ** priority_queue_count,
        };
}

pub export fn leanrt_test_runtime_task_mark_deleted(task: *anyopaque) callconv(.c) bool {
    const manager = g_runtime_manager orelse return false;
    return manager.markDeleted(@ptrCast(@alignCast(task)));
}

pub export fn leanrt_test_runtime_task_manager_last_finalize_summary(out: *RuntimeFinalizeSummary) callconv(.c) void {
    out.* = g_last_runtime_finalize_summary;
}

pub export fn leanrt_test_task_mark_mt_reset() callconv(.c) void {
    resetTaskMarkMtState();
}

pub export fn leanrt_test_task_mark_mt_snapshot(out: *TaskMarkMtSnapshot) callconv(.c) void {
    out.* = g_task_mark_mt_state.snapshot();
}

pub export fn leanrt_test_task_manager_snapshot(out: *TaskManagerSnapshot) callconv(.c) void {
    out.* = if (g_test_manager) |manager|
        manager.snapshot()
    else
        .{
            .queue_count = priority_queue_count,
            .lock_count = 0,
            .condvar_count = 0,
            .worker_count = 0,
            .max_std_workers = 0,
            .idle_workers = 0,
            .dedicated_started = 0,
            .dedicated_finished = 0,
            .inline_runs = 0,
            .standard_runs = 0,
            .dedicated_runs = 0,
            .max_prio_seen = 0,
            .queue_lengths = [_]c_uint{0} ** priority_queue_count,
        };
}

pub export fn leanrt_test_task_manager_spawn_sync_task() callconv(.c) bool {
    return withSyntheticTask(LEAN_SYNC_PRIO, runSyntheticTaskAndWait);
}

pub export fn leanrt_test_task_manager_spawn_standard_task(prio: c_uint) callconv(.c) bool {
    return withSyntheticTask(prio, runSyntheticTaskAndWait);
}

pub export fn leanrt_test_task_manager_spawn_dedicated_task(prio: c_uint) callconv(.c) bool {
    return withSyntheticTask(prio, runSyntheticTaskAndWait);
}

pub export fn leanrt_test_task_manager_contention_smoke(thread_count: c_uint) callconv(.c) bool {
    const manager = g_test_manager orelse return false;
    if (thread_count < 2) {
        return false;
    }

    var state = ContentionState{
        .manager = manager,
        .expected_waiters = thread_count - 1,
    };
    var threads: std.ArrayList(std.Thread) = .empty;
    defer threads.deinit(std.heap.c_allocator);

    var i: usize = 0;
    while (i < state.expected_waiters) : (i += 1) {
        const waiter = std.Thread.spawn(.{}, contentionWaiter, .{&state}) catch return false;
        threads.append(std.heap.c_allocator, waiter) catch return false;
    }

    const broadcaster = std.Thread.spawn(.{}, contentionBroadcaster, .{&state}) catch return false;
    threads.append(std.heap.c_allocator, broadcaster) catch return false;

    for (threads.items) |*thread_handle| {
        thread_handle.join();
    }

    return state.broadcaster_ran and state.awakened == state.expected_waiters;
}

pub export fn leanrt_test_task_manager_finalize() callconv(.c) void {
    leanrt_test_task_manager_reset();
}

const EnvSnapshot = struct {
    value: ?[:0]u8,
};

fn captureLeanNumThreadsEnv() !EnvSnapshot {
    const current = libc.getenv("LEAN_NUM_THREADS");
    if (current) |value| {
        return .{ .value = try testing.allocator.dupeZ(u8, std.mem.span(value)) };
    }
    return .{ .value = null };
}

fn restoreLeanNumThreadsEnv(snapshot: EnvSnapshot) !void {
    defer if (snapshot.value) |value| testing.allocator.free(value);
    if (snapshot.value) |value| {
        if (libc.setenv("LEAN_NUM_THREADS", value.ptr, 1) != 0) {
            return error.SetEnvFailed;
        }
    } else if (libc.unsetenv("LEAN_NUM_THREADS") != 0) {
        return error.UnsetEnvFailed;
    }
}

test "foundation exposes nine priority queues and one lock pair" {
    const snapshot = try captureLeanNumThreadsEnv();
    defer restoreLeanNumThreadsEnv(snapshot) catch @panic("failed to restore LEAN_NUM_THREADS");
    if (libc.unsetenv("LEAN_NUM_THREADS") != 0) return error.UnsetEnvFailed;

    leanrt_test_task_manager_reset();
    defer leanrt_test_task_manager_finalize();
    try testing.expect(leanrt_test_task_manager_init_from_env());

    var shape: TaskManagerSnapshot = undefined;
    leanrt_test_task_manager_snapshot(&shape);

    try testing.expectEqual(@as(c_uint, priority_queue_count), shape.queue_count);
    try testing.expectEqual(@as(c_uint, 1), shape.lock_count);
    try testing.expectEqual(@as(c_uint, 2), shape.condvar_count);
    try testing.expectEqual(@as(c_uint, 0), shape.worker_count);
    try testing.expectEqual(defaultWorkerCount(), shape.max_std_workers);
    for (shape.queue_lengths) |len| {
        try testing.expectEqual(@as(c_uint, 0), len);
    }
}

test "LEAN_NUM_THREADS override is honored" {
    const snapshot = try captureLeanNumThreadsEnv();
    defer restoreLeanNumThreadsEnv(snapshot) catch @panic("failed to restore LEAN_NUM_THREADS");
    if (libc.setenv("LEAN_NUM_THREADS", "4", 1) != 0) return error.SetEnvFailed;

    leanrt_test_task_manager_reset();
    defer leanrt_test_task_manager_finalize();
    try testing.expect(leanrt_test_task_manager_init_from_env());

    var shape: TaskManagerSnapshot = undefined;
    leanrt_test_task_manager_snapshot(&shape);
    try testing.expectEqual(@as(c_uint, 4), shape.max_std_workers);
}

test "sync priority runs inline and standard workers stay lazy until needed" {
    const snapshot = try captureLeanNumThreadsEnv();
    defer restoreLeanNumThreadsEnv(snapshot) catch @panic("failed to restore LEAN_NUM_THREADS");
    if (libc.setenv("LEAN_NUM_THREADS", "1", 1) != 0) return error.SetEnvFailed;

    leanrt_test_task_manager_reset();
    defer leanrt_test_task_manager_finalize();
    try testing.expect(leanrt_test_task_manager_init_from_env());
    try testing.expect(leanrt_test_task_manager_spawn_sync_task());

    var shape: TaskManagerSnapshot = undefined;
    leanrt_test_task_manager_snapshot(&shape);
    try testing.expectEqual(@as(c_uint, 0), shape.worker_count);
    try testing.expectEqual(@as(c_uint, 1), shape.inline_runs);

    try testing.expect(leanrt_test_task_manager_spawn_standard_task(0));
    leanrt_test_task_manager_snapshot(&shape);
    try testing.expectEqual(@as(c_uint, 1), shape.worker_count);
    try testing.expectEqual(@as(c_uint, 1), shape.standard_runs);
}

test "priority above max uses a dedicated worker independent of standard worker count" {
    const snapshot = try captureLeanNumThreadsEnv();
    defer restoreLeanNumThreadsEnv(snapshot) catch @panic("failed to restore LEAN_NUM_THREADS");
    if (libc.setenv("LEAN_NUM_THREADS", "0", 1) != 0) return error.SetEnvFailed;

    leanrt_test_task_manager_reset();
    defer leanrt_test_task_manager_finalize();
    try testing.expect(leanrt_test_task_manager_init_from_env());
    try testing.expect(leanrt_test_task_manager_spawn_dedicated_task(LEAN_MAX_PRIO + 1));

    var shape: TaskManagerSnapshot = undefined;
    leanrt_test_task_manager_snapshot(&shape);
    try testing.expectEqual(@as(c_uint, 0), shape.max_std_workers);
    try testing.expectEqual(@as(c_uint, 0), shape.worker_count);
    try testing.expectEqual(@as(c_uint, 1), shape.dedicated_started);
    try testing.expectEqual(@as(c_uint, 1), shape.dedicated_finished);
    try testing.expectEqual(@as(c_uint, 1), shape.dedicated_runs);
}

test "single mutex and condvar survive eight-thread contention" {
    const snapshot = try captureLeanNumThreadsEnv();
    defer restoreLeanNumThreadsEnv(snapshot) catch @panic("failed to restore LEAN_NUM_THREADS");
    if (libc.setenv("LEAN_NUM_THREADS", "1", 1) != 0) return error.SetEnvFailed;

    leanrt_test_task_manager_reset();
    defer leanrt_test_task_manager_finalize();
    try testing.expect(leanrt_test_task_manager_init_from_env());
    try testing.expect(leanrt_test_task_manager_contention_smoke(8));
}

test "runtime manager export follows lifecycle" {
    destroyRuntimeManager();
    defer destroyRuntimeManager();

    try testing.expect(createRuntimeManager(2));
    try testing.expect(task_manager_export.get() != null);

    destroyRuntimeManager();
    try testing.expect(task_manager_export.get() == null);
}
