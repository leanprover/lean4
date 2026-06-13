const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const apply = @import("apply.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const sync = @import("sync.zig");

const Obj = ?*anyopaque;

var g_thunk_st_path_count = std.atomic.Value(usize).init(0);
var g_thunk_mt_path_count = std.atomic.Value(usize).init(0);
var g_thunk_mt_cas_success_count = std.atomic.Value(usize).init(0);
var g_thunk_mt_cas_fail_count = std.atomic.Value(usize).init(0);

fn thunkPtr(t: *anyopaque) *lean.lean_thunk_object {
    return @ptrCast(@alignCast(t));
}

fn opaqueFunPtr(fun: anytype) Obj {
    return @ptrCast(@constCast(fun));
}

fn closureSlot(thunk: *lean.lean_thunk_object) *sync.AtomicLeanPtr {
    return sync.atomicLeanPtr(&thunk.m_closure);
}

fn valueSlot(thunk: *lean.lean_thunk_object) *sync.AtomicLeanPtr {
    return sync.atomicLeanPtr(&thunk.m_value);
}

fn loadValueAcquire(thunk: *lean.lean_thunk_object) Obj {
    const bits = valueSlot(thunk).value.load(.acquire);
    return if (bits == 0) null else @ptrFromInt(bits);
}

fn storeValueRelease(thunk: *lean.lean_thunk_object, value: *anyopaque) void {
    valueSlot(thunk).value.store(@intFromPtr(value), .release);
}

fn markThunkValueShared(value: *anyopaque) void {
    if (!object.lean_is_scalar(value)) {
        rc.lean_mark_mt(value);
    }
}

fn waitForPublishedValue(thunk: *lean.lean_thunk_object) *anyopaque {
    while (true) {
        if (loadValueAcquire(thunk)) |value| return value;
        std.Thread.yield() catch {};
    }
}

fn thunkGetSt(thunk: *lean.lean_thunk_object) *anyopaque {
    _ = g_thunk_st_path_count.fetchAdd(1, .acq_rel);

    const closure = thunk.m_closure orelse {
        return thunk.m_value orelse @panic("single-thread thunk missing closure and value");
    };
    thunk.m_closure = null;

    const result = apply.lean_apply_1(closure, object.lean_box(0).?) orelse
        @panic("thunk closure returned null");
    std.debug.assert(thunk.m_value == null);
    thunk.m_value = result;
    return result;
}

fn thunkGetMt(thunk: *lean.lean_thunk_object) *anyopaque {
    _ = g_thunk_mt_path_count.fetchAdd(1, .acq_rel);

    while (true) {
        const current_bits = closureSlot(thunk).value.load(.acquire);
        if (current_bits != 0) {
            const closure: *anyopaque = @ptrFromInt(current_bits);
            if (closureSlot(thunk).value.cmpxchgStrong(current_bits, 0, .acq_rel, .acquire) == null) {
                _ = g_thunk_mt_cas_success_count.fetchAdd(1, .acq_rel);

                const result = apply.lean_apply_1(closure, object.lean_box(0).?) orelse
                    @panic("thunk closure returned null");
                markThunkValueShared(result);
                storeValueRelease(thunk, result);
                return result;
            }

            _ = g_thunk_mt_cas_fail_count.fetchAdd(1, .acq_rel);
            continue;
        }

        return waitForPublishedValue(thunk);
    }
}

export fn lean_thunk_get_core(t: *anyopaque) callconv(.c) *anyopaque {
    const thunk = thunkPtr(t);
    return if (thunk.m_header.m_rc <= 0) thunkGetMt(thunk) else thunkGetSt(thunk);
}

pub export fn leanrt_test_reset_thunk_debug_counters() callconv(.c) void {
    g_thunk_st_path_count.store(0, .release);
    g_thunk_mt_path_count.store(0, .release);
    g_thunk_mt_cas_success_count.store(0, .release);
    g_thunk_mt_cas_fail_count.store(0, .release);
}

pub export fn leanrt_test_get_thunk_st_path_count() callconv(.c) usize {
    return g_thunk_st_path_count.load(.acquire);
}

pub export fn leanrt_test_get_thunk_mt_path_count() callconv(.c) usize {
    return g_thunk_mt_path_count.load(.acquire);
}

pub export fn leanrt_test_get_thunk_mt_cas_success_count() callconv(.c) usize {
    return g_thunk_mt_cas_success_count.load(.acquire);
}

pub export fn leanrt_test_get_thunk_mt_cas_fail_count() callconv(.c) usize {
    return g_thunk_mt_cas_fail_count.load(.acquire);
}

fn allocThunk(closure: Obj) *lean.lean_thunk_object {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_thunk_object));
    const thunk: *lean.lean_thunk_object = @ptrCast(@alignCast(ptr));
    thunk.m_header = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanThunk,
    };
    thunk.m_value = null;
    thunk.m_closure = closure;
    return thunk;
}

var g_st_closure_calls = std.atomic.Value(usize).init(0);
var g_mt_closure_calls = std.atomic.Value(usize).init(0);

fn stThunkClosure(_: Obj) callconv(.c) Obj {
    _ = g_st_closure_calls.fetchAdd(1, .acq_rel);
    return object.lean_box(42);
}

fn mtThunkClosure(_: Obj) callconv(.c) Obj {
    _ = g_mt_closure_calls.fetchAdd(1, .acq_rel);
    return object.lean_box(77);
}

fn raceThunkGetter(thunk: *lean.lean_thunk_object, slot: *Obj) void {
    slot.* = lean_thunk_get_core(@ptrCast(thunk));
}

test "single-thread thunk force uses plain store path" {
    leanrt_test_reset_thunk_debug_counters();
    g_st_closure_calls.store(0, .release);

    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&stThunkClosure), 1, 0);
    const thunk = allocThunk(closure);
    defer rc.lean_dec(@ptrCast(thunk));

    const result = lean_thunk_get_core(@ptrCast(thunk));
    try testing.expectEqual(object.lean_box(42), result);
    try testing.expectEqual(@as(usize, 1), g_st_closure_calls.load(.acquire));
    try testing.expectEqual(@as(?*anyopaque, null), thunk.m_closure);
    try testing.expectEqual(result, thunk.m_value);
    try testing.expectEqual(@as(usize, 1), leanrt_test_get_thunk_st_path_count());
    try testing.expectEqual(@as(usize, 0), leanrt_test_get_thunk_mt_path_count());
}

test "multi-thread thunk force runs closure once and publishes shared value" {
    leanrt_test_reset_thunk_debug_counters();
    g_mt_closure_calls.store(0, .release);

    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&mtThunkClosure), 1, 0);
    const thunk = allocThunk(closure);
    defer rc.lean_dec(@ptrCast(thunk));
    rc.lean_mark_mt(@ptrCast(thunk));

    var results: [4]Obj = .{ null, null, null, null };
    var threads: [4]std.Thread = undefined;

    for (&threads, &results) |*thread, *result| {
        thread.* = try std.Thread.spawn(.{}, raceThunkGetter, .{ thunk, result });
    }
    for (threads) |thread| thread.join();

    for (results) |result| {
        try testing.expectEqual(object.lean_box(77), result);
    }
    try testing.expectEqual(@as(usize, 1), g_mt_closure_calls.load(.acquire));
    try testing.expectEqual(@as(?*anyopaque, null), thunk.m_closure);
    try testing.expectEqual(object.lean_box(77), thunk.m_value);
    try testing.expect(leanrt_test_get_thunk_mt_path_count() >= 1);
    try testing.expectEqual(@as(usize, 1), leanrt_test_get_thunk_mt_cas_success_count());
}
