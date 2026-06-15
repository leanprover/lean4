// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

// `lean_ref_object` is ABI-pinned to 16 bytes, so the MT synchronization state
// lives out-of-line. A single runtime mutex is sufficient for the current M3
// contract and keeps the public layout identical to `lean.h`.
var g_mt_ref_mutex: std.Io.Mutex = .init;

fn header(o: *anyopaque) *lean.lean_object {
    return @ptrCast(@alignCast(o));
}

fn asRef(o: *anyopaque) *lean.lean_ref_object {
    return @ptrCast(@alignCast(o));
}

fn refMaybeMt(ref: *anyopaque) bool {
    const m_rc = header(ref).m_rc;
    return m_rc < 0 or m_rc == 0;
}

fn mtTakeValue(ref: *anyopaque) ?*anyopaque {
    g_mt_ref_mutex.lockUncancelable(std.Options.debug_io);
    defer g_mt_ref_mutex.unlock(std.Options.debug_io);
    const ref_obj = asRef(ref);
    const value = ref_obj.m_value;
    ref_obj.m_value = null;
    return value;
}

fn mtGetValue(ref: *anyopaque) *anyopaque {
    g_mt_ref_mutex.lockUncancelable(std.Options.debug_io);
    defer g_mt_ref_mutex.unlock(std.Options.debug_io);
    return asRef(ref).m_value orelse @panic("null reference read");
}

fn mtSetValue(ref: *anyopaque, new_value: *anyopaque) ?*anyopaque {
    g_mt_ref_mutex.lockUncancelable(std.Options.debug_io);
    defer g_mt_ref_mutex.unlock(std.Options.debug_io);
    const ref_obj = asRef(ref);
    const old_value = ref_obj.m_value;
    ref_obj.m_value = new_value;
    return old_value;
}

fn mtSwapValue(ref: *anyopaque, new_value: *anyopaque) *anyopaque {
    g_mt_ref_mutex.lockUncancelable(std.Options.debug_io);
    defer g_mt_ref_mutex.unlock(std.Options.debug_io);
    const ref_obj = asRef(ref);
    const old_value = ref_obj.m_value orelse @panic("null reference read");
    ref_obj.m_value = new_value;
    return old_value;
}

fn makeRef(initial: ?*anyopaque) *anyopaque {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_ref_object));
    const ref_obj = asRef(ptr);
    ref_obj.* = .{
        .m_header = .{
            .m_rc = 1,
            .m_cs_sz = 0,
            .m_other = 0,
            .m_tag = lean.LeanRef,
        },
        .m_value = initial,
    };
    return ptr;
}

fn expectRefValue(ref: *anyopaque) *anyopaque {
    return asRef(ref).m_value orelse @panic("null reference read");
}

fn makePlainObject() *anyopaque {
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_object));
    header(ptr).* = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = 0,
    };
    return ptr;
}

pub export fn lean_st_ref_reset(ref: *anyopaque) callconv(.c) *anyopaque {
    const old_value = if (refMaybeMt(ref))
        mtTakeValue(ref)
    else blk: {
        const ref_obj = asRef(ref);
        const value = ref_obj.m_value;
        ref_obj.m_value = null;
        break :blk value;
    };

    if (old_value) |value| {
        rc.lean_dec(value);
    }

    return object.lean_box(0).?;
}

pub export fn lean_st_mk_ref(value: *anyopaque) callconv(.c) *anyopaque {
    return makeRef(value);
}

pub export fn lean_st_ref_get(ref: *anyopaque) callconv(.c) *anyopaque {
    const value = if (refMaybeMt(ref))
        mtGetValue(ref)
    else
        expectRefValue(ref);

    rc.lean_inc(value);
    return value;
}

pub export fn lean_st_ref_take(ref: *anyopaque) callconv(.c) *anyopaque {
    if (refMaybeMt(ref)) {
        while (true) {
            if (mtTakeValue(ref)) |value| return value;
        }
    }
    const ref_obj = asRef(ref);
    const value = ref_obj.m_value orelse @panic("null reference read");
    ref_obj.m_value = null;
    return value;
}

pub export fn lean_st_ref_set(ref: *anyopaque, value: *anyopaque) callconv(.c) *anyopaque {
    const old_value = if (refMaybeMt(ref)) blk: {
        rc.lean_mark_mt(value);
        break :blk mtSetValue(ref, value);
    } else blk: {
        const ref_obj = asRef(ref);
        const old = ref_obj.m_value;
        ref_obj.m_value = value;
        break :blk old;
    };

    if (old_value) |old| {
        rc.lean_dec(old);
    }

    return object.lean_box(0).?;
}

pub export fn lean_st_ref_swap(ref: *anyopaque, value: *anyopaque) callconv(.c) *anyopaque {
    if (refMaybeMt(ref)) {
        rc.lean_mark_mt(value);
        return mtSwapValue(ref, value);
    }

    const ref_obj = asRef(ref);
    const old_value = ref_obj.m_value orelse @panic("null reference read");
    ref_obj.m_value = value;
    return old_value;
}

pub export fn lean_st_ref_ptr_eq(ref1: *anyopaque, ref2: *anyopaque) callconv(.c) u8 {
    return @intFromBool(asRef(ref1) == asRef(ref2));
}

test "lean_ref_object layout matches lean.h" {
    try testing.expectEqual(@as(usize, 16), @sizeOf(lean.lean_ref_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_ref_object, "m_value"));
}

test "lean_st_ref_reset clears a single-threaded ref and decrements its value" {
    const value = makePlainObject();
    const ref = makeRef(value);
    defer alloc.lean_free_object(ref);

    alloc.resetTestCounters();
    const result = lean_st_ref_reset(ref);

    try testing.expectEqual(object.lean_box(0), result);
    try testing.expectEqual(@as(?*anyopaque, null), asRef(ref).m_value);
    try testing.expectEqual(@as(usize, 1), alloc.testFreeCount());
}

test "lean_st_ref_reset clears a multi-threaded ref and decrements its value" {
    const value = makePlainObject();
    const ref = makeRef(value);
    defer alloc.lean_free_object(ref);

    rc.lean_mark_mt(ref);
    try testing.expect(refMaybeMt(ref));

    alloc.resetTestCounters();
    const result = lean_st_ref_reset(ref);

    try testing.expectEqual(object.lean_box(0), result);
    try testing.expectEqual(@as(?*anyopaque, null), asRef(ref).m_value);
    try testing.expectEqual(@as(usize, 1), alloc.testFreeCount());
}

test "lean_st_mk_ref creates a LeanRef cell with the provided value" {
    const value = makePlainObject();
    const ref = lean_st_mk_ref(value);
    defer {
        _ = lean_st_ref_reset(ref);
        alloc.lean_free_object(ref);
    }

    try testing.expectEqual(@as(i32, 1), header(ref).m_rc);
    try testing.expectEqual(@as(u8, lean.LeanRef), header(ref).m_tag);
    try testing.expectEqual(@as(?*anyopaque, value), asRef(ref).m_value);
}

test "lean_st_ref_get set and swap round trip in the single-threaded path" {
    const initial = makePlainObject();
    const ref = makeRef(initial);
    defer alloc.lean_free_object(ref);

    const got = lean_st_ref_get(ref);
    try testing.expectEqual(initial, got);
    try testing.expectEqual(@as(i32, 2), header(initial).m_rc);
    rc.lean_dec(got);
    try testing.expectEqual(@as(i32, 1), header(initial).m_rc);

    const next = makePlainObject();
    alloc.resetTestCounters();
    const set_result = lean_st_ref_set(ref, next);
    try testing.expectEqual(object.lean_box(0), set_result);
    try testing.expectEqual(next, expectRefValue(ref));
    try testing.expectEqual(@as(usize, 1), alloc.testFreeCount());

    const replacement = makePlainObject();
    const swapped = lean_st_ref_swap(ref, replacement);
    try testing.expectEqual(next, swapped);
    try testing.expectEqual(replacement, expectRefValue(ref));
    rc.lean_dec(swapped);
    try testing.expectEqual(@as(usize, 2), alloc.testFreeCount());

    _ = lean_st_ref_reset(ref);
    try testing.expectEqual(@as(?*anyopaque, null), asRef(ref).m_value);
    try testing.expectEqual(@as(usize, 3), alloc.testFreeCount());
}

test "lean_st_ref helpers use the marked MT path without panicking" {
    const initial = makePlainObject();
    const ref = makeRef(initial);
    defer alloc.lean_free_object(ref);

    rc.lean_mark_mt(ref);
    try testing.expect(refMaybeMt(ref));
    try testing.expectEqual(@as(i32, -1), header(initial).m_rc);

    const got = lean_st_ref_get(ref);
    try testing.expectEqual(initial, got);
    rc.lean_dec(got);

    const next = makePlainObject();
    const set_result = lean_st_ref_set(ref, next);
    try testing.expectEqual(object.lean_box(0), set_result);
    try testing.expectEqual(@as(i32, -1), header(next).m_rc);
    try testing.expectEqual(next, expectRefValue(ref));

    const replacement = makePlainObject();
    const swapped = lean_st_ref_swap(ref, replacement);
    try testing.expectEqual(next, swapped);
    try testing.expectEqual(@as(i32, -1), header(replacement).m_rc);
    try testing.expectEqual(replacement, expectRefValue(ref));
    rc.lean_dec(swapped);

    _ = lean_st_ref_reset(ref);
    try testing.expectEqual(@as(?*anyopaque, null), asRef(ref).m_value);
}
