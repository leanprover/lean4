// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const string = @import("string.zig");

const Obj = ?*anyopaque;
const max_direct_args = 16;
const Fn1 = *const fn (Obj) callconv(.c) Obj;
const Fn2 = *const fn (Obj, Obj) callconv(.c) Obj;
const Fn3 = *const fn (Obj, Obj, Obj) callconv(.c) Obj;
const Fn4 = *const fn (Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn5 = *const fn (Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn6 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn7 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn8 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn9 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn10 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn11 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn12 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn13 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn14 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn15 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn16 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fnn = *const fn ([*]Obj) callconv(.c) Obj;

fn opaqueFunPtr(fun: anytype) ?*anyopaque {
    return @ptrCast(@constCast(fun));
}

fn box(n: usize) *anyopaque {
    return object.lean_box(n).?;
}

fn header(o: *anyopaque) *lean.lean_object {
    return @ptrCast(@alignCast(o));
}

fn closurePtr(o: *anyopaque) *lean.lean_closure_object {
    return @ptrCast(@alignCast(o));
}

fn closureSlots(o: *lean.lean_closure_object) [*]Obj {
    return @ptrCast(&o.m_objs);
}

fn castFun(comptime F: type, raw: Obj) F {
    return @ptrFromInt(@intFromPtr(raw orelse @panic("null closure function")));
}

fn stringBytes(msg: *anyopaque) []const u8 {
    const str: *lean.lean_string_object = @ptrCast(@alignCast(msg));
    const bytes: [*]const u8 = @ptrCast(&str.m_data);
    return bytes[0 .. str.m_size - 1];
}

fn writeStderr(bytes: []const u8) void {
    std.Io.File.writeStreamingAll(std.Io.File.stderr(), std.Options.debug_io, bytes) catch {};
}

fn writeTrace(prefix: []const u8, msg: *anyopaque) void {
    writeStderr(prefix);
    writeStderr(stringBytes(msg));
    writeStderr("\n");
}

fn initCallArgs(arity: usize, stack: *[max_direct_args]Obj) []Obj {
    if (arity <= max_direct_args) return stack[0..arity];
    return std.heap.page_allocator.alloc(Obj, arity) catch @panic("out of memory");
}

fn deinitCallArgs(arity: usize, args: []Obj) void {
    if (arity > max_direct_args) std.heap.page_allocator.free(args);
}

fn copyExistingFixed(target: []Obj, source: [*]Obj, fixed: usize, exclusive: bool) void {
    for (0..fixed) |i| {
        const value = source[i];
        if (!exclusive) rc.lean_inc(value);
        target[i] = value;
    }
}

fn callFunction(fun: Obj, args: []const Obj) Obj {
    return switch (args.len) {
        1 => castFun(Fn1, fun)(args[0]),
        2 => castFun(Fn2, fun)(args[0], args[1]),
        3 => castFun(Fn3, fun)(args[0], args[1], args[2]),
        4 => castFun(Fn4, fun)(args[0], args[1], args[2], args[3]),
        5 => castFun(Fn5, fun)(args[0], args[1], args[2], args[3], args[4]),
        6 => castFun(Fn6, fun)(args[0], args[1], args[2], args[3], args[4], args[5]),
        7 => castFun(Fn7, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]),
        8 => castFun(Fn8, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]),
        9 => castFun(Fn9, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8]),
        10 => castFun(Fn10, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9]),
        11 => castFun(Fn11, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10]),
        12 => castFun(Fn12, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11]),
        13 => castFun(Fn13, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12]),
        14 => castFun(Fn14, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13]),
        15 => castFun(Fn15, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14]),
        16 => castFun(Fn16, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15]),
        else => castFun(Fnn, fun)(@constCast(args.ptr)),
    };
}

fn runThunk(fn_obj: *anyopaque) ?*anyopaque {
    if (object.lean_is_scalar(fn_obj)) return fn_obj;

    const closure = closurePtr(fn_obj);
    const arity: usize = closure.m_arity;
    const fixed: usize = closure.m_num_fixed;
    std.debug.assert(fixed + 1 == arity);

    var stack: [max_direct_args]Obj = undefined;
    const args = initCallArgs(arity, &stack);
    defer deinitCallArgs(arity, args);

    const exclusive = rc.lean_is_exclusive(fn_obj);
    copyExistingFixed(args, closureSlots(closure), fixed, exclusive);
    args[fixed] = box(0);

    const result = callFunction(closure.m_fun, args);
    if (exclusive) {
        alloc.lean_free_object(fn_obj);
    } else {
        rc.lean_dec_ref(fn_obj);
    }
    return result;
}

fn makeTestObject(rc_value: i32) *anyopaque {
    const value = alloc.lean_alloc_object(@sizeOf(lean.lean_object));
    header(value).* = .{
        .m_rc = rc_value,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = 0,
    };
    return value;
}

var g_sleep_count: usize = 0;

fn sleepThunk(unit: ?*anyopaque) callconv(.c) ?*anyopaque {
    std.debug.assert(unit == box(0));
    g_sleep_count += 1;
    return box(7);
}

export fn lean_dbg_trace(s: *anyopaque, fn_obj: *anyopaque) callconv(.c) ?*anyopaque {
    writeTrace("", s);
    rc.lean_dec(s);
    return runThunk(fn_obj);
}

export fn lean_dbg_sleep(ms: u32, fn_obj: *anyopaque) callconv(.c) ?*anyopaque {
    std.Io.sleep(std.Options.debug_io, .fromMilliseconds(@as(i64, ms)), .awake) catch {};
    return runThunk(fn_obj);
}

export fn lean_dbg_trace_if_shared(s: *anyopaque, a: *anyopaque) callconv(.c) ?*anyopaque {
    if (!object.lean_is_scalar(a) and rc.lean_is_shared(a)) {
        writeTrace("shared RC ", s);
    }
    rc.lean_dec(s);
    return a;
}

test "lean_dbg_sleep waits and returns thunk value" {
    g_sleep_count = 0;
    const thunk = alloc.lean_alloc_closure(opaqueFunPtr(&sleepThunk), 1, 0);
    const result = lean_dbg_sleep(1, thunk);

    try testing.expectEqual(box(7), result);
    try testing.expectEqual(@as(usize, 1), g_sleep_count);
}

test "lean_dbg_trace_if_shared returns exclusive values unchanged" {
    const msg = string.mkAsciiStringBytes("shared-value");
    const value = makeTestObject(1);
    const result = lean_dbg_trace_if_shared(msg, value);
    defer alloc.lean_free_object(value);

    try testing.expectEqual(value, result);
}
