// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const init = @import("init.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");

const user_error_tag: c_uint = 18;

fn asString(msg: *anyopaque) *lean.lean_string_object {
    return @ptrCast(@alignCast(msg));
}

fn stringBytes(msg: *anyopaque) []const u8 {
    const str = asString(msg);
    const size = if (str.m_size == 0) 0 else str.m_size - 1;
    const bytes: [*]const u8 = @ptrCast(&str.m_data);
    return bytes[0..size];
}

fn resultTag(r: *anyopaque) u8 {
    return @as(u8, @truncate(object.lean_ptr_tag(r)));
}

fn maybeStringMessage(value: ?*anyopaque) ?[]const u8 {
    const ptr = value orelse return null;
    if (object.lean_is_scalar(ptr)) return null;
    if (object.lean_obj_tag(ptr) != lean.LeanString) return null;
    return stringBytes(ptr);
}

fn detailsFieldIndex(err: *anyopaque) ?c_uint {
    return switch (object.lean_obj_tag(err)) {
        user_error_tag => 0,
        1, 2, 3, 4, 5, 6, 7, 8, 9 => 0,
        0, 10, 11, 12, 13, 14, 15, 16 => 1,
        else => null,
    };
}

fn ioErrorMessage(err: *anyopaque) []const u8 {
    if (object.lean_is_scalar(err)) {
        return "end of file";
    }

    const details_index = detailsFieldIndex(err) orelse return "unknown IO error";
    return maybeStringMessage(ctor.lean_ctor_get(err, details_index)) orelse "unknown IO error";
}

pub export fn lean_io_result_show_error(r: *anyopaque) callconv(.c) void {
    if (!lean_io_result_is_error(r)) return;
    const err = lean_io_result_get_error(r) orelse return;
    std.debug.print("uncaught exception: {s}\n", .{ioErrorMessage(err)});
}

pub export fn lean_io_mark_end_initialization() callconv(.c) void {
    init.markEndInitialization();
}

pub export fn lean_io_initializing() callconv(.c) u8 {
    return if (init.isInitializing()) 1 else 0;
}

pub export fn lean_io_result_mk_ok(a: ?*anyopaque) callconv(.c) *anyopaque {
    const result = alloc.lean_alloc_ctor(0, 1, 0);
    ctor.lean_ctor_set(result, 0, a);
    return result;
}

pub export fn lean_io_result_mk_error(e: ?*anyopaque) callconv(.c) *anyopaque {
    const result = alloc.lean_alloc_ctor(1, 1, 0);
    ctor.lean_ctor_set(result, 0, e);
    return result;
}

pub export fn lean_io_result_is_ok(r: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(r)) return false;
    return resultTag(r) == 0;
}

pub export fn lean_io_result_is_error(r: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(r)) return false;
    return resultTag(r) == 1;
}

pub export fn lean_io_result_get_value(r: *anyopaque) callconv(.c) ?*anyopaque {
    std.debug.assert(lean_io_result_is_ok(r));
    return ctor.lean_ctor_get(r, 0);
}

pub export fn lean_io_result_get_error(r: *anyopaque) callconv(.c) ?*anyopaque {
    std.debug.assert(lean_io_result_is_error(r));
    return ctor.lean_ctor_get(r, 0);
}

test "lean_io_result_mk_ok reports ok and returns stored value" {
    const result = lean_io_result_mk_ok(object.lean_box(0));
    defer alloc.lean_free_object(result);

    try testing.expect(lean_io_result_is_ok(result));
    try testing.expect(!lean_io_result_is_error(result));
    try testing.expectEqual(object.lean_box(0), lean_io_result_get_value(result));
}

test "lean_io_result_mk_error reports error and returns stored value" {
    const result = lean_io_result_mk_error(object.lean_box(7));
    defer alloc.lean_free_object(result);

    try testing.expect(!lean_io_result_is_ok(result));
    try testing.expect(lean_io_result_is_error(result));
    try testing.expectEqual(object.lean_box(7), lean_io_result_get_error(result));
}

test "lean_io_mark_end_initialization clears initialization flag" {
    init.resetTestState();
    try testing.expectEqual(@as(u8, 1), lean_io_initializing());
    lean_io_mark_end_initialization();
    try testing.expectEqual(@as(u8, 0), lean_io_initializing());
}
