// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const runtime_options = @import("runtime_options");

const pointer_bytes: c_uint = @sizeOf(?*anyopaque);

fn mkOptionSome(value: *anyopaque) *anyopaque {
    const some = alloc.lean_alloc_ctor(1, 1, 0);
    ctor.lean_ctor_set(some, 0, value);
    return some;
}

fn mkOptionFilenameError(tag: c_uint, filename: ?*anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    const result = alloc.lean_alloc_ctor(tag, 2, 4);
    ctor.lean_ctor_set(result, 0, if (filename) |name| mkOptionSome(name) else object.lean_box(0));
    ctor.lean_ctor_set(result, 1, details);
    ctor.lean_ctor_set_uint32(result, pointer_bytes * 2, os_code);
    return result;
}

fn mkDirectFilenameError(tag: c_uint, filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    const result = alloc.lean_alloc_ctor(tag, 2, 4);
    ctor.lean_ctor_set(result, 0, filename);
    ctor.lean_ctor_set(result, 1, details);
    ctor.lean_ctor_set_uint32(result, pointer_bytes * 2, os_code);
    return result;
}

fn mkDetailsOnlyError(tag: c_uint, os_code: u32, details: *anyopaque) *anyopaque {
    const result = alloc.lean_alloc_ctor(tag, 1, 4);
    ctor.lean_ctor_set(result, 0, details);
    ctor.lean_ctor_set_uint32(result, pointer_bytes, os_code);
    return result;
}

pub fn lean_mk_io_error_already_exists(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(0, null, os_code, details);
}

pub fn lean_mk_io_error_already_exists_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(0, filename, os_code, details);
}

pub fn lean_mk_io_error_eof(unit: *anyopaque) *anyopaque {
    _ = unit;
    return object.lean_box(17).?;
}

pub fn lean_mk_io_error_hardware_fault(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(5, os_code, details);
}

pub fn lean_mk_io_error_illegal_operation(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(7, os_code, details);
}

pub fn lean_mk_io_error_inappropriate_type(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(15, null, os_code, details);
}

pub fn lean_mk_io_error_inappropriate_type_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(15, filename, os_code, details);
}

pub fn lean_mk_io_error_interrupted(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkDirectFilenameError(10, filename, os_code, details);
}

pub fn lean_mk_io_error_invalid_argument(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(12, null, os_code, details);
}

pub fn lean_mk_io_error_invalid_argument_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(12, filename, os_code, details);
}

pub fn lean_mk_io_error_no_file_or_directory(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkDirectFilenameError(11, filename, os_code, details);
}

pub fn lean_mk_io_error_no_such_thing(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(16, null, os_code, details);
}

pub fn lean_mk_io_error_no_such_thing_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(16, filename, os_code, details);
}

pub fn lean_mk_io_error_other_error(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(1, os_code, details);
}

pub fn lean_mk_io_error_permission_denied(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(13, null, os_code, details);
}

pub fn lean_mk_io_error_permission_denied_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(13, filename, os_code, details);
}

pub fn lean_mk_io_error_protocol_error(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(8, os_code, details);
}

pub fn lean_mk_io_error_resource_busy(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(2, os_code, details);
}

pub fn lean_mk_io_error_resource_exhausted(os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(14, null, os_code, details);
}

pub fn lean_mk_io_error_resource_exhausted_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return mkOptionFilenameError(14, filename, os_code, details);
}

pub fn lean_mk_io_error_resource_vanished(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(3, os_code, details);
}

pub fn lean_mk_io_error_time_expired(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(9, os_code, details);
}

pub fn lean_mk_io_error_unsatisfied_constraints(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(6, os_code, details);
}

pub fn lean_mk_io_error_unsupported_operation(os_code: u32, details: *anyopaque) *anyopaque {
    return mkDetailsOnlyError(4, os_code, details);
}

pub fn lean_mk_io_user_error(msg: *anyopaque) *anyopaque {
    const result = alloc.lean_alloc_ctor(18, 1, 0);
    ctor.lean_ctor_set(result, 0, msg);
    return result;
}

pub export fn lean_mk_io_error_already_exists_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_already_exists(os_code, details);
}

pub export fn lean_mk_io_error_already_exists_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_already_exists_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_eof_zig_impl(unit: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_eof(unit);
}

pub export fn lean_mk_io_error_hardware_fault_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_hardware_fault(os_code, details);
}

pub export fn lean_mk_io_error_illegal_operation_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_illegal_operation(os_code, details);
}

pub export fn lean_mk_io_error_inappropriate_type_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_inappropriate_type(os_code, details);
}

pub export fn lean_mk_io_error_inappropriate_type_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_inappropriate_type_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_interrupted_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_interrupted(filename, os_code, details);
}

pub export fn lean_mk_io_error_invalid_argument_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_invalid_argument(os_code, details);
}

pub export fn lean_mk_io_error_invalid_argument_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_invalid_argument_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_no_file_or_directory_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_no_file_or_directory(filename, os_code, details);
}

pub export fn lean_mk_io_error_no_such_thing_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_no_such_thing(os_code, details);
}

pub export fn lean_mk_io_error_no_such_thing_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_no_such_thing_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_other_error_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_other_error(os_code, details);
}

pub export fn lean_mk_io_error_permission_denied_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_permission_denied(os_code, details);
}

pub export fn lean_mk_io_error_permission_denied_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_permission_denied_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_protocol_error_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_protocol_error(os_code, details);
}

pub export fn lean_mk_io_error_resource_busy_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_resource_busy(os_code, details);
}

pub export fn lean_mk_io_error_resource_exhausted_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_resource_exhausted(os_code, details);
}

pub export fn lean_mk_io_error_resource_exhausted_file_zig_impl(filename: *anyopaque, os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_resource_exhausted_file(filename, os_code, details);
}

pub export fn lean_mk_io_error_resource_vanished_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_resource_vanished(os_code, details);
}

pub export fn lean_mk_io_error_time_expired_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_time_expired(os_code, details);
}

pub export fn lean_mk_io_error_unsatisfied_constraints_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_unsatisfied_constraints(os_code, details);
}

pub export fn lean_mk_io_error_unsupported_operation_zig_impl(os_code: u32, details: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_error_unsupported_operation(os_code, details);
}

pub export fn lean_mk_io_user_error_zig_impl(msg: *anyopaque) callconv(.c) *anyopaque {
    return lean_mk_io_user_error(msg);
}
extern fn lean_mk_string_unchecked(s: [*:0]const u8, sz: usize, len: usize) callconv(.c) *anyopaque;

fn lean_io_error_to_string_impl(err: *anyopaque) callconv(.c) *anyopaque {
    const tag = object.lean_obj_tag(err);
    if (tag == 17) {
        return lean_mk_string_unchecked("end of file".ptr, 11, 11);
    }
    if (tag == 18) {
        const msg = ctor.lean_ctor_get(err, 0).?;
        rc.lean_inc(msg);
        return msg;
    }
    return lean_mk_string_unchecked("IO error".ptr, 8, 8);
}
comptime {
    if (runtime_options.export_lean_helpers) {
        @export(&lean_io_error_to_string_impl, .{ .name = "lean_io_error_to_string" });
    }
}

fn expectOptionSome(option_value: ?*anyopaque, expected: ?*anyopaque) !void {
    try testing.expect(option_value != null);
    try testing.expect(!object.lean_is_scalar(option_value));
    try testing.expectEqual(@as(c_uint, 1), object.lean_obj_tag(option_value));
    try testing.expectEqual(expected, ctor.lean_ctor_get(option_value.?, 0));
}

fn expectScalarCode(result: *anyopaque, object_count: c_uint, expected: u32) !void {
    try testing.expectEqual(expected, ctor.lean_ctor_get_uint32(result, pointer_bytes * object_count));
}

fn expectDetailsOnly(result: *anyopaque, tag: c_uint, expected_code: u32, expected_details: ?*anyopaque) !void {
    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(tag, object.lean_obj_tag(result));
    try testing.expectEqual(expected_details, ctor.lean_ctor_get(result, 0));
    try expectScalarCode(result, 1, expected_code);
}

fn expectOptionFilename(result: *anyopaque, tag: c_uint, filename: ?*anyopaque, expected_code: u32, expected_details: ?*anyopaque) !void {
    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(tag, object.lean_obj_tag(result));
    try expectOptionSome(ctor.lean_ctor_get(result, 0), filename);
    try testing.expectEqual(expected_details, ctor.lean_ctor_get(result, 1));
    try expectScalarCode(result, 2, expected_code);
}

fn expectOptionNone(result: *anyopaque, tag: c_uint, expected_code: u32, expected_details: ?*anyopaque) !void {
    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(tag, object.lean_obj_tag(result));
    try testing.expectEqual(object.lean_box(0), ctor.lean_ctor_get(result, 0));
    try testing.expectEqual(expected_details, ctor.lean_ctor_get(result, 1));
    try expectScalarCode(result, 2, expected_code);
}

fn expectDirectFilename(result: *anyopaque, tag: c_uint, filename: ?*anyopaque, expected_code: u32, expected_details: ?*anyopaque) !void {
    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(tag, object.lean_obj_tag(result));
    try testing.expectEqual(filename, ctor.lean_ctor_get(result, 0));
    try testing.expectEqual(expected_details, ctor.lean_ctor_get(result, 1));
    try expectScalarCode(result, 2, expected_code);
}

fn mkString(bytes: [:0]const u8) *anyopaque {
    const size = bytes.len + 1;
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_string_object) + size);
    const str: *lean.lean_string_object = @ptrCast(@alignCast(ptr));
    str.m_header = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanString,
    };
    str.m_size = size;
    str.m_capacity = size;
    str.m_length = bytes.len;
    const data: [*]u8 = @ptrCast(&str.m_data);
    @memcpy(data[0..bytes.len], bytes[0..bytes.len]);
    data[bytes.len] = 0;
    return ptr;
}

fn decIfHeap(o: ?*anyopaque) void {
    if (o) |value| {
        if (!object.lean_is_scalar(value)) {
            rc.lean_dec(value);
        }
    }
}

test "io error constructors mirror stage1 generated layouts" {
    const os_code: u32 = 0xdecafbad;

    {
        const details = mkString("already exists");
        const result = lean_mk_io_error_already_exists(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 0, os_code, details);
    }

    {
        const filename = mkString("exists.txt");
        const details = mkString("already exists file");
        const result = lean_mk_io_error_already_exists_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 0, filename, os_code, details);
    }

    {
        const result = lean_mk_io_error_eof(object.lean_box(0).?);
        try testing.expect(object.lean_is_scalar(result));
        try testing.expectEqual(@as(c_uint, 17), object.lean_obj_tag(result));
    }

    {
        const details = mkString("hardware fault");
        const result = lean_mk_io_error_hardware_fault(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 5, os_code, details);
    }

    {
        const details = mkString("illegal operation");
        const result = lean_mk_io_error_illegal_operation(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 7, os_code, details);
    }

    {
        const details = mkString("inappropriate type");
        const result = lean_mk_io_error_inappropriate_type(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 15, os_code, details);
    }

    {
        const filename = mkString("dir");
        const details = mkString("inappropriate type file");
        const result = lean_mk_io_error_inappropriate_type_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 15, filename, os_code, details);
    }

    {
        const filename = mkString("interrupt");
        const details = mkString("interrupted");
        const result = lean_mk_io_error_interrupted(filename, os_code, details);
        defer decIfHeap(result);
        try expectDirectFilename(result, 10, filename, os_code, details);
    }

    {
        const details = mkString("invalid argument");
        const result = lean_mk_io_error_invalid_argument(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 12, os_code, details);
    }

    {
        const filename = mkString("bad.txt");
        const details = mkString("invalid argument file");
        const result = lean_mk_io_error_invalid_argument_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 12, filename, os_code, details);
    }

    {
        const filename = mkString("missing.txt");
        const details = mkString("no file or directory");
        const result = lean_mk_io_error_no_file_or_directory(filename, os_code, details);
        defer decIfHeap(result);
        try expectDirectFilename(result, 11, filename, os_code, details);
    }

    {
        const details = mkString("no such thing");
        const result = lean_mk_io_error_no_such_thing(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 16, os_code, details);
    }

    {
        const filename = mkString("ghost");
        const details = mkString("no such thing file");
        const result = lean_mk_io_error_no_such_thing_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 16, filename, os_code, details);
    }

    {
        const details = mkString("other error");
        const result = lean_mk_io_error_other_error(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 1, os_code, details);
    }

    {
        const details = mkString("permission denied");
        const result = lean_mk_io_error_permission_denied(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 13, os_code, details);
    }

    {
        const filename = mkString("secret");
        const details = mkString("permission denied file");
        const result = lean_mk_io_error_permission_denied_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 13, filename, os_code, details);
    }

    {
        const details = mkString("protocol error");
        const result = lean_mk_io_error_protocol_error(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 8, os_code, details);
    }

    {
        const details = mkString("resource busy");
        const result = lean_mk_io_error_resource_busy(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 2, os_code, details);
    }

    {
        const details = mkString("resource exhausted");
        const result = lean_mk_io_error_resource_exhausted(os_code, details);
        defer decIfHeap(result);
        try expectOptionNone(result, 14, os_code, details);
    }

    {
        const filename = mkString("full");
        const details = mkString("resource exhausted file");
        const result = lean_mk_io_error_resource_exhausted_file(filename, os_code, details);
        defer decIfHeap(result);
        try expectOptionFilename(result, 14, filename, os_code, details);
    }

    {
        const details = mkString("resource vanished");
        const result = lean_mk_io_error_resource_vanished(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 3, os_code, details);
    }

    {
        const details = mkString("time expired");
        const result = lean_mk_io_error_time_expired(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 9, os_code, details);
    }

    {
        const details = mkString("unsatisfied constraints");
        const result = lean_mk_io_error_unsatisfied_constraints(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 6, os_code, details);
    }

    {
        const details = mkString("unsupported operation");
        const result = lean_mk_io_error_unsupported_operation(os_code, details);
        defer decIfHeap(result);
        try expectDetailsOnly(result, 4, os_code, details);
    }

    {
        const msg = mkString("user error");
        const result = lean_mk_io_user_error(msg);
        defer decIfHeap(result);
        try testing.expect(!object.lean_is_scalar(result));
        try testing.expectEqual(@as(c_uint, 18), object.lean_obj_tag(result));
        try testing.expectEqual(msg, ctor.lean_ctor_get(result, 0));
    }
}
