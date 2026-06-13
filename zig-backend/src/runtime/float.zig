const builtin = @import("builtin");
const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const box = @import("box.zig");
const ctor = @import("ctor.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const once = @import("once.zig");
const rc = @import("rc.zig");
const string = @import("string.zig");

const lean_fmt_allocator_state: u8 = 0;

extern fn lean_int_big_nonneg(a: *anyopaque) callconv(.c) bool;

const LeanFmtAllocator = struct {
    const vtable = std.mem.Allocator.VTable{
        .alloc = allocBytes,
        .resize = resizeBytes,
        .remap = remapBytes,
        .free = freeBytes,
    };

    fn allocBytes(_: *anyopaque, len: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
        if (alignment.toByteUnits() > alloc.LEAN_OBJECT_SIZE_DELTA) return null;
        const ptr: [*]u8 = @ptrCast(alloc.lean_alloc_object(len));
        return ptr;
    }

    fn resizeBytes(_: *anyopaque, memory: []u8, _: std.mem.Alignment, new_len: usize, _: usize) bool {
        return new_len <= memory.len;
    }

    fn remapBytes(_: *anyopaque, memory: []u8, _: std.mem.Alignment, new_len: usize, _: usize) ?[*]u8 {
        if (new_len <= memory.len) return memory.ptr;
        return null;
    }

    fn freeBytes(_: *anyopaque, memory: []u8, _: std.mem.Alignment, _: usize) void {
        alloc.lean_free_object(@ptrCast(memory.ptr));
    }
};

fn leanFmtAllocator() std.mem.Allocator {
    return .{
        .ptr = @constCast(&lean_fmt_allocator_state),
        .vtable = &LeanFmtAllocator.vtable,
    };
}

fn scalarToInt(o: ?*anyopaque) i32 {
    return @as(i32, @bitCast(@as(u32, @truncate(object.lean_unbox(o)))));
}

fn leanIntToObject(value: i32) *anyopaque {
    if (@sizeOf(usize) == 8) {
        return object.lean_box(@as(usize, @intCast(@as(u32, @bitCast(value))))).?;
    }
    return object.lean_box(@as(usize, @bitCast(value))).?;
}

fn formatFloat(comptime T: type, value: T) *anyopaque {
    if (std.math.isNan(value)) {
        return string.mkAsciiStringBytes("NaN");
    }

    const gpa = leanFmtAllocator();
    const bytes = std.fmt.allocPrint(gpa, "{}", .{value}) catch @panic("out of memory");
    defer gpa.free(bytes);
    return string.mkAsciiStringBytes(bytes);
}

fn makeFrexpResult(value: f64) *anyopaque {
    const parts = std.math.frexp(value);
    const result = alloc.lean_alloc_ctor(0, 2, 0);
    ctor.lean_ctor_set(result, 0, box.lean_box_float(parts.significand));
    ctor.lean_ctor_set(result, 1, if (std.math.isFinite(value)) leanIntToObject(parts.exponent) else object.lean_box(0));
    return result;
}

fn makeFrexp32Result(value: f32) *anyopaque {
    const parts = std.math.frexp(value);
    const result = alloc.lean_alloc_ctor(0, 2, 0);
    ctor.lean_ctor_set(result, 0, box.lean_box_float32(parts.significand));
    ctor.lean_ctor_set(result, 1, if (std.math.isFinite(value)) leanIntToObject(parts.exponent) else object.lean_box(0));
    return result;
}

export fn lean_float_to_string(a: f64) callconv(.c) *anyopaque {
    return formatFloat(f64, a);
}

export fn lean_float_scaleb(a: f64, b: *anyopaque) callconv(.c) f64 {
    if (object.lean_is_scalar(b)) {
        return std.math.scalbn(a, scalarToInt(b));
    }
    if (a == 0) return 0;
    if (builtin.is_test) return 0;
    return if (lean_int_big_nonneg(b)) a * std.math.inf(f64) else 0;
}

export fn lean_float_isnan(a: f64) callconv(.c) u8 {
    return @intFromBool(std.math.isNan(a));
}

export fn lean_float_isfinite(a: f64) callconv(.c) u8 {
    return @intFromBool(std.math.isFinite(a));
}

export fn lean_float_isinf(a: f64) callconv(.c) u8 {
    return @intFromBool(std.math.isInf(a));
}

export fn lean_float_frexp(a: f64) callconv(.c) *anyopaque {
    return makeFrexpResult(a);
}

export fn lean_float32_to_string(a: f32) callconv(.c) *anyopaque {
    return formatFloat(f32, a);
}

export fn lean_float32_scaleb(a: f32, b: *anyopaque) callconv(.c) f32 {
    if (object.lean_is_scalar(b)) {
        return std.math.scalbn(a, scalarToInt(b));
    }
    if (a == 0) return 0;
    if (builtin.is_test) return 0;
    return if (lean_int_big_nonneg(b)) a * std.math.inf(f32) else 0;
}

export fn lean_float32_isnan(a: f32) callconv(.c) u8 {
    return @intFromBool(std.math.isNan(a));
}

export fn lean_float32_isfinite(a: f32) callconv(.c) u8 {
    return @intFromBool(std.math.isFinite(a));
}

export fn lean_float32_isinf(a: f32) callconv(.c) u8 {
    return @intFromBool(std.math.isInf(a));
}

export fn lean_float32_frexp(a: f32) callconv(.c) *anyopaque {
    return makeFrexp32Result(a);
}

export fn lean_float32_once_cold(loc: *f32, tok: *once.lean_once_cell_t, init: *const fn () callconv(.c) f32) callconv(.c) f32 {
    return once.onceCold(f32, loc, tok, init);
}

export fn lean_float_once_cold(loc: *f64, tok: *once.lean_once_cell_t, init: *const fn () callconv(.c) f64) callconv(.c) f64 {
    return once.onceCold(f64, loc, tok, init);
}

fn stringBytes(o: *anyopaque) []const u8 {
    const str: *lean.lean_string_object = @ptrCast(@alignCast(o));
    const bytes: [*]const u8 = @ptrCast(&str.m_data);
    return bytes[0 .. str.m_size - 1];
}

var float_once_count: usize = 0;
var float32_once_count: usize = 0;

fn initFloatValue() callconv(.c) f64 {
    float_once_count += 1;
    return 7.5;
}

fn initFloat32Value() callconv(.c) f32 {
    float32_once_count += 1;
    return 3.25;
}

test "lean_float_frexp zero returns zero significand and exponent" {
    const result = lean_float_frexp(0.0);
    defer rc.lean_dec(result);

    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(@as(u64, 0), @as(u64, @bitCast(box.lean_unbox_float(ctor.lean_ctor_get(result, 0)))));
    try testing.expectEqual(object.lean_box(0), ctor.lean_ctor_get(result, 1));
}

test "lean_float predicates classify infinity and NaN" {
    try testing.expectEqual(@as(u8, 0), lean_float_isfinite(std.math.inf(f64)));
    try testing.expectEqual(@as(u8, 1), lean_float_isinf(std.math.inf(f64)));
    try testing.expectEqual(@as(u8, 1), lean_float_isnan(@as(f64, @bitCast(@as(u64, 0x7ff8_0000_0000_1234)))));
}

test "lean_float_to_string prints decimal prefix" {
    const result = lean_float_to_string(3.14);
    defer rc.lean_dec(result);

    try testing.expect(std.mem.startsWith(u8, stringBytes(result), "3.14"));
}

test "lean_float_once_cold initializes once" {
    float_once_count = 0;
    var loc: f64 = 0;
    var tok = once.initOnceCell();

    try testing.expectEqual(@as(f64, 7.5), lean_float_once_cold(&loc, &tok, &initFloatValue));
    try testing.expectEqual(@as(f64, 7.5), lean_float_once_cold(&loc, &tok, &initFloatValue));
    try testing.expectEqual(@as(usize, 1), float_once_count);
}

test "lean_float32_frexp zero returns zero significand and exponent" {
    const result = lean_float32_frexp(0.0);
    defer rc.lean_dec(result);

    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(@as(u32, 0), @as(u32, @bitCast(box.lean_unbox_float32(ctor.lean_ctor_get(result, 0)))));
    try testing.expectEqual(object.lean_box(0), ctor.lean_ctor_get(result, 1));
}

test "lean_float32 predicates classify infinity and NaN" {
    try testing.expectEqual(@as(u8, 0), lean_float32_isfinite(std.math.inf(f32)));
    try testing.expectEqual(@as(u8, 1), lean_float32_isinf(std.math.inf(f32)));
    try testing.expectEqual(@as(u8, 1), lean_float32_isnan(@as(f32, @bitCast(@as(u32, 0x7fc0_1234)))));
}

test "lean_float32_to_string prints decimal prefix" {
    const result = lean_float32_to_string(3.14);
    defer rc.lean_dec(result);

    try testing.expect(std.mem.startsWith(u8, stringBytes(result), "3.14"));
}

test "lean_float32_once_cold initializes once" {
    float32_once_count = 0;
    var loc: f32 = 0;
    var tok = once.initOnceCell();

    try testing.expectEqual(@as(f32, 3.25), lean_float32_once_cold(&loc, &tok, &initFloat32Value));
    try testing.expectEqual(@as(f32, 3.25), lean_float32_once_cold(&loc, &tok, &initFloat32Value));
    try testing.expectEqual(@as(usize, 1), float32_once_count);
}
