const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");

fn taggedScalarLimit() u64 {
    return @as(u64, std.math.maxInt(usize) >> 1);
}

fn header(o: *anyopaque) *lean.lean_object {
    return @ptrCast(@alignCast(o));
}

fn scalarFieldPtr(comptime T: type, o: *anyopaque) *T {
    return @ptrFromInt(@intFromPtr(o) + @sizeOf(lean.lean_ctor_object));
}

fn maybeFree(o: ?*anyopaque) void {
    if (o) |ptr| {
        if (!object.lean_is_scalar(ptr)) {
            alloc.lean_free_object(ptr);
        }
    }
}

fn allocBoxedScalar(comptime T: type, value: T) *anyopaque {
    const ptr = alloc.lean_alloc_ctor(0, 0, @intCast(@sizeOf(T)));
    header(ptr).m_cs_sz = @intCast(@sizeOf(T));
    scalarFieldPtr(T, ptr).* = value;
    return ptr;
}

fn loadBoxedScalar(comptime T: type, o: *anyopaque) T {
    return scalarFieldPtr(T, o).*;
}

fn boxTaggedIfPossible(v: u64) ?*anyopaque {
    if (v <= taggedScalarLimit()) {
        return object.lean_box(@intCast(v));
    }
    return null;
}

pub export fn lean_box_uint8_zig_impl(v: u8) callconv(.c) ?*anyopaque {
    return object.lean_box(v);
}

pub export fn lean_unbox_uint8_zig_impl(o: ?*anyopaque) callconv(.c) u8 {
    if (object.lean_is_scalar(o)) {
        return @intCast(object.lean_unbox(o));
    }
    return loadBoxedScalar(u8, o.?);
}

pub export fn lean_box_uint16_zig_impl(v: u16) callconv(.c) ?*anyopaque {
    return object.lean_box(v);
}

pub export fn lean_unbox_uint16_zig_impl(o: ?*anyopaque) callconv(.c) u16 {
    if (object.lean_is_scalar(o)) {
        return @intCast(object.lean_unbox(o));
    }
    return loadBoxedScalar(u16, o.?);
}

pub export fn lean_box_uint32(v: u32) callconv(.c) ?*anyopaque {
    if (@sizeOf(usize) == 4) {
        return allocBoxedScalar(u32, v);
    }
    return object.lean_box(v);
}

pub export fn lean_unbox_uint32(o: ?*anyopaque) callconv(.c) u32 {
    if (object.lean_is_scalar(o)) {
        return @intCast(object.lean_unbox(o));
    }
    return loadBoxedScalar(u32, o.?);
}

pub export fn lean_box_uint64(v: u64) callconv(.c) ?*anyopaque {
    return boxTaggedIfPossible(v) orelse allocBoxedScalar(u64, v);
}

pub export fn lean_unbox_uint64(o: ?*anyopaque) callconv(.c) u64 {
    if (object.lean_is_scalar(o)) {
        return object.lean_unbox(o);
    }
    return loadBoxedScalar(u64, o.?);
}

pub export fn lean_box_usize(v: usize) callconv(.c) ?*anyopaque {
    return boxTaggedIfPossible(v) orelse allocBoxedScalar(usize, v);
}

pub export fn lean_unbox_usize(o: ?*anyopaque) callconv(.c) usize {
    if (object.lean_is_scalar(o)) {
        return object.lean_unbox(o);
    }
    return loadBoxedScalar(usize, o.?);
}

pub export fn lean_box_float(v: f64) callconv(.c) ?*anyopaque {
    return allocBoxedScalar(u64, lean_float_to_bits(v));
}

pub export fn lean_unbox_float(o: ?*anyopaque) callconv(.c) f64 {
    return lean_float_of_bits(loadBoxedScalar(u64, o.?));
}

pub export fn lean_box_float32(v: f32) callconv(.c) ?*anyopaque {
    return allocBoxedScalar(u32, lean_float32_to_bits(v));
}

pub export fn lean_unbox_float32(o: ?*anyopaque) callconv(.c) f32 {
    return lean_float32_of_bits(loadBoxedScalar(u32, o.?));
}

export fn lean_float_of_bits(u: u64) callconv(.c) f64 {
    return @bitCast(u);
}

export fn lean_float_to_bits(d: f64) callconv(.c) u64 {
    return @bitCast(d);
}

export fn lean_float32_of_bits(u: u32) callconv(.c) f32 {
    return @bitCast(u);
}

export fn lean_float32_to_bits(d: f32) callconv(.c) u32 {
    return @bitCast(d);
}

test "usize roundtrip covers tagged and boxed representations" {
    const large = std.math.maxInt(usize) - 1;
    const values = [_]usize{ 0, 1, @intCast(taggedScalarLimit()), large };

    for (values) |value| {
        const boxed = lean_box_usize(value);
        defer maybeFree(boxed);

        try testing.expectEqual(value, lean_unbox_usize(boxed));
        if (value <= taggedScalarLimit()) {
            try testing.expect(object.lean_is_scalar(boxed));
        } else {
            try testing.expect(!object.lean_is_scalar(boxed));
            try testing.expectEqual(@as(u16, @sizeOf(usize)), header(boxed.?).m_cs_sz);
        }
    }
}

test "uint32 roundtrip preserves boundary values" {
    const values = [_]u32{ 0, 1, std.math.maxInt(u32) };

    for (values) |value| {
        const boxed = lean_box_uint32(value);
        defer maybeFree(boxed);

        try testing.expectEqual(value, lean_unbox_uint32(boxed));
    }
}

test "uint8 zig helper roundtrip preserves boundary values" {
    const values = [_]u8{ 0, std.math.maxInt(u8) };

    for (values) |value| {
        const boxed = lean_box_uint8_zig_impl(value);
        defer maybeFree(boxed);

        try testing.expect(object.lean_is_scalar(boxed));
        try testing.expectEqual(value, lean_unbox_uint8_zig_impl(boxed));
    }
}

test "uint16 zig helper roundtrip preserves boundary values" {
    const values = [_]u16{ 0, std.math.maxInt(u16) };

    for (values) |value| {
        const boxed = lean_box_uint16_zig_impl(value);
        defer maybeFree(boxed);

        try testing.expect(object.lean_is_scalar(boxed));
        try testing.expectEqual(value, lean_unbox_uint16_zig_impl(boxed));
    }
}

test "uint64 roundtrip uses heap fallback above tagged-scalar range" {
    const limit = taggedScalarLimit();
    const values = [_]u64{ 0, 1, limit, limit + 1, std.math.maxInt(u64) };

    for (values) |value| {
        const boxed = lean_box_uint64(value);
        defer maybeFree(boxed);

        try testing.expectEqual(value, lean_unbox_uint64(boxed));
        if (value <= limit) {
            try testing.expect(object.lean_is_scalar(boxed));
        } else {
            try testing.expect(!object.lean_is_scalar(boxed));
            try testing.expectEqual(@as(u16, @sizeOf(u64)), header(boxed.?).m_cs_sz);
        }
    }
}

test "float boxing preserves f64 bit patterns" {
    const bit_patterns = [_]u64{
        0x0000_0000_0000_0000,
        0x8000_0000_0000_0000,
        0x3ff0_0000_0000_0000,
        0x7ff8_0000_0000_1234,
        0xfff0_0000_0000_0000,
    };

    for (bit_patterns) |bits| {
        const value = lean_float_of_bits(bits);
        const boxed = lean_box_float(value);
        defer maybeFree(boxed);

        try testing.expect(!object.lean_is_scalar(boxed));
        try testing.expectEqual(@as(u16, @sizeOf(f64)), header(boxed.?).m_cs_sz);
        try testing.expectEqual(bits, lean_float_to_bits(lean_unbox_float(boxed)));
    }
}

test "float32 boxing preserves f32 bit patterns" {
    const bit_patterns = [_]u32{
        0x0000_0000,
        0x8000_0000,
        0x3f80_0000,
        0x7fc0_1234,
        0xff80_0000,
    };

    for (bit_patterns) |bits| {
        const value = lean_float32_of_bits(bits);
        const boxed = lean_box_float32(value);
        defer maybeFree(boxed);

        try testing.expect(!object.lean_is_scalar(boxed));
        try testing.expectEqual(@as(u16, @sizeOf(f32)), header(boxed.?).m_cs_sz);
        try testing.expectEqual(bits, lean_float32_to_bits(lean_unbox_float32(boxed)));
    }
}
