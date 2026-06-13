// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const builtin = @import("builtin");
const testing = std.testing;
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const string = @import("string.zig");

const pointer_bytes: c_uint = @sizeOf(?*anyopaque);
const murmur_hash_m: u64 = 0xc6a4a7935bd1e995;
const murmur_hash_r: u6 = 47;

const nat_big_eq = if (builtin.is_test)
    struct {
        fn call(a1: ?*anyopaque, a2: ?*anyopaque) bool {
            return a1 == a2;
        }
    }.call
else
    struct {
        extern fn lean_nat_big_eq(a1: ?*anyopaque, a2: ?*anyopaque) callconv(.c) bool;
    }.lean_nat_big_eq;

fn asString(o: *anyopaque) *lean.lean_string_object {
    return @ptrCast(@alignCast(o));
}

fn stringSize(o: *anyopaque) usize {
    return asString(o).m_size;
}

fn stringData(o: *anyopaque) [*]const u8 {
    return @ptrCast(&asString(o).m_data);
}

fn stringEq(s1: ?*anyopaque, s2: ?*anyopaque) bool {
    if (s1 == s2) return true;
    if (s1 == null or s2 == null) return false;
    const lhs = s1.?;
    const rhs = s2.?;
    const lhs_size = stringSize(lhs);
    return lhs_size == stringSize(rhs) and std.mem.eql(u8, stringData(lhs)[0..lhs_size], stringData(rhs)[0..lhs_size]);
}

fn natEq(a1: ?*anyopaque, a2: ?*anyopaque) bool {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return a1 == a2;
    }
    return nat_big_eq(a1, a2);
}

fn nameHashPtr(n: ?*anyopaque) u64 {
    std.debug.assert(n != null and !object.lean_is_scalar(n));
    return ctor.lean_ctor_get_uint64(n.?, pointer_bytes * 2);
}

fn sliceBounds(slice: *anyopaque) struct { start: usize, end: usize } {
    const start_obj = ctor.lean_ctor_get(slice, 1) orelse @panic("slice start missing");
    const end_obj = ctor.lean_ctor_get(slice, 2) orelse @panic("slice end missing");
    std.debug.assert(object.lean_is_scalar(start_obj));
    std.debug.assert(object.lean_is_scalar(end_obj));
    return .{
        .start = object.lean_unbox(start_obj),
        .end = object.lean_unbox(end_obj),
    };
}

fn sliceBytes(slice: *anyopaque) []const u8 {
    const source = ctor.lean_ctor_get(slice, 0) orelse @panic("slice source missing");
    const bounds = sliceBounds(slice);
    std.debug.assert(bounds.end >= bounds.start);
    return stringData(source)[bounds.start..bounds.end];
}

fn murmurHash64A(bytes: []const u8, seed: u64) u64 {
    var h = seed ^ (@as(u64, bytes.len) *% murmur_hash_m);
    var index: usize = 0;
    while (index + 8 <= bytes.len) : (index += 8) {
        var k: u64 = 0;
        @memcpy(std.mem.asBytes(&k), bytes[index .. index + 8]);
        k *%= murmur_hash_m;
        k ^= k >> murmur_hash_r;
        k *%= murmur_hash_m;
        h ^= k;
        h *%= murmur_hash_m;
    }

    const tail = bytes[index..];
    switch (tail.len) {
        7 => h ^= @as(u64, tail[6]) << 48,
        else => {},
    }
    switch (tail.len) {
        7, 6 => h ^= @as(u64, tail[5]) << 40,
        else => {},
    }
    switch (tail.len) {
        7, 6, 5 => h ^= @as(u64, tail[4]) << 32,
        else => {},
    }
    switch (tail.len) {
        7, 6, 5, 4 => h ^= @as(u64, tail[3]) << 24,
        else => {},
    }
    switch (tail.len) {
        7, 6, 5, 4, 3 => h ^= @as(u64, tail[2]) << 16,
        else => {},
    }
    switch (tail.len) {
        7, 6, 5, 4, 3, 2 => h ^= @as(u64, tail[1]) << 8,
        else => {},
    }
    switch (tail.len) {
        7, 6, 5, 4, 3, 2, 1 => {
            h ^= @as(u64, tail[0]);
            h *%= murmur_hash_m;
        },
        else => {},
    }

    h ^= h >> murmur_hash_r;
    h *%= murmur_hash_m;
    h ^= h >> murmur_hash_r;
    return h;
}

pub export fn lean_name_eq(n1: *anyopaque, n2: *anyopaque) callconv(.c) u8 {
    var lhs: ?*anyopaque = n1;
    var rhs: ?*anyopaque = n2;

    if (lhs == rhs) return 1;
    if (object.lean_is_scalar(lhs) and object.lean_is_scalar(rhs)) return 0;
    if (object.lean_is_scalar(lhs) != object.lean_is_scalar(rhs) or nameHashPtr(lhs) != nameHashPtr(rhs)) {
        return 0;
    }

    while (true) {
        std.debug.assert(lhs != null and rhs != null);
        std.debug.assert(!object.lean_is_scalar(lhs));
        std.debug.assert(!object.lean_is_scalar(rhs));

        const tag = object.lean_ptr_tag(lhs.?);
        if (tag != object.lean_ptr_tag(rhs.?)) {
            return 0;
        }

        if (tag == 1) {
            if (!stringEq(ctor.lean_ctor_get(lhs.?, 1), ctor.lean_ctor_get(rhs.?, 1))) {
                return 0;
            }
        } else {
            if (!natEq(ctor.lean_ctor_get(lhs.?, 1), ctor.lean_ctor_get(rhs.?, 1))) {
                return 0;
            }
        }

        lhs = ctor.lean_ctor_get(lhs.?, 0);
        rhs = ctor.lean_ctor_get(rhs.?, 0);
        if (lhs == rhs) return 1;
        if (object.lean_is_scalar(lhs) != object.lean_is_scalar(rhs)) {
            return 0;
        }
    }
}

pub export fn lean_slice_hash(slice: *anyopaque) callconv(.c) u64 {
    return murmurHash64A(sliceBytes(slice), 11);
}

pub export fn lean_slice_dec_lt(s1: *anyopaque, s2: *anyopaque) callconv(.c) u8 {
    return @intFromBool(std.mem.order(u8, sliceBytes(s1), sliceBytes(s2)) == .lt);
}

fn mkNameNum(prefix: *anyopaque, nat_value: usize, hash: u64) *anyopaque {
    const result = alloc.lean_alloc_ctor(0, 2, @sizeOf(u64));
    ctor.lean_ctor_set(result, 0, prefix);
    ctor.lean_ctor_set(result, 1, object.lean_box(nat_value));
    ctor.lean_ctor_set_uint64(result, pointer_bytes * 2, hash);
    return result;
}

fn mkNameStr(prefix: *anyopaque, suffix: []const u8, hash: u64) *anyopaque {
    const result = alloc.lean_alloc_ctor(1, 2, @sizeOf(u64));
    ctor.lean_ctor_set(result, 0, prefix);
    ctor.lean_ctor_set(result, 1, string.mkAsciiStringBytes(suffix));
    ctor.lean_ctor_set_uint64(result, pointer_bytes * 2, hash);
    return result;
}

fn mkSlice(source: *anyopaque, start: usize, end: usize) *anyopaque {
    const result = alloc.lean_alloc_ctor(0, 3, 0);
    ctor.lean_ctor_set(result, 0, source);
    ctor.lean_ctor_set(result, 1, object.lean_box(start));
    ctor.lean_ctor_set(result, 2, object.lean_box(end));
    return result;
}

fn decIfHeap(o: ?*anyopaque) void {
    if (o) |value| {
        if (!object.lean_is_scalar(value)) {
            rc.lean_dec(value);
        }
    }
}

test "lean_name_eq walks the Lean.Name ctor spine" {
    const anonymous = object.lean_box(0).?;
    const lhs = mkNameStr(mkNameNum(anonymous, 7, 0xaaaa), "leaf", 0xbbbb);
    const rhs = mkNameStr(mkNameNum(anonymous, 7, 0xaaaa), "leaf", 0xbbbb);
    const diff = mkNameStr(mkNameNum(anonymous, 8, 0xaaaa), "leaf", 0xbbbb);
    defer decIfHeap(lhs);
    defer decIfHeap(rhs);
    defer decIfHeap(diff);

    try testing.expectEqual(@as(u8, 1), lean_name_eq(lhs, rhs));
    try testing.expectEqual(@as(u8, 0), lean_name_eq(lhs, diff));
}

test "lean_slice_hash uses slice bytes rather than the backing string" {
    const slice1 = mkSlice(string.mkAsciiStringBytes("zzleanzz"), 2, 6);
    const slice2 = mkSlice(string.mkAsciiStringBytes("lean"), 0, 4);
    const slice3 = mkSlice(string.mkAsciiStringBytes("leao"), 0, 4);
    defer decIfHeap(slice1);
    defer decIfHeap(slice2);
    defer decIfHeap(slice3);

    try testing.expectEqual(lean_slice_hash(slice1), lean_slice_hash(slice2));
    try testing.expect(lean_slice_hash(slice1) != lean_slice_hash(slice3));
}

test "lean_slice_dec_lt uses lexicographic order and slice length" {
    const less = mkSlice(string.mkAsciiStringBytes("abc"), 0, 3);
    const greater = mkSlice(string.mkAsciiStringBytes("abd"), 0, 3);
    const prefix = mkSlice(string.mkAsciiStringBytes("ab"), 0, 2);
    defer decIfHeap(less);
    defer decIfHeap(greater);
    defer decIfHeap(prefix);

    try testing.expectEqual(@as(u8, 1), lean_slice_dec_lt(less, greater));
    try testing.expectEqual(@as(u8, 0), lean_slice_dec_lt(greater, less));
    try testing.expectEqual(@as(u8, 1), lean_slice_dec_lt(prefix, less));
}
