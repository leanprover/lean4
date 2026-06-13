const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const io_min = @import("io_min.zig");
const lean = @import("lean_object.zig");
const mpz_zig = @import("mpz_zig");
const object = @import("object.zig");
const mpz_object = @import("mpz_object.zig");

const max_small_nat: usize = std.math.maxInt(usize) >> 1;
const overflow_message: [:0]const u8 = "integer overflow in runtime computation";

fn freeNatResult(o: ?*anyopaque) void {
    if (!object.lean_is_scalar(o)) alloc.lean_free_object(o.?);
}

fn expectNatValue(o: ?*anyopaque, expected: []const u8, expect_scalar: bool) !void {
    try testing.expectEqual(expect_scalar, object.lean_is_scalar(o));
    if (expect_scalar) {
        const parsed = try std.fmt.parseUnsigned(usize, expected, 10);
        try testing.expectEqual(parsed, object.lean_unbox(o));
        return;
    }

    const header: *align(1) lean.lean_object = @ptrCast(o.?);
    try testing.expectEqual(lean.LeanMPZ, header.m_tag);
    try testing.expectEqual(@as(i32, 1), header.m_rc);

    const actual = try mpz_object.mpzValue(o.?).toString(testing.allocator, 10);
    defer testing.allocator.free(actual);
    try testing.expectEqualStrings(expected, actual);
}

fn foldNatObject(obj: *anyopaque) ?*anyopaque {
    const value = mpz_object.mpzValue(obj);
    if (value.fitsSizeT()) {
        const small = value.getSizeT() catch unreachable;
        if (small <= max_small_nat) {
            alloc.lean_free_object(obj);
            return object.lean_box(small);
        }
    }
    return obj;
}

fn allocNatFromZig(value: anytype) ?*anyopaque {
    const obj = mpz_object.lean_alloc_mpz();
    mpz_object.mpzValue(obj).set(value) catch {
        alloc.lean_free_object(obj);
        @panic("bignum: out of memory");
    };
    return foldNatObject(obj);
}

pub export fn lean_nat_overflow_mul(_a1: usize, _a2: usize) callconv(.c) ?*anyopaque {
    _ = _a1;
    _ = _a2;
    io_min.lean_internal_panic(overflow_message);
    unreachable;
}

pub export fn lean_cstr_to_nat(n: [*:0]const u8) callconv(.c) ?*anyopaque {
    const obj = mpz_object.lean_alloc_mpz();
    mpz_object.mpzValue(obj).setStr(10, std.mem.span(n)) catch {
        alloc.lean_free_object(obj);
        @panic("lean_cstr_to_nat: invalid decimal");
    };
    return foldNatObject(obj);
}

pub export fn lean_big_usize_to_nat(n: usize) callconv(.c) ?*anyopaque {
    if (n <= max_small_nat) return object.lean_box(n);
    return allocNatFromZig(n);
}

pub export fn lean_big_uint64_to_nat(n: u64) callconv(.c) ?*anyopaque {
    if (n <= max_small_nat) return object.lean_box(@intCast(n));
    return allocNatFromZig(n);
}

test "lean_cstr_to_nat uses scalar and big results at the Nat boundary" {
    const zero = lean_cstr_to_nat("0");
    defer freeNatResult(zero);
    try expectNatValue(zero, "0", true);

    const one = lean_cstr_to_nat("1");
    defer freeNatResult(one);
    try expectNatValue(one, "1", true);

    var boundary_buf: [64]u8 = undefined;
    const boundary = try std.fmt.bufPrintZ(&boundary_buf, "{}", .{max_small_nat});
    const boxed_boundary = lean_cstr_to_nat(boundary);
    defer freeNatResult(boxed_boundary);
    try expectNatValue(boxed_boundary, boundary, true);

    var beyond_buf: [64]u8 = undefined;
    const beyond = try std.fmt.bufPrintZ(&beyond_buf, "{}", .{max_small_nat + 1});
    const big_boundary = lean_cstr_to_nat(beyond);
    defer freeNatResult(big_boundary);
    try expectNatValue(big_boundary, beyond, false);

    const big_decimal = lean_cstr_to_nat("10000000000000000000000000000000000000000");
    defer freeNatResult(big_decimal);
    try expectNatValue(big_decimal, "10000000000000000000000000000000000000000", false);
}

test "lean_big_usize_to_nat preserves values around LEAN_MAX_SMALL_NAT" {
    var small_buf: [64]u8 = undefined;
    const small_expected = try std.fmt.bufPrintZ(&small_buf, "{}", .{max_small_nat});
    const small = lean_big_usize_to_nat(max_small_nat);
    defer freeNatResult(small);
    try expectNatValue(small, small_expected, true);

    const big = lean_big_usize_to_nat(max_small_nat + 1);
    defer freeNatResult(big);
    var big_buf: [64]u8 = undefined;
    const expected = try std.fmt.bufPrintZ(&big_buf, "{}", .{max_small_nat + 1});
    try expectNatValue(big, expected, false);
}

test "lean_big_uint64_to_nat handles u64 inputs across scalar and big paths" {
    const small = lean_big_uint64_to_nat(1);
    defer freeNatResult(small);
    try expectNatValue(small, "1", true);

    const max_u64 = lean_big_uint64_to_nat(std.math.maxInt(u64));
    defer freeNatResult(max_u64);
    try expectNatValue(max_u64, "18446744073709551615", false);
}
