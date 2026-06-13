// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

//! Nat (arbitrary-precision natural number) arithmetic: small-nat fast
//! paths with big-nat fallbacks for add/sub/mul, division and modulo,
//! comparison and bitwise operations, and shifts/pow/gcd/log2.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const io_min = @import("io_min.zig");
const lean = @import("lean_object.zig");
const mpz_zig = @import("mpz_zig");
const mpz_object = @import("mpz_object.zig");
const nat_constructors = @import("nat_constructors.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

const max_small_nat: usize = std.math.maxInt(usize) >> 1;

// ===== Small-nat fast paths and add/sub/mul with big-nat overflow =====

const WideUsize = std.meta.Int(.unsigned, @bitSizeOf(usize) * 2);

fn freeNatResult(o: ?*anyopaque) void {
    if (!object.lean_is_scalar(o)) alloc.lean_free_object(o.?);
}

fn expectNatValue(o: ?*anyopaque, expected: []const u8, expect_scalar: bool) !void {
    try testing.expectEqual(expect_scalar, object.lean_is_scalar(o));
    if (expect_scalar) {
        try testing.expectEqual(try std.fmt.parseUnsigned(usize, expected, 10), object.lean_unbox(o));
        return;
    }

    const header: *align(1) lean.lean_object = @ptrCast(o.?);
    try testing.expectEqual(lean.LeanMPZ, header.m_tag);
    try testing.expectEqual(@as(i32, 1), header.m_rc);

    const actual = try mpz_object.mpzValue(o.?).toString(testing.allocator, 10);
    defer testing.allocator.free(actual);
    try testing.expectEqualStrings(expected, actual);
}

fn shareNat(o: *anyopaque) void {
    rc.lean_inc(o);
}

fn panicOutOfMemory() noreturn {
    @panic("bignum: out of memory");
}

fn natToMpz(o: *anyopaque) mpz_zig.Mpz {
    if (object.lean_is_scalar(o)) {
        return mpz_zig.Mpz.initSet(std.heap.c_allocator, object.lean_unbox(o)) catch panicOutOfMemory();
    }

    var value = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    value.copy(mpz_object.mpzValue(o)) catch panicOutOfMemory();
    return value;
}

fn foldNatResult(value: *const mpz_zig.Mpz) ?*anyopaque {
    if (value.fitsSizeT()) {
        const small = value.getSizeT() catch unreachable;
        if (small <= max_small_nat) return object.lean_box(small);
        return nat_constructors.lean_big_usize_to_nat(small);
    }
    if (value.fitsUint()) {
        return nat_constructors.lean_big_uint64_to_nat(value.getUint() catch unreachable);
    }

    const text = value.toString(std.heap.c_allocator, 10) catch panicOutOfMemory();
    defer std.heap.c_allocator.free(text);
    const ztext = std.heap.c_allocator.dupeZ(u8, text) catch panicOutOfMemory();
    defer std.heap.c_allocator.free(ztext);
    return nat_constructors.lean_cstr_to_nat(ztext);
}

fn succViaZig(a: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a);
    defer lhs.deinit();

    var one = mpz_zig.Mpz.initSet(std.heap.c_allocator, @as(u8, 1)) catch panicOutOfMemory();
    defer one.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.add(&lhs, &one) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn addViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.add(&lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn subViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();
    if (lhs.cmp(&rhs) < 0) return object.lean_box(0);

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.sub(&lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn mulViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.mul(&lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&result);
}

pub export fn lean_nat_big_succ(a: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a)) {
        const n = object.lean_unbox(a);
        if (n < max_small_nat) return object.lean_box(n + 1);
        return nat_constructors.lean_big_usize_to_nat(n + 1);
    }

    return succViaZig(a);
}

pub export fn lean_nat_big_add(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const lhs = object.lean_unbox(a1);
        const rhs = object.lean_unbox(a2);
        const sum = lhs + rhs;
        if (sum <= max_small_nat) return object.lean_box(sum);
        return nat_constructors.lean_big_usize_to_nat(sum);
    }

    return addViaZig(a1, a2);
}

pub export fn lean_nat_big_sub(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const lhs = object.lean_unbox(a1);
        const rhs = object.lean_unbox(a2);
        return object.lean_box(if (lhs < rhs) 0 else lhs - rhs);
    }

    return subViaZig(a1, a2);
}

pub export fn lean_nat_big_mul(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const lhs = object.lean_unbox(a1);
        const rhs = object.lean_unbox(a2);
        const product = @as(WideUsize, lhs) * @as(WideUsize, rhs);
        if (product <= max_small_nat) return object.lean_box(@intCast(product));
        if (product <= std.math.maxInt(usize)) return nat_constructors.lean_big_usize_to_nat(@intCast(product));
    }

    return mulViaZig(a1, a2);
}

test "nat arithmetic part 1 canonicalizes small and big results" {
    const succ_small = lean_nat_big_succ(object.lean_box(41).?);
    defer freeNatResult(succ_small);
    try expectNatValue(succ_small, "42", true);

    const add_big = lean_nat_big_add(object.lean_box(max_small_nat).?, object.lean_box(1).?);
    defer freeNatResult(add_big);
    try expectNatValue(add_big, "9223372036854775808", false);

    const lhs = @import("nat_constructors.zig").lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(lhs);
    const rhs = @import("nat_constructors.zig").lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(rhs);

    const mul_big = lean_nat_big_mul(lhs.?, rhs.?);
    defer freeNatResult(mul_big);
    try expectNatValue(mul_big, "6277101735386680763835789423207666416102355444464034512896", false);
}

test "nat arithmetic part 1 subtraction truncates and preserves shared rc" {
    const lhs = @import("nat_constructors.zig").lean_cstr_to_nat("9223372036854775815");
    defer freeNatResult(lhs);
    const rhs = @import("nat_constructors.zig").lean_cstr_to_nat("9223372036854775808");
    defer freeNatResult(rhs);

    shareNat(lhs.?);
    shareNat(rhs.?);
    defer rc.lean_dec(lhs);
    defer rc.lean_dec(rhs);

    const lhs_header: *align(1) lean.lean_object = @ptrCast(lhs.?);
    const rhs_header: *align(1) lean.lean_object = @ptrCast(rhs.?);
    const lhs_rc = lhs_header.m_rc;
    const rhs_rc = rhs_header.m_rc;

    const diff = lean_nat_big_sub(lhs.?, rhs.?);
    defer freeNatResult(diff);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try testing.expectEqual(rhs_rc, rhs_header.m_rc);
    try expectNatValue(diff, "7", true);

    const zero = lean_nat_big_sub(object.lean_box(7).?, object.lean_box(9).?);
    defer freeNatResult(zero);
    try expectNatValue(zero, "0", true);
}

// ===== Division, modulo, and related big-nat fallbacks =====

fn divViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (object.lean_is_scalar(a2) and object.lean_unbox(a2) == 0) return object.lean_box(0);
    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return object.lean_box(0);

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();
    if (rhs.sgn() == 0) return object.lean_box(0);

    var remainder = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer remainder.deinit();
    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    quotient.divFloor(&remainder, &lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&quotient);
}

fn divExactViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return object.lean_box(0);

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();
    if (rhs.sgn() == 0) return object.lean_box(0);

    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    quotient.divExact(&lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&quotient);
}

fn modViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return a1;
    if (object.lean_is_scalar(a2) and object.lean_unbox(a2) == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();
    if (rhs.sgn() == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }

    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    var remainder = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer remainder.deinit();
    quotient.divFloor(&remainder, &lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&remainder);
}

pub export fn lean_nat_big_div(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const rhs = object.lean_unbox(a2);
        return if (rhs == 0) object.lean_box(0) else object.lean_box(object.lean_unbox(a1) / rhs);
    }

    if (object.lean_is_scalar(a2) and object.lean_unbox(a2) == 0) return object.lean_box(0);
    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return object.lean_box(0);

    return divViaZig(a1, a2);
}

pub export fn lean_nat_big_div_exact(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const rhs = object.lean_unbox(a2);
        return if (rhs == 0) object.lean_box(0) else object.lean_box(object.lean_unbox(a1) / rhs);
    }

    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return object.lean_box(0);
    return divExactViaZig(a1, a2);
}

pub export fn lean_nat_big_mod(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const rhs = object.lean_unbox(a2);
        return if (rhs == 0) a1 else object.lean_box(object.lean_unbox(a1) % rhs);
    }

    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) return a1;
    if (object.lean_is_scalar(a2) and object.lean_unbox(a2) == 0) {
        rc.lean_inc(a1);
        return a1;
    }

    return modViaZig(a1, a2);
}

test "nat arithmetic part 2 canonicalizes quotient remainder and exact results" {
    const div_small = lean_nat_big_div(object.lean_box(42).?, object.lean_box(7).?);
    defer freeNatResult(div_small);
    try expectNatValue(div_small, "6", true);

    const lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(lhs);
    const rhs = nat_constructors.lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(rhs);

    const div_big = lean_nat_big_div(lhs.?, rhs.?);
    defer freeNatResult(div_big);
    try expectNatValue(div_big, "18446744073709551616", false);

    const exact_big = lean_nat_big_div_exact(lhs.?, rhs.?);
    defer freeNatResult(exact_big);
    try expectNatValue(exact_big, "18446744073709551616", false);

    const mod_lhs = nat_constructors.lean_cstr_to_nat("46116860184273879040");
    defer freeNatResult(mod_lhs);
    const mod_big = lean_nat_big_mod(mod_lhs.?, rhs.?);
    defer freeNatResult(mod_big);
    try expectNatValue(mod_big, "9223372036854775808", false);
}

test "nat arithmetic part 2 zero-divisor and rc paths match object.cpp" {
    const shared_lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(shared_lhs);
    const shared_rhs = nat_constructors.lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(shared_rhs);
    const mod_lhs = nat_constructors.lean_cstr_to_nat("46116860184273879040");
    defer freeNatResult(mod_lhs);

    const div_zero = lean_nat_big_div(shared_lhs.?, object.lean_box(0).?);
    defer freeNatResult(div_zero);
    try expectNatValue(div_zero, "0", true);
    try testing.expectEqual(object.lean_box(7), lean_nat_big_mod(object.lean_box(7).?, object.lean_box(0).?));

    shareNat(shared_lhs.?);
    shareNat(shared_rhs.?);
    defer rc.lean_dec(shared_lhs);
    defer rc.lean_dec(shared_rhs);

    const lhs_header: *align(1) lean.lean_object = @ptrCast(shared_lhs.?);
    const rhs_header: *align(1) lean.lean_object = @ptrCast(shared_rhs.?);

    const div_rc_before = lhs_header.m_rc;
    const rhs_rc_before = rhs_header.m_rc;
    const div_result = lean_nat_big_div(shared_lhs.?, shared_rhs.?);
    defer freeNatResult(div_result);
    try testing.expectEqual(div_rc_before, lhs_header.m_rc);
    try testing.expectEqual(rhs_rc_before, rhs_header.m_rc);
    try expectNatValue(div_result, "18446744073709551616", false);

    const exact_result = lean_nat_big_div_exact(shared_lhs.?, shared_rhs.?);
    defer freeNatResult(exact_result);
    try testing.expectEqual(div_rc_before, lhs_header.m_rc);
    try testing.expectEqual(rhs_rc_before, rhs_header.m_rc);
    try expectNatValue(exact_result, "18446744073709551616", false);

    shareNat(mod_lhs.?);
    defer rc.lean_dec(mod_lhs);
    const mod_header: *align(1) lean.lean_object = @ptrCast(mod_lhs.?);
    const mod_rc_before = mod_header.m_rc;
    const mod_result = lean_nat_big_mod(mod_lhs.?, shared_rhs.?);
    defer freeNatResult(mod_result);
    try testing.expectEqual(mod_rc_before, mod_header.m_rc);
    try testing.expectEqual(rhs_rc_before, rhs_header.m_rc);
    try expectNatValue(mod_result, "9223372036854775808", false);

    const mod_zero_before = lhs_header.m_rc;
    const mod_zero = lean_nat_big_mod(shared_lhs.?, object.lean_box(0).?);
    try testing.expectEqual(shared_lhs.?, mod_zero.?);
    try testing.expectEqual(mod_zero_before + 1, lhs_header.m_rc);
    rc.lean_dec(mod_zero);
}

// ===== Comparison and bitwise operations =====

const BitOp = enum { and_, or_, xor_ };

fn cmpViaZig(a1: *anyopaque, a2: *anyopaque) i8 {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();
    return lhs.cmp(&rhs);
}

fn bitwiseViaZig(op: BitOp, a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    switch (op) {
        .and_ => result.bitAnd(&lhs, &rhs) catch panicOutOfMemory(),
        .or_ => result.bitOr(&lhs, &rhs) catch panicOutOfMemory(),
        .xor_ => result.bitXor(&lhs, &rhs) catch panicOutOfMemory(),
    }
    return foldNatResult(&result);
}

pub export fn lean_nat_big_eq(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) return a1 == a2;
    return cmpViaZig(a1, a2) == 0;
}

pub export fn lean_nat_big_le(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return object.lean_unbox(a1) <= object.lean_unbox(a2);
    }
    return cmpViaZig(a1, a2) <= 0;
}

pub export fn lean_nat_big_lt(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return object.lean_unbox(a1) < object.lean_unbox(a2);
    }
    return cmpViaZig(a1, a2) < 0;
}

pub export fn lean_nat_big_land(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return object.lean_box(object.lean_unbox(a1) & object.lean_unbox(a2));
    }
    return bitwiseViaZig(.and_, a1, a2);
}

pub export fn lean_nat_big_lor(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return object.lean_box(object.lean_unbox(a1) | object.lean_unbox(a2));
    }
    return bitwiseViaZig(.or_, a1, a2);
}

pub export fn lean_nat_big_xor(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        return object.lean_box(object.lean_unbox(a1) ^ object.lean_unbox(a2));
    }
    return bitwiseViaZig(.xor_, a1, a2);
}

test "nat compare and bitwise match expected mixed-path semantics" {
    try testing.expect(lean_nat_big_eq(object.lean_box(7).?, object.lean_box(7).?));
    try testing.expect(lean_nat_big_le(object.lean_box(7).?, object.lean_box(9).?));
    try testing.expect(lean_nat_big_lt(object.lean_box(7).?, object.lean_box(9).?));

    const lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(lhs);
    const rhs = nat_constructors.lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(rhs);

    try testing.expect(!lean_nat_big_eq(lhs.?, rhs.?));
    try testing.expect(!lean_nat_big_le(lhs.?, rhs.?));
    try testing.expect(!lean_nat_big_lt(lhs.?, rhs.?));
    try testing.expect(lean_nat_big_lt(rhs.?, lhs.?));

    const land = lean_nat_big_land(lhs.?, rhs.?);
    defer freeNatResult(land);
    try expectNatValue(land, "0", true);

    const lor = lean_nat_big_lor(lhs.?, object.lean_box(0).?);
    defer freeNatResult(lor);
    try expectNatValue(lor, "340282366920938463463374607431768211456", false);

    const xor = lean_nat_big_xor(lhs.?, lhs.?);
    defer freeNatResult(xor);
    try expectNatValue(xor, "0", true);
}

test "nat compare does not consume args and bitwise identities hold" {
    const lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(lhs);
    const rhs = nat_constructors.lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(rhs);

    shareNat(lhs.?);
    shareNat(rhs.?);
    defer rc.lean_dec(lhs);
    defer rc.lean_dec(rhs);

    const lhs_header: *align(1) lean.lean_object = @ptrCast(lhs.?);
    const rhs_header: *align(1) lean.lean_object = @ptrCast(rhs.?);
    const lhs_rc = lhs_header.m_rc;
    const rhs_rc = rhs_header.m_rc;

    _ = lean_nat_big_eq(lhs.?, rhs.?);
    _ = lean_nat_big_le(lhs.?, rhs.?);
    _ = lean_nat_big_lt(lhs.?, rhs.?);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try testing.expectEqual(rhs_rc, rhs_header.m_rc);

    const land_zero = lean_nat_big_land(lhs.?, object.lean_box(0).?);
    defer freeNatResult(land_zero);
    try expectNatValue(land_zero, "0", true);

    const xor_zero = lean_nat_big_xor(lhs.?, object.lean_box(0).?);
    defer freeNatResult(xor_zero);
    try expectNatValue(xor_zero, "340282366920938463463374607431768211456", false);
}

// ===== Shifts, pow, gcd, and log2 =====

const max_uint_exponent: usize = std.math.maxInt(c_uint);
const shiftl_panic_message: [:0]const u8 = "Nat.shiftl exponent is too big";
const shiftr_panic_message: [:0]const u8 = "Nat.shiftr exponent is too big";
const pow_panic_message: [:0]const u8 = "Nat.pow exponent is too big";

fn natLog2Scalar(value: usize) usize {
    var result: usize = 0;
    var n = value;
    while (n >= 2) : (n /= 2) result += 1;
    return result;
}

fn shiftlViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_unbox(a1) == 0) return object.lean_box(0);
    if (!object.lean_is_scalar(a2) or object.lean_unbox(a2) > max_uint_exponent) {
        io_min.lean_internal_panic(shiftl_panic_message);
        unreachable;
    }

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.mul2k(&lhs, object.lean_unbox(a2)) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn shiftrViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (!object.lean_is_scalar(a2)) return object.lean_box(0);

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    const shift = object.lean_unbox(a2);
    if (shift > max_uint_exponent) {
        if (lhs.log2() >= shift) {
            io_min.lean_internal_panic(shiftr_panic_message);
            unreachable;
        }
        return object.lean_box(0);
    }

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.div2k(&lhs, shift) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn powViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    if (!object.lean_is_scalar(a2) or object.lean_unbox(a2) > max_uint_exponent) {
        io_min.lean_internal_panic(pow_panic_message);
        unreachable;
    }

    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.pow(&lhs, @intCast(object.lean_unbox(a2))) catch panicOutOfMemory();
    return foldNatResult(&result);
}

fn gcdViaZig(a1: *anyopaque, a2: *anyopaque) ?*anyopaque {
    var lhs = natToMpz(a1);
    defer lhs.deinit();
    var rhs = natToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.gcd(&lhs, &rhs) catch panicOutOfMemory();
    return foldNatResult(&result);
}

pub export fn lean_nat_shiftl(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a1) and object.lean_unbox(a1) == 0) return object.lean_box(0);
    return shiftlViaZig(a1, a2);
}

pub export fn lean_nat_big_shiftr(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    if (!object.lean_is_scalar(a2)) return object.lean_box(0);
    return shiftrViaZig(a1, a2);
}

pub export fn lean_nat_pow(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    return powViaZig(a1, a2);
}

pub export fn lean_nat_gcd(a1: *anyopaque, a2: *anyopaque) callconv(.c) ?*anyopaque {
    return gcdViaZig(a1, a2);
}

pub export fn lean_nat_log2(a: *anyopaque) callconv(.c) ?*anyopaque {
    if (object.lean_is_scalar(a)) return object.lean_box(natLog2Scalar(object.lean_unbox(a)));
    return object.lean_box(mpz_object.mpzValue(a).log2());
}

test "nat shift pow gcd log2 match mixed-path semantics" {
    const shift_base = nat_constructors.lean_cstr_to_nat("18446744073709551616");
    defer freeNatResult(shift_base);

    const shiftl = lean_nat_shiftl(shift_base.?, object.lean_box(12).?);
    defer freeNatResult(shiftl);
    try expectNatValue(shiftl, "75557863725914323419136", false);

    const shiftr = lean_nat_big_shiftr(shiftl.?, object.lean_box(72).?);
    defer freeNatResult(shiftr);
    try expectNatValue(shiftr, "16", true);

    const shiftr_zero = lean_nat_big_shiftr(shift_base.?, object.lean_box(max_uint_exponent + 1).?);
    defer freeNatResult(shiftr_zero);
    try expectNatValue(shiftr_zero, "0", true);

    const pow = lean_nat_pow(shift_base.?, object.lean_box(2).?);
    defer freeNatResult(pow);
    try expectNatValue(pow, "340282366920938463463374607431768211456", false);

    const gcd_lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(gcd_lhs);
    const gcd_rhs = nat_constructors.lean_cstr_to_nat("36893488147419103232");
    defer freeNatResult(gcd_rhs);
    const gcd = lean_nat_gcd(gcd_lhs.?, gcd_rhs.?);
    defer freeNatResult(gcd);
    try expectNatValue(gcd, "36893488147419103232", false);

    const gcd_zero = lean_nat_gcd(object.lean_box(0).?, gcd_rhs.?);
    defer freeNatResult(gcd_zero);
    try expectNatValue(gcd_zero, "36893488147419103232", false);

    const log2_big = lean_nat_log2(gcd_lhs.?);
    defer freeNatResult(log2_big);
    try expectNatValue(log2_big, "128", true);

    const log2_zero = lean_nat_log2(object.lean_box(0).?);
    defer freeNatResult(log2_zero);
    try expectNatValue(log2_zero, "0", true);
}

test "nat shift pow gcd log2 preserve rc discipline" {
    const lhs = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211456");
    defer freeNatResult(lhs);
    const rhs = nat_constructors.lean_cstr_to_nat("36893488147419103232");
    defer freeNatResult(rhs);

    shareNat(lhs.?);
    shareNat(rhs.?);
    defer rc.lean_dec(lhs);
    defer rc.lean_dec(rhs);

    const lhs_header: *align(1) lean.lean_object = @ptrCast(lhs.?);
    const rhs_header: *align(1) lean.lean_object = @ptrCast(rhs.?);
    const lhs_rc = lhs_header.m_rc;
    const rhs_rc = rhs_header.m_rc;

    const shiftl = lean_nat_shiftl(lhs.?, object.lean_box(1).?);
    defer freeNatResult(shiftl);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try expectNatValue(shiftl, "680564733841876926926749214863536422912", false);

    const shiftr = lean_nat_big_shiftr(lhs.?, object.lean_box(64).?);
    defer freeNatResult(shiftr);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try expectNatValue(shiftr, "18446744073709551616", false);

    const pow = lean_nat_pow(rhs.?, object.lean_box(2).?);
    defer freeNatResult(pow);
    try testing.expectEqual(rhs_rc, rhs_header.m_rc);
    try expectNatValue(pow, "1361129467683753853853498429727072845824", false);

    const gcd = lean_nat_gcd(lhs.?, rhs.?);
    defer freeNatResult(gcd);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try testing.expectEqual(rhs_rc, rhs_header.m_rc);
    try expectNatValue(gcd, "36893488147419103232", false);

    const log2 = lean_nat_log2(lhs.?);
    defer freeNatResult(log2);
    try testing.expectEqual(lhs_rc, lhs_header.m_rc);
    try expectNatValue(log2, "128", true);
}
