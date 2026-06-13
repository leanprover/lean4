const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const mpz_zig = @import("mpz_zig");
const mpz_object = @import("mpz_object.zig");
const nat_constructors = @import("nat_constructors.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

const max_small_nat: usize = std.math.maxInt(usize) >> 1;
const max_small_int: i64 = if (@sizeOf(usize) == 8) std.math.maxInt(c_int) else std.math.maxInt(c_int) >> 1;
const min_small_int: i64 = if (@sizeOf(usize) == 8) std.math.minInt(c_int) else std.math.minInt(c_int) >> 1;

fn panicOutOfMemory() noreturn {
    @panic("bignum: out of memory");
}

fn freeIntResult(o: *anyopaque) void {
    if (!object.lean_is_scalar(o)) alloc.lean_free_object(o);
}

fn scalarToInt64(o: *anyopaque) i64 {
    const raw: u32 = @truncate(object.lean_unbox(o));
    const signed: i32 = @bitCast(raw);
    return signed;
}

fn boxInt(value: i64) *anyopaque {
    std.debug.assert(min_small_int <= value and value <= max_small_int);
    const small: c_int = @intCast(value);
    const bits: u32 = @bitCast(small);
    return object.lean_box(bits).?;
}

fn intToMpz(o: *anyopaque) mpz_zig.Mpz {
    if (object.lean_is_scalar(o)) {
        return mpz_zig.Mpz.initSet(std.heap.c_allocator, scalarToInt64(o)) catch panicOutOfMemory();
    }

    var value = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    value.copy(mpz_object.mpzValue(o)) catch panicOutOfMemory();
    return value;
}

fn cloneToLeanMpz(value: *const mpz_zig.Mpz) *anyopaque {
    const obj = mpz_object.lean_alloc_mpz();
    mpz_object.mpzValue(obj).copy(value) catch {
        alloc.lean_free_object(obj);
        panicOutOfMemory();
    };
    return obj;
}

fn allocBigIntFromValue(value: anytype) *anyopaque {
    const obj = mpz_object.lean_alloc_mpz();
    mpz_object.mpzValue(obj).set(value) catch {
        alloc.lean_free_object(obj);
        panicOutOfMemory();
    };
    return obj;
}

fn allocBigIntFromString(value: []const u8) *anyopaque {
    const obj = mpz_object.lean_alloc_mpz();
    mpz_object.mpzValue(obj).setStr(10, value) catch {
        alloc.lean_free_object(obj);
        @panic("lean_cstr_to_int: invalid decimal");
    };
    return obj;
}

fn foldIntResult(value: *const mpz_zig.Mpz) *anyopaque {
    if (value.fitsInt()) {
        const small = value.getInt() catch unreachable;
        if (min_small_int <= small and small <= max_small_int) return boxInt(small);
    }
    return cloneToLeanMpz(value);
}

fn mpzToNatResult(value: *const mpz_zig.Mpz) *anyopaque {
    if (value.fitsSizeT()) {
        const small = value.getSizeT() catch unreachable;
        if (small <= max_small_nat) return object.lean_box(small).?;
        return nat_constructors.lean_big_usize_to_nat(small).?;
    }
    if (value.fitsUint()) {
        return nat_constructors.lean_big_uint64_to_nat(value.getUint() catch unreachable).?;
    }

    const text = value.toString(std.heap.c_allocator, 10) catch panicOutOfMemory();
    defer std.heap.c_allocator.free(text);
    const ztext = std.heap.c_allocator.dupeZ(u8, text) catch panicOutOfMemory();
    defer std.heap.c_allocator.free(ztext);
    return nat_constructors.lean_cstr_to_nat(ztext).?;
}

fn intEqViaZig(a1: *anyopaque, a2: *anyopaque) bool {
    return intCmpViaZig(a1, a2) == 0;
}

fn intCmpViaZig(a1: *anyopaque, a2: *anyopaque) i8 {
    if (object.lean_is_scalar(a1) and object.lean_is_scalar(a2)) {
        const lhs = scalarToInt64(a1);
        const rhs = scalarToInt64(a2);
        return if (lhs < rhs) -1 else if (lhs > rhs) 1 else 0;
    }
    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();
    return lhs.cmp(&rhs);
}

fn bigIntToNatViaZig(a: *anyopaque) *anyopaque {
    var value = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer value.deinit();
    value.copy(mpz_object.mpzValue(a)) catch panicOutOfMemory();
    rc.lean_dec(a);
    return mpzToNatResult(&value);
}

fn negViaZig(a: *anyopaque) *anyopaque {
    var lhs = intToMpz(a);
    defer lhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.neg(&lhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

fn addViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.add(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

fn subViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.sub(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

fn mulViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.mul(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

fn divViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) return a2;

    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var remainder = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer remainder.deinit();
    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    quotient.divTruncQR(&remainder, &lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&quotient);
}

fn divExactViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    if (object.lean_is_scalar(a1) and !object.lean_is_scalar(a2)) {
        return if (scalarToInt64(a1) == 0) a1 else boxInt(-1);
    }

    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    quotient.divExact(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&quotient);
}

fn modViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }

    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var quotient = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer quotient.deinit();
    var remainder = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer remainder.deinit();
    quotient.divTruncQR(&remainder, &lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&remainder);
}

fn edivViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) return a2;

    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.ediv(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

fn emodViaZig(a1: *anyopaque, a2: *anyopaque) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }

    var lhs = intToMpz(a1);
    defer lhs.deinit();
    var rhs = intToMpz(a2);
    defer rhs.deinit();

    var result = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer result.deinit();
    result.emod(&lhs, &rhs) catch panicOutOfMemory();
    return foldIntResult(&result);
}

export fn lean_int_big_neg(a: *anyopaque) callconv(.c) *anyopaque {
    return negViaZig(a);
}

export fn lean_int_big_add(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    return addViaZig(a1, a2);
}

export fn lean_int_big_sub(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    return subViaZig(a1, a2);
}

export fn lean_int_big_mul(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    return mulViaZig(a1, a2);
}

export fn lean_int_big_div(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) return a2;
    return divViaZig(a1, a2);
}

export fn lean_int_big_div_exact(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    return divExactViaZig(a1, a2);
}

export fn lean_int_big_mod(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }
    return modViaZig(a1, a2);
}

export fn lean_int_big_ediv(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) return a2;
    return edivViaZig(a1, a2);
}

export fn lean_int_big_emod(a1: *anyopaque, a2: *anyopaque) callconv(.c) *anyopaque {
    if (object.lean_is_scalar(a2) and scalarToInt64(a2) == 0) {
        if (!object.lean_is_scalar(a1)) rc.lean_inc(a1);
        return a1;
    }
    return emodViaZig(a1, a2);
}

export fn lean_int_big_eq(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    return intEqViaZig(a1, a2);
}

export fn lean_int_big_le(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    return intCmpViaZig(a1, a2) <= 0;
}

export fn lean_int_big_lt(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    return intCmpViaZig(a1, a2) < 0;
}

export fn lean_int_big_nonneg(a: *anyopaque) callconv(.c) bool {
    if (object.lean_is_scalar(a)) return scalarToInt64(a) >= 0;
    return mpz_object.mpzValue(a).sgn() >= 0;
}

export fn lean_cstr_to_int(n: [*:0]const u8) callconv(.c) *anyopaque {
    var value = mpz_zig.Mpz.init(std.heap.c_allocator) catch panicOutOfMemory();
    defer value.deinit();
    value.setStr(10, std.mem.span(n)) catch @panic("lean_cstr_to_int: invalid decimal");
    return foldIntResult(&value);
}

export fn lean_big_int_to_int(n: c_int) callconv(.c) *anyopaque {
    return allocBigIntFromValue(n);
}

export fn lean_big_size_t_to_int(n: usize) callconv(.c) *anyopaque {
    return allocBigIntFromValue(n);
}

export fn lean_big_int64_to_int(n: i64) callconv(.c) *anyopaque {
    if (min_small_int <= n and n <= max_small_int) return boxInt(n);
    return allocBigIntFromValue(n);
}

export fn lean_big_int_to_nat(a: *anyopaque) callconv(.c) *anyopaque {
    return bigIntToNatViaZig(a);
}

pub export fn leanrt_test_int_eq_cstr(o: *anyopaque, value: [*:0]const u8) callconv(.c) u8 {
    const expected = lean_cstr_to_int(value);
    defer freeIntResult(expected);
    return @intFromBool(lean_int_big_eq(o, expected));
}

fn expectIntValue(o: *anyopaque, expected: []const u8, expect_scalar: bool) !void {
    try testing.expectEqual(expect_scalar, object.lean_is_scalar(o));
    if (expect_scalar) {
        try testing.expectEqual(try std.fmt.parseInt(i64, expected, 10), scalarToInt64(o));
        return;
    }

    const header: *align(1) lean.lean_object = @ptrCast(o);
    try testing.expectEqual(lean.LeanMPZ, header.m_tag);
    try testing.expectEqual(@as(i32, 1), header.m_rc);

    const actual = try mpz_object.mpzValue(o).toString(testing.allocator, 10);
    defer testing.allocator.free(actual);
    try testing.expectEqualStrings(expected, actual);
}

test "int constructors round-trip signs and boundaries" {
    const zero = lean_cstr_to_int("0");
    defer freeIntResult(zero);
    try expectIntValue(zero, "0", true);

    const neg = lean_cstr_to_int("-42");
    defer freeIntResult(neg);
    try expectIntValue(neg, "-42", true);

    const big_neg = lean_cstr_to_int("-1234567890123456789012");
    defer freeIntResult(big_neg);
    try expectIntValue(big_neg, "-1234567890123456789012", false);
    try testing.expect(!lean_int_big_nonneg(big_neg));

    const small_big = lean_big_int_to_int(-17);
    defer freeIntResult(small_big);
    try expectIntValue(small_big, "-17", false);

    const big_size = lean_big_size_t_to_int(std.math.maxInt(usize));
    defer freeIntResult(big_size);
    try expectIntValue(big_size, "18446744073709551615", false);
    try testing.expect(lean_int_big_nonneg(big_size));

    const int64_min = lean_big_int64_to_int(std.math.minInt(i64));
    defer freeIntResult(int64_min);
    try expectIntValue(int64_min, "-9223372036854775808", false);
    try testing.expect(!lean_int_big_nonneg(int64_min));

    const int64_min_copy = lean_big_int64_to_int(std.math.minInt(i64));
    defer freeIntResult(int64_min_copy);
    try testing.expect(lean_int_big_eq(int64_min, int64_min_copy));
}

test "lean_big_int_to_nat consumes its mpz input" {
    alloc.resetTestCounters();
    const input = mpz_object.leanrt_test_alloc_mpz_from_cstr("18446744073709551616");
    const free_before = alloc.testFreeCount();
    const result = lean_big_int_to_nat(input);
    defer if (!object.lean_is_scalar(result)) alloc.lean_free_object(result);

    try testing.expectEqual(free_before + 1, alloc.testFreeCount());
    try testing.expect(!object.lean_is_scalar(result));
    const actual = try mpz_object.mpzValue(result).toString(testing.allocator, 10);
    defer testing.allocator.free(actual);
    try testing.expectEqualStrings("18446744073709551616", actual);
}

fn nextStressWord(state: *u64) u64 {
    var x = state.*;
    x ^= x << 7;
    x ^= x >> 9;
    x ^= x << 8;
    state.* = x;
    return x;
}

fn stressLiteral(index: usize) [*:0]const u8 {
    const values = [_][:0]const u8{
        "0",
        "42",
        "-42",
        "2147483648",
        "-2147483649",
        "18446744073709551616",
        "-18446744073709551616",
        "340282366920938463463374607431768211456",
        "-340282366920938463463374607431768211456",
    };
    return values[index % values.len].ptr;
}

test "int arithmetic part 1 preserves rc and algebraic invariants" {
    const zero = lean_cstr_to_int("0");
    defer freeIntResult(zero);
    const a = lean_cstr_to_int("340282366920938463463374607431768211456");
    defer freeIntResult(a);
    const b = lean_cstr_to_int("-18446744073709551616");
    defer freeIntResult(b);

    rc.lean_inc(a);
    rc.lean_inc(b);
    defer rc.lean_dec(a);
    defer rc.lean_dec(b);

    const a_header: *align(1) lean.lean_object = @ptrCast(a);
    const b_header: *align(1) lean.lean_object = @ptrCast(b);
    const a_rc = a_header.m_rc;
    const b_rc = b_header.m_rc;

    const neg_zero = lean_int_big_neg(zero);
    defer freeIntResult(neg_zero);
    try testing.expect(lean_int_big_nonneg(neg_zero));

    const neg_a = lean_int_big_neg(a);
    defer freeIntResult(neg_a);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expect(!object.lean_is_scalar(neg_a));
    try testing.expectEqual(@as(i32, 1), (@as(*align(1) lean.lean_object, @ptrCast(neg_a))).m_rc);

    const negneg_a = lean_int_big_neg(neg_a);
    defer freeIntResult(negneg_a);
    try testing.expect(lean_int_big_eq(negneg_a, a));

    const add_ab = lean_int_big_add(a, b);
    defer freeIntResult(add_ab);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);

    const add_ba = lean_int_big_add(b, a);
    defer freeIntResult(add_ba);
    try testing.expect(lean_int_big_eq(add_ab, add_ba));

    const sub_back = lean_int_big_sub(add_ab, b);
    defer freeIntResult(sub_back);
    try testing.expect(lean_int_big_eq(sub_back, a));

    const mul_ab = lean_int_big_mul(a, b);
    defer freeIntResult(mul_ab);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);
    try testing.expect(!lean_int_big_nonneg(mul_ab));

    const mul_ba = lean_int_big_mul(b, a);
    defer freeIntResult(mul_ba);
    try testing.expect(lean_int_big_eq(mul_ab, mul_ba));
}

test "int arithmetic part 1 randomized stress balances mpz allocations" {
    alloc.resetTestCounters();

    var state: u64 = 0xdecafbad12345678;
    var i: usize = 0;
    while (i < 10_000) : (i += 1) {
        const a = lean_cstr_to_int(stressLiteral(nextStressWord(&state)));
        const b = lean_cstr_to_int(stressLiteral(nextStressWord(&state)));

        switch (nextStressWord(&state) % 4) {
            0 => {
                const result = lean_int_big_neg(a);
                freeIntResult(result);
            },
            1 => {
                const result = lean_int_big_add(a, b);
                freeIntResult(result);
            },
            2 => {
                const result = lean_int_big_sub(a, b);
                freeIntResult(result);
            },
            else => {
                const result = lean_int_big_mul(a, b);
                freeIntResult(result);
            },
        }

        freeIntResult(a);
        freeIntResult(b);
    }

    try testing.expectEqual(alloc.testAllocCount(), alloc.testFreeCount());
}

test "int division family matches truncating exact and euclidean semantics" {
    const trunc_lhs = lean_cstr_to_int("-7");
    defer freeIntResult(trunc_lhs);
    const trunc_rhs = lean_cstr_to_int("3");
    defer freeIntResult(trunc_rhs);
    const trunc_div = lean_int_big_div(trunc_lhs, trunc_rhs);
    defer freeIntResult(trunc_div);
    try expectIntValue(trunc_div, "-2", true);

    const trunc_mod = lean_int_big_mod(trunc_lhs, trunc_rhs);
    defer freeIntResult(trunc_mod);
    try expectIntValue(trunc_mod, "-1", true);

    const euclid_div = lean_int_big_ediv(trunc_lhs, trunc_rhs);
    defer freeIntResult(euclid_div);
    try expectIntValue(euclid_div, "-3", true);

    const euclid_mod = lean_int_big_emod(trunc_lhs, trunc_rhs);
    defer freeIntResult(euclid_mod);
    try expectIntValue(euclid_mod, "2", true);
    try testing.expect(lean_int_big_nonneg(euclid_mod));

    const neg_rhs = lean_cstr_to_int("-3");
    defer freeIntResult(neg_rhs);
    const trunc_neg = lean_int_big_div(trunc_lhs, neg_rhs);
    defer freeIntResult(trunc_neg);
    try expectIntValue(trunc_neg, "2", true);

    const euclid_neg = lean_int_big_ediv(trunc_lhs, neg_rhs);
    defer freeIntResult(euclid_neg);
    try expectIntValue(euclid_neg, "3", true);

    const euclid_mod_neg = lean_int_big_emod(trunc_lhs, neg_rhs);
    defer freeIntResult(euclid_mod_neg);
    try expectIntValue(euclid_mod_neg, "2", true);
    try testing.expect(lean_int_big_nonneg(euclid_mod_neg));

    const pos_lhs = lean_cstr_to_int("7");
    defer freeIntResult(pos_lhs);
    const trunc_pos_neg = lean_int_big_div(pos_lhs, neg_rhs);
    defer freeIntResult(trunc_pos_neg);
    try expectIntValue(trunc_pos_neg, "-2", true);

    const exact_lhs = lean_cstr_to_int("18446744073709551616");
    defer freeIntResult(exact_lhs);
    const exact_rhs = lean_cstr_to_int("-4294967296");
    defer freeIntResult(exact_rhs);
    const exact_div = lean_int_big_div_exact(exact_lhs, exact_rhs);
    defer freeIntResult(exact_div);
    try expectIntValue(exact_div, "-4294967296", false);

    const int64_min = lean_big_int64_to_int(std.math.minInt(i64));
    defer freeIntResult(int64_min);
    const minus_one = lean_cstr_to_int("-1");
    defer freeIntResult(minus_one);
    const min_div = lean_int_big_div(int64_min, minus_one);
    defer freeIntResult(min_div);
    try expectIntValue(min_div, "9223372036854775808", false);

    const min_ediv = lean_int_big_ediv(int64_min, minus_one);
    defer freeIntResult(min_ediv);
    try expectIntValue(min_ediv, "9223372036854775808", false);

    const product = lean_int_big_mul(euclid_div, trunc_rhs);
    defer freeIntResult(product);
    const recomposed = lean_int_big_add(product, euclid_mod);
    defer freeIntResult(recomposed);
    try testing.expect(lean_int_big_eq(recomposed, trunc_lhs));
}

test "int division family zero-divisor and rc paths mirror object.cpp" {
    const zero = lean_cstr_to_int("0");
    defer freeIntResult(zero);
    const a = lean_cstr_to_int("340282366920938463463374607431768211456");
    defer freeIntResult(a);
    const b = lean_cstr_to_int("-18446744073709551616");
    defer freeIntResult(b);

    const div_zero = lean_int_big_div(a, zero);
    defer freeIntResult(div_zero);
    try testing.expectEqual(zero, div_zero);

    const ediv_zero = lean_int_big_ediv(a, zero);
    defer freeIntResult(ediv_zero);
    try testing.expectEqual(zero, ediv_zero);

    const a_header: *align(1) lean.lean_object = @ptrCast(a);
    const mod_zero_before = a_header.m_rc;
    const mod_zero = lean_int_big_mod(a, zero);
    try testing.expectEqual(a, mod_zero);
    try testing.expectEqual(mod_zero_before + 1, a_header.m_rc);
    rc.lean_dec(mod_zero);

    const emod_zero_before = a_header.m_rc;
    const emod_zero = lean_int_big_emod(a, zero);
    try testing.expectEqual(a, emod_zero);
    try testing.expectEqual(emod_zero_before + 1, a_header.m_rc);
    rc.lean_dec(emod_zero);

    rc.lean_inc(a);
    rc.lean_inc(b);
    defer rc.lean_dec(a);
    defer rc.lean_dec(b);

    const a_rc = a_header.m_rc;
    const b_header: *align(1) lean.lean_object = @ptrCast(b);
    const b_rc = b_header.m_rc;

    const div_result = lean_int_big_div(a, b);
    defer freeIntResult(div_result);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);
    try testing.expectEqual(@as(i32, 1), (@as(*align(1) lean.lean_object, @ptrCast(div_result))).m_rc);

    const exact_lhs = lean_cstr_to_int("18446744073709551616");
    defer freeIntResult(exact_lhs);
    const exact_rhs = lean_cstr_to_int("-4294967296");
    defer freeIntResult(exact_rhs);
    const exact_result = lean_int_big_div_exact(exact_lhs, exact_rhs);
    defer freeIntResult(exact_result);
    try expectIntValue(exact_result, "-4294967296", false);

    const mod_result = lean_int_big_mod(a, b);
    defer freeIntResult(mod_result);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);

    const ediv_result = lean_int_big_ediv(a, b);
    defer freeIntResult(ediv_result);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);

    const emod_result = lean_int_big_emod(a, b);
    defer freeIntResult(emod_result);
    try testing.expectEqual(a_rc, a_header.m_rc);
    try testing.expectEqual(b_rc, b_header.m_rc);
    try testing.expect(lean_int_big_nonneg(emod_result));
}

test "int compare matches cmp reflexivity and rc discipline" {
    const zero = lean_cstr_to_int("0");
    defer freeIntResult(zero);
    const pos = lean_cstr_to_int("340282366920938463463374607431768211456");
    defer freeIntResult(pos);
    const neg = lean_cstr_to_int("-18446744073709551616");
    defer freeIntResult(neg);

    try testing.expect(lean_int_big_eq(pos, pos));
    try testing.expect(lean_int_big_le(pos, pos));
    try testing.expect(!lean_int_big_lt(pos, pos));

    try testing.expect(!lean_int_big_eq(neg, pos));
    try testing.expect(lean_int_big_lt(neg, pos));
    try testing.expect(lean_int_big_le(neg, pos));
    try testing.expect(!lean_int_big_lt(pos, neg));
    try testing.expect(!lean_int_big_le(pos, neg));

    try testing.expect(lean_int_big_nonneg(zero));
    try testing.expect(lean_int_big_nonneg(pos));
    try testing.expect(!lean_int_big_nonneg(neg));

    rc.lean_inc(pos);
    rc.lean_inc(neg);
    defer rc.lean_dec(pos);
    defer rc.lean_dec(neg);

    const pos_header: *align(1) lean.lean_object = @ptrCast(pos);
    const neg_header: *align(1) lean.lean_object = @ptrCast(neg);
    const pos_rc = pos_header.m_rc;
    const neg_rc = neg_header.m_rc;

    _ = lean_int_big_eq(pos, neg);
    _ = lean_int_big_le(pos, neg);
    _ = lean_int_big_lt(pos, neg);
    _ = lean_int_big_nonneg(pos);
    try testing.expectEqual(pos_rc, pos_header.m_rc);
    try testing.expectEqual(neg_rc, neg_header.m_rc);
}
