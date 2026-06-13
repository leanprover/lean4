// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const big_int = std.math.big.int;

pub const Limb = std.math.big.Limb;
const Allocator = std.mem.Allocator;

fn orderSign(order: std.math.Order) i8 {
    return switch (order) {
        .lt => -1,
        .eq => 0,
        .gt => 1,
    };
}

pub const Mpz = struct {
    managed: big_int.Managed,

    pub fn init(alloc: Allocator) !Mpz {
        return .{ .managed = try big_int.Managed.init(alloc) };
    }

    pub fn initSet(alloc: Allocator, value: anytype) !Mpz {
        return .{ .managed = try big_int.Managed.initSet(alloc, value) };
    }

    pub fn deinit(self: *Mpz) void {
        self.managed.deinit();
    }

    pub fn getAllocator(self: *const Mpz) Allocator {
        return self.managed.allocator;
    }

    pub fn copy(self: *Mpz, other: *const Mpz) !void {
        try self.managed.copy(other.managed.toConst());
    }

    pub fn swap(self: *Mpz, other: *Mpz) void {
        self.managed.swap(&other.managed);
    }

    pub fn set(self: *Mpz, value: anytype) !void {
        try self.managed.set(value);
    }

    pub fn setStr(self: *Mpz, base: u8, value: []const u8) !void {
        try self.managed.setString(base, value);
    }

    pub fn toString(self: *const Mpz, alloc: Allocator, base: u8) ![]u8 {
        return self.managed.toString(alloc, base, .lower);
    }

    pub fn sgn(self: *const Mpz) i8 {
        return if (self.managed.toConst().eqlZero())
            0
        else if (self.managed.isPositive())
            1
        else
            -1;
    }

    pub fn cmp(lhs: *const Mpz, rhs: *const Mpz) i8 {
        return orderSign(lhs.managed.order(rhs.managed));
    }

    pub fn cmpInt(lhs: *const Mpz, rhs: i64) i8 {
        return orderSign(lhs.managed.toConst().orderAgainstScalar(rhs));
    }

    pub fn cmpUint(lhs: *const Mpz, rhs: u64) i8 {
        return orderSign(lhs.managed.toConst().orderAgainstScalar(rhs));
    }

    pub fn fitsInt(self: *const Mpz) bool {
        return self.managed.fits(i64);
    }

    pub fn fitsUint(self: *const Mpz) bool {
        return self.managed.fits(u64);
    }

    pub fn fitsSizeT(self: *const Mpz) bool {
        return self.managed.fits(usize);
    }

    pub fn getInt(self: *const Mpz) big_int.Const.ConvertError!i64 {
        return self.managed.toInt(i64);
    }

    pub fn getUint(self: *const Mpz) big_int.Const.ConvertError!u64 {
        return self.managed.toInt(u64);
    }

    pub fn getSizeT(self: *const Mpz) big_int.Const.ConvertError!usize {
        return self.managed.toInt(usize);
    }

    pub fn getLimb(self: *const Mpz, index: usize) Limb {
        return if (index < self.managed.len()) self.managed.limbs[index] else 0;
    }

    pub fn log2(self: *const Mpz) usize {
        const value = self.managed.toConst();
        return if (value.eqlZero()) 0 else value.bitCountAbs() - 1;
    }

    pub fn bitCountAbs(self: *const Mpz) usize {
        return self.managed.bitCountAbs();
    }

    pub fn add(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try result.managed.add(&lhs.managed, &rhs.managed);
    }

    pub fn sub(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try result.managed.sub(&lhs.managed, &rhs.managed);
    }

    pub fn mul(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try result.managed.mul(&lhs.managed, &rhs.managed);
    }

    pub fn divTruncQR(quotient: *Mpz, remainder: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        std.debug.assert(rhs.sgn() != 0);
        try quotient.managed.divTrunc(&remainder.managed, &lhs.managed, &rhs.managed);
    }

    pub fn divFloor(quotient: *Mpz, remainder: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        std.debug.assert(rhs.sgn() != 0);
        try quotient.managed.divFloor(&remainder.managed, &lhs.managed, &rhs.managed);
    }

    fn adjustEuclidean(quotient: *Mpz, remainder: *Mpz, divisor: *const Mpz) !void {
        if (remainder.sgn() >= 0) return;

        var one = try Mpz.initSet(quotient.getAllocator(), @as(u8, 1));
        defer one.deinit();
        if (divisor.sgn() > 0) {
            try quotient.sub(quotient, &one);
            try remainder.add(remainder, divisor);
        } else {
            try quotient.add(quotient, &one);
            try remainder.sub(remainder, divisor);
        }
    }

    pub fn ediv(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        std.debug.assert(rhs.sgn() != 0);
        var remainder = try Mpz.init(result.getAllocator());
        defer remainder.deinit();
        try result.divTruncQR(&remainder, lhs, rhs);
        try adjustEuclidean(result, &remainder, rhs);
    }

    pub fn emod(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        std.debug.assert(rhs.sgn() != 0);
        var quotient = try Mpz.init(result.getAllocator());
        defer quotient.deinit();
        try quotient.divTruncQR(result, lhs, rhs);
        try adjustEuclidean(&quotient, result, rhs);
    }

    pub fn divExact(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        std.debug.assert(rhs.sgn() != 0);
        var remainder = try Mpz.init(result.getAllocator());
        defer remainder.deinit();
        try result.divTruncQR(&remainder, lhs, rhs);
    }

    pub fn neg(result: *Mpz, value: *const Mpz) !void {
        try result.copy(value);
        result.managed.negate();
    }

    pub fn pow(result: *Mpz, value: *const Mpz, exponent: u32) !void {
        try result.managed.pow(&value.managed, exponent);
    }

    pub fn gcd(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try result.managed.ensureCapacity(@max(lhs.managed.len(), rhs.managed.len()));
        try result.managed.gcd(&lhs.managed, &rhs.managed);
    }

    fn bitwise(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz, comptime op: enum { and_, or_, xor_ }) !void {
        const bit_count = @max(
            lhs.managed.toConst().bitCountTwosCompForSignedness(.signed),
            rhs.managed.toConst().bitCountTwosCompForSignedness(.signed),
        ) + 1;
        const byte_count = @max(1, (bit_count + 7) / 8);

        const allocator = result.getAllocator();
        const lhs_bytes = try allocator.alloc(u8, byte_count);
        defer allocator.free(lhs_bytes);
        const rhs_bytes = try allocator.alloc(u8, byte_count);
        defer allocator.free(rhs_bytes);
        const out_bytes = try allocator.alloc(u8, byte_count);
        defer allocator.free(out_bytes);

        @memset(lhs_bytes, 0);
        @memset(rhs_bytes, 0);
        lhs.managed.toConst().writeTwosComplement(lhs_bytes, .little);
        rhs.managed.toConst().writeTwosComplement(rhs_bytes, .little);

        for (out_bytes, lhs_bytes, rhs_bytes) |*out, lhs_byte, rhs_byte| {
            out.* = switch (op) {
                .and_ => lhs_byte & rhs_byte,
                .or_ => lhs_byte | rhs_byte,
                .xor_ => lhs_byte ^ rhs_byte,
            };
        }

        try result.managed.ensureCapacity(big_int.calcTwosCompLimbCount(byte_count * 8));
        var mutable = result.managed.toMutable();
        mutable.readTwosComplement(out_bytes, byte_count * 8, .little, .signed);
        result.managed.setMetadata(mutable.positive, mutable.len);
    }

    pub fn bitAnd(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try bitwise(result, lhs, rhs, .and_);
    }

    pub fn bitOr(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try bitwise(result, lhs, rhs, .or_);
    }

    pub fn bitXor(result: *Mpz, lhs: *const Mpz, rhs: *const Mpz) !void {
        try bitwise(result, lhs, rhs, .xor_);
    }

    pub fn mul2k(result: *Mpz, value: *const Mpz, shift: usize) !void {
        try result.managed.shiftLeft(&value.managed, shift);
    }

    pub fn div2k(result: *Mpz, value: *const Mpz, shift: usize) !void {
        try result.managed.shiftRight(&value.managed, shift);
    }

    pub fn modPow2(result: *Mpz, value: *const Mpz, shift: usize) !void {
        var quotient = try Mpz.init(result.getAllocator());
        defer quotient.deinit();
        var scaled = try Mpz.init(result.getAllocator());
        defer scaled.deinit();

        try quotient.div2k(value, shift);
        try scaled.mul2k(&quotient, shift);
        try result.sub(value, &scaled);
    }

    fn setPow2(result: *Mpz, shift: usize) !void {
        try result.set(@as(u8, 1));
        try result.managed.shiftLeft(&result.managed, shift);
    }

    pub fn smodPow2(result: *Mpz, value: *const Mpz, shift: usize) !void {
        if (shift == 0) {
            try result.set(@as(u8, 0));
            return;
        }

        try result.modPow2(value, shift);

        var threshold = try Mpz.init(result.getAllocator());
        defer threshold.deinit();
        try threshold.setPow2(shift - 1);
        if (result.cmp(&threshold) < 0) return;

        var modulus = try Mpz.init(result.getAllocator());
        defer modulus.deinit();
        try modulus.setPow2(shift);
        try result.sub(result, &modulus);
    }
};

const c = struct {
    extern fn gmp_oracle_free_string(text: [*:0]u8) callconv(.c) void;
    extern fn gmp_oracle_add(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_sub(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_mul(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_div_trunc_qr(lhs: [*:0]const u8, rhs: [*:0]const u8, q: *[*:0]u8, r: *[*:0]u8) callconv(.c) void;
    extern fn gmp_oracle_div_floor(lhs: [*:0]const u8, rhs: [*:0]const u8, q: *[*:0]u8, r: *[*:0]u8) callconv(.c) void;
    extern fn gmp_oracle_ediv(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_emod(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_div_exact(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_neg(value: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_pow(value: [*:0]const u8, exponent: u32) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_gcd(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_bit_and(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_bit_or(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_bit_xor(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_mul_2exp(value: [*:0]const u8, shift: usize) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_fdiv_q_2exp(value: [*:0]const u8, shift: usize) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_fdiv_r_2exp(value: [*:0]const u8, shift: usize) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_smod_pow2(value: [*:0]const u8, shift: usize) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_cmp(lhs: [*:0]const u8, rhs: [*:0]const u8) callconv(.c) c_int;
    extern fn gmp_oracle_cmp_i64(lhs: [*:0]const u8, rhs: i64) callconv(.c) c_int;
    extern fn gmp_oracle_cmp_u64(lhs: [*:0]const u8, rhs: u64) callconv(.c) c_int;
    extern fn gmp_oracle_fits_i64(value: [*:0]const u8) callconv(.c) bool;
    extern fn gmp_oracle_fits_u64(value: [*:0]const u8) callconv(.c) bool;
    extern fn gmp_oracle_fits_size_t(value: [*:0]const u8) callconv(.c) bool;
    extern fn gmp_oracle_get_i64(value: [*:0]const u8) callconv(.c) i64;
    extern fn gmp_oracle_get_u64(value: [*:0]const u8) callconv(.c) u64;
    extern fn gmp_oracle_get_size_t(value: [*:0]const u8) callconv(.c) usize;
    extern fn gmp_oracle_get_limb(value: [*:0]const u8, index: usize) callconv(.c) c_ulonglong;
    extern fn gmp_oracle_to_string_base(value: [*:0]const u8, base: c_int) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_parse_base_to_base(value: [*:0]const u8, input_base: c_int, output_base: c_int) callconv(.c) [*:0]u8;
    extern fn gmp_oracle_log2_abs(value: [*:0]const u8) callconv(.c) usize;
    extern fn gmp_oracle_bit_count_abs(value: [*:0]const u8) callconv(.c) usize;
};

const shifts = [_]usize{ 0, 1, 2, 7, 8, 15, 16, 31, 32, 63, 64, 65, 127 };
const exponents = [_]u32{ 0, 1, 2, 3, 5, 16, 31, 64 };
const signed_scalars = [_]i64{
    -9223372036854775808,
    -65536,
    -1,
    0,
    1,
    65535,
    9223372036854775807,
};
const unsigned_scalars = [_]u64{
    0,
    1,
    65535,
    4294967295,
    18446744073709551615,
};

const OwnedString = struct {
    ptr: [*:0]u8,

    fn slice(self: OwnedString) []const u8 {
        return std.mem.span(self.ptr);
    }

    fn deinit(self: OwnedString) void {
        c.gmp_oracle_free_string(self.ptr);
    }
};

const OracleQR = struct {
    q: OwnedString,
    r: OwnedString,

    fn deinit(self: OracleQR) void {
        self.q.deinit();
        self.r.deinit();
    }
};

const FixtureSet = struct {
    values: [15][]const u8,

    fn init(allocator: Allocator) !FixtureSet {
        var fixtures: FixtureSet = undefined;
        fixtures.values[0] = "0";
        fixtures.values[1] = "1";
        fixtures.values[2] = "-1";
        fixtures.values[3] = "9223372036854775807";
        fixtures.values[4] = "-9223372036854775808";
        fixtures.values[5] = "18446744073709551616";

        var prng = std.Random.DefaultPrng.init(0x5eed_cafe_f00d_beef);
        var random = prng.random();
        const bit_counts = [_]usize{ 5, 31, 63, 64, 65, 127, 128, 191, 257 };
        for (bit_counts, 0..) |bits, index| {
            fixtures.values[6 + index] = try randomDecimal(allocator, &random, bits, true);
        }
        return fixtures;
    }
};

fn randomDecimal(allocator: Allocator, random: *std.Random, bit_count: usize, signed: bool) ![]const u8 {
    const hex_len = @max(1, (bit_count + 3) / 4);
    const negative = signed and random.boolean();
    var text = try allocator.alloc(u8, hex_len + @intFromBool(negative));
    var offset: usize = 0;
    if (negative) {
        text[0] = '-';
        offset = 1;
    }

    const digits = "0123456789abcdef";
    const first_nibble_bits = if (bit_count % 4 == 0) 4 else bit_count % 4;
    const first_limit: u8 = @as(u8, 1) << @intCast(first_nibble_bits);
    text[offset] = digits[1 + (random.int(u8) % (first_limit - 1))];
    for (text[offset + 1 ..]) |*slot| {
        slot.* = digits[random.int(u8) & 0x0f];
    }

    var value = try big_int.Managed.init(allocator);
    defer value.deinit();
    try value.setString(16, text[offset..]);
    if (negative and !value.toConst().eqlZero()) value.negate();
    return try value.toString(allocator, 10, .lower);
}

fn parseBase(base: u8, text: []const u8) !Mpz {
    var value = try Mpz.init(testing.allocator);
    errdefer value.deinit();
    try value.setStr(base, text);
    return value;
}

fn parseDecimal(text: []const u8) !Mpz {
    return parseBase(10, text);
}

fn expectDecimalEq(arena: Allocator, actual: *const Mpz, expected: []const u8) !void {
    const got = try actual.toString(arena, 10);
    try testing.expectEqualStrings(expected, got);
}

fn oracleBinary(arena: Allocator, lhs: []const u8, rhs: []const u8, comptime func: anytype) !OwnedString {
    const lhs_z = try arena.dupeZ(u8, lhs);
    const rhs_z = try arena.dupeZ(u8, rhs);
    return .{ .ptr = func(lhs_z.ptr, rhs_z.ptr) };
}

fn oracleUnary(arena: Allocator, value: []const u8, comptime func: anytype) !OwnedString {
    const value_z = try arena.dupeZ(u8, value);
    return .{ .ptr = func(value_z.ptr) };
}

fn oracleShift(arena: Allocator, value: []const u8, shift: usize, comptime func: anytype) !OwnedString {
    const value_z = try arena.dupeZ(u8, value);
    return .{ .ptr = func(value_z.ptr, shift) };
}

fn oraclePow(arena: Allocator, value: []const u8, exponent: u32) !OwnedString {
    const value_z = try arena.dupeZ(u8, value);
    return .{ .ptr = c.gmp_oracle_pow(value_z.ptr, exponent) };
}

fn oracleBase(arena: Allocator, value: []const u8, base: u8) !OwnedString {
    const value_z = try arena.dupeZ(u8, value);
    return .{ .ptr = c.gmp_oracle_to_string_base(value_z.ptr, base) };
}

fn oracleParseBase(arena: Allocator, value: []const u8, input_base: u8, output_base: u8) !OwnedString {
    const value_z = try arena.dupeZ(u8, value);
    return .{ .ptr = c.gmp_oracle_parse_base_to_base(value_z.ptr, input_base, output_base) };
}

fn oracleDiv(arena: Allocator, lhs: []const u8, rhs: []const u8, comptime func: anytype) !OracleQR {
    const lhs_z = try arena.dupeZ(u8, lhs);
    const rhs_z = try arena.dupeZ(u8, rhs);
    var q: [*:0]u8 = undefined;
    var r: [*:0]u8 = undefined;
    func(lhs_z.ptr, rhs_z.ptr, &q, &r);
    return .{ .q = .{ .ptr = q }, .r = .{ .ptr = r } };
}

fn oracleCmp(arena: Allocator, lhs: []const u8, rhs: []const u8) !i8 {
    const lhs_z = try arena.dupeZ(u8, lhs);
    const rhs_z = try arena.dupeZ(u8, rhs);
    return orderSign(@as(std.math.Order, switch (c.gmp_oracle_cmp(lhs_z.ptr, rhs_z.ptr)) {
        0 => .eq,
        else => |value| if (value < 0) .lt else .gt,
    }));
}

fn oracleCmpInt(arena: Allocator, lhs: []const u8, rhs: i64) !i8 {
    const lhs_z = try arena.dupeZ(u8, lhs);
    return if (c.gmp_oracle_cmp_i64(lhs_z.ptr, rhs) < 0) -1 else if (c.gmp_oracle_cmp_i64(lhs_z.ptr, rhs) > 0) 1 else 0;
}

fn oracleCmpUint(arena: Allocator, lhs: []const u8, rhs: u64) !i8 {
    const lhs_z = try arena.dupeZ(u8, lhs);
    return if (c.gmp_oracle_cmp_u64(lhs_z.ptr, rhs) < 0) -1 else if (c.gmp_oracle_cmp_u64(lhs_z.ptr, rhs) > 0) 1 else 0;
}

fn expectBinaryOp(arena: Allocator, lhs: []const u8, rhs: []const u8, comptime oracle_func: anytype, comptime zig_func: anytype) !void {
    var lhs_value = try parseDecimal(lhs);
    defer lhs_value.deinit();
    var rhs_value = try parseDecimal(rhs);
    defer rhs_value.deinit();
    var result = try Mpz.init(testing.allocator);
    defer result.deinit();
    try zig_func(&result, &lhs_value, &rhs_value);
    const expected = try oracle_func(arena, lhs, rhs);
    defer expected.deinit();
    try expectDecimalEq(arena, &result, expected.slice());
}

fn expectUnaryOp(arena: Allocator, value: []const u8, comptime oracle_func: anytype, comptime zig_func: anytype) !void {
    var input = try parseDecimal(value);
    defer input.deinit();
    var result = try Mpz.init(testing.allocator);
    defer result.deinit();
    try zig_func(&result, &input);
    const expected = try oracle_func(arena, value);
    defer expected.deinit();
    try expectDecimalEq(arena, &result, expected.slice());
}

fn expectShiftOp(arena: Allocator, value: []const u8, shift: usize, comptime oracle_func: anytype, comptime zig_func: anytype) !void {
    var input = try parseDecimal(value);
    defer input.deinit();
    var result = try Mpz.init(testing.allocator);
    defer result.deinit();
    try zig_func(&result, &input, shift);
    const expected = try oracle_func(arena, value, shift);
    defer expected.deinit();
    try expectDecimalEq(arena, &result, expected.slice());
}

fn expectPowOp(arena: Allocator, value: []const u8, exponent: u32) !void {
    var input = try parseDecimal(value);
    defer input.deinit();
    var result = try Mpz.init(testing.allocator);
    defer result.deinit();
    try result.pow(&input, exponent);
    const expected = try oraclePow(arena, value, exponent);
    defer expected.deinit();
    try expectDecimalEq(arena, &result, expected.slice());
}

fn expectDivOp(arena: Allocator, lhs: []const u8, rhs: []const u8, comptime oracle_func: anytype, comptime zig_func: anytype) !void {
    var lhs_value = try parseDecimal(lhs);
    defer lhs_value.deinit();
    var rhs_value = try parseDecimal(rhs);
    defer rhs_value.deinit();
    var quotient = try Mpz.init(testing.allocator);
    defer quotient.deinit();
    var remainder = try Mpz.init(testing.allocator);
    defer remainder.deinit();
    try zig_func(&quotient, &remainder, &lhs_value, &rhs_value);
    const expected = try oracle_func(arena, lhs, rhs);
    defer expected.deinit();
    try expectDecimalEq(arena, &quotient, expected.q.slice());
    try expectDecimalEq(arena, &remainder, expected.r.slice());
}

fn exactDividend(arena: Allocator, divisor: []const u8, quotient: []const u8) !OwnedString {
    return oracleBinary(arena, divisor, quotient, c.gmp_oracle_mul);
}

test "Mpz.add matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryAdd, Mpz.add);
    };
}

test "Mpz.sub matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinarySub, Mpz.sub);
    };
}

test "Mpz.mul matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryMul, Mpz.mul);
    };
}

test "Mpz.divTruncQR matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        if (std.mem.eql(u8, rhs, "0")) continue;
        try expectDivOp(arena, lhs, rhs, oracleDivTrunc, Mpz.divTruncQR);
    };
}

test "Mpz.divFloor matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        if (std.mem.eql(u8, rhs, "0")) continue;
        try expectDivOp(arena, lhs, rhs, oracleDivFloor, Mpz.divFloor);
    };
}

test "Mpz.ediv matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        if (std.mem.eql(u8, rhs, "0")) continue;
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryEdiv, Mpz.ediv);
    };
}

test "Mpz.emod matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        if (std.mem.eql(u8, rhs, "0")) continue;
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryEmod, Mpz.emod);
    };
}

test "Mpz.divExact matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values[1..]) |divisor| for (fixtures.values) |quotient| {
        if (std.mem.eql(u8, divisor, "0")) continue;
        const dividend = try exactDividend(arena, divisor, quotient);
        defer dividend.deinit();
        try expectBinaryOp(arena, dividend.slice(), divisor, oracleBinaryDivExact, Mpz.divExact);
    };
}

test "Mpz.neg matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        try expectUnaryOp(arena, value, oracleUnaryNeg, Mpz.neg);
    }
}

test "Mpz.pow matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| for (exponents) |exponent| {
        try expectPowOp(arena, value, exponent);
    };
}

test "Mpz.gcd matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryGcd, Mpz.gcd);
    };
}

test "Mpz.bitAnd matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryAnd, Mpz.bitAnd);
    };
}

test "Mpz.bitOr matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryOr, Mpz.bitOr);
    };
}

test "Mpz.bitXor matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        try expectBinaryOp(arena, lhs, rhs, oracleBinaryXor, Mpz.bitXor);
    };
}

test "Mpz.mul2k matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| for (shifts) |shift| {
        try expectShiftOp(arena, value, shift, oracleShiftMul2k, Mpz.mul2k);
    };
}

test "Mpz.div2k matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| for (shifts) |shift| {
        try expectShiftOp(arena, value, shift, oracleShiftDiv2k, Mpz.div2k);
    };
}

test "Mpz.modPow2 matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| for (shifts) |shift| {
        try expectShiftOp(arena, value, shift, oracleShiftModPow2, Mpz.modPow2);
    };
}

test "Mpz.smodPow2 matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| for (shifts) |shift| {
        try expectShiftOp(arena, value, shift, oracleShiftSmodPow2, Mpz.smodPow2);
    };
}

test "Mpz.cmp matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |lhs| for (fixtures.values) |rhs| {
        var lhs_value = try parseDecimal(lhs);
        defer lhs_value.deinit();
        var rhs_value = try parseDecimal(rhs);
        defer rhs_value.deinit();
        try testing.expectEqual(try oracleCmp(arena, lhs, rhs), lhs_value.cmp(&rhs_value));
    };
}

test "Mpz.cmpInt matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        for (signed_scalars) |scalar| {
            try testing.expectEqual(try oracleCmpInt(arena, value, scalar), parsed.cmpInt(scalar));
        }
    }
}

test "Mpz.cmpUint matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        for (unsigned_scalars) |scalar| {
            try testing.expectEqual(try oracleCmpUint(arena, value, scalar), parsed.cmpUint(scalar));
        }
    }
}

test "Mpz.fitsInt matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_fits_i64(value_z.ptr), parsed.fitsInt());
    }
}

test "Mpz.fitsUint matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_fits_u64(value_z.ptr), parsed.fitsUint());
    }
}

test "Mpz.fitsSizeT matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_fits_size_t(value_z.ptr), parsed.fitsSizeT());
    }
}

test "Mpz.getInt matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        if (!parsed.fitsInt()) continue;
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_get_i64(value_z.ptr), try parsed.getInt());
    }
}

test "Mpz.getUint matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        if (!parsed.fitsUint()) continue;
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_get_u64(value_z.ptr), try parsed.getUint());
    }
}

test "Mpz.getSizeT matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        if (!parsed.fitsSizeT()) continue;
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_get_size_t(value_z.ptr), try parsed.getSizeT());
    }
}

test "Mpz.getLimb matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        const limit = c.gmp_oracle_bit_count_abs(value_z.ptr) / @bitSizeOf(Limb) + 1;
        for (0..limit) |index| {
            try testing.expectEqual(@as(Limb, @intCast(c.gmp_oracle_get_limb(value_z.ptr, index))), parsed.getLimb(index));
        }
    }
}

test "Mpz.toString matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    const bases = [_]u8{ 2, 10, 16 };
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        for (bases) |base| {
            const got = try parsed.toString(arena, base);
            const expected = try oracleBase(arena, value, base);
            defer expected.deinit();
            try testing.expectEqualStrings(expected.slice(), got);
        }
    }
}

test "Mpz.setStr matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    const bases = [_]u8{ 2, 10, 16 };
    for (fixtures.values) |value| for (bases) |base| {
        const repr = try oracleBase(arena, value, base);
        defer repr.deinit();
        var parsed = try parseBase(base, repr.slice());
        defer parsed.deinit();
        const expected = try oracleParseBase(arena, repr.slice(), base, 10);
        defer expected.deinit();
        try expectDecimalEq(arena, &parsed, expected.slice());
    };
}

test "Mpz.log2 matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_log2_abs(value_z.ptr), parsed.log2());
    }
}

test "Mpz.bitCountAbs matches GMP" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fixtures = try FixtureSet.init(arena);
    for (fixtures.values) |value| {
        var parsed = try parseDecimal(value);
        defer parsed.deinit();
        const value_z = try arena.dupeZ(u8, value);
        try testing.expectEqual(c.gmp_oracle_bit_count_abs(value_z.ptr), parsed.bitCountAbs());
    }
}

test "Mpz.swap exchanges values" {
    var lhs = try parseDecimal("123456789012345678901234567890");
    defer lhs.deinit();
    var rhs = try parseDecimal("-340282366920938463463374607431768211457");
    defer rhs.deinit();
    lhs.swap(&rhs);
    try testing.expectEqual(@as(i8, -1), lhs.sgn());
    try testing.expectEqual(@as(i8, 1), rhs.sgn());
}

fn oracleBinaryAdd(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_add);
}

fn oracleBinarySub(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_sub);
}

fn oracleBinaryMul(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_mul);
}

fn oracleBinaryEdiv(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_ediv);
}

fn oracleBinaryEmod(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_emod);
}

fn oracleBinaryDivExact(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_div_exact);
}

fn oracleBinaryGcd(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_gcd);
}

fn oracleBinaryAnd(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_bit_and);
}

fn oracleBinaryOr(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_bit_or);
}

fn oracleBinaryXor(arena: Allocator, lhs: []const u8, rhs: []const u8) !OwnedString {
    return oracleBinary(arena, lhs, rhs, c.gmp_oracle_bit_xor);
}

fn oracleUnaryNeg(arena: Allocator, value: []const u8) !OwnedString {
    return oracleUnary(arena, value, c.gmp_oracle_neg);
}

fn oracleDivTrunc(arena: Allocator, lhs: []const u8, rhs: []const u8) !OracleQR {
    return oracleDiv(arena, lhs, rhs, c.gmp_oracle_div_trunc_qr);
}

fn oracleDivFloor(arena: Allocator, lhs: []const u8, rhs: []const u8) !OracleQR {
    return oracleDiv(arena, lhs, rhs, c.gmp_oracle_div_floor);
}

fn oracleShiftMul2k(arena: Allocator, value: []const u8, shift: usize) !OwnedString {
    return oracleShift(arena, value, shift, c.gmp_oracle_mul_2exp);
}

fn oracleShiftDiv2k(arena: Allocator, value: []const u8, shift: usize) !OwnedString {
    return oracleShift(arena, value, shift, c.gmp_oracle_fdiv_q_2exp);
}

fn oracleShiftModPow2(arena: Allocator, value: []const u8, shift: usize) !OwnedString {
    return oracleShift(arena, value, shift, c.gmp_oracle_fdiv_r_2exp);
}

fn oracleShiftSmodPow2(arena: Allocator, value: []const u8, shift: usize) !OwnedString {
    return oracleShift(arena, value, shift, c.gmp_oracle_smod_pow2);
}
