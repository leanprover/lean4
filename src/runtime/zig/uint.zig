// Nat (big-nat → unsigned fixed-width) conversion helpers.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const mpz_object = @import("mpz_object.zig");
const nat_constructors = @import("nat_constructors.zig");
const object = @import("object.zig");

fn natLowWord(o: *anyopaque) u64 {
    if (object.lean_is_scalar(o)) return @intCast(object.lean_unbox(o));
    return @intCast(mpz_object.mpzValue(o).getLimb(0));
}

export fn lean_uint8_of_big_nat(a: *anyopaque) callconv(.c) u8 {
    return @truncate(natLowWord(a));
}

export fn lean_uint16_of_big_nat(a: *anyopaque) callconv(.c) u16 {
    return @truncate(natLowWord(a));
}

export fn lean_uint32_of_big_nat(a: *anyopaque) callconv(.c) u32 {
    return @truncate(natLowWord(a));
}

export fn lean_uint64_of_big_nat(a: *anyopaque) callconv(.c) u64 {
    return natLowWord(a);
}

export fn lean_uint64_mix_hash(h: u64, k: u64) callconv(.c) u64 {
    const m: u64 = 0xc6a4a7935bd1e995;
    const r: u6 = 47;

    var key = k;
    key *%= m;
    key ^= key >> r;
    key ^= m;

    var hash = h ^ key;
    hash *%= m;
    return hash;
}

export fn lean_usize_of_big_nat(a: *anyopaque) callconv(.c) usize {
    return @intCast(natLowWord(a));
}

fn freeNatResult(o: ?*anyopaque) void {
    if (!object.lean_is_scalar(o)) alloc.lean_free_object(o.?);
}

test "unsigned width conversions truncate to low bits" {
    const wide = mpz_object.lean_alloc_mpz();
    defer alloc.lean_free_object(wide);
    try mpz_object.mpzValue(wide).setStr(16, "10000000000000000123456789ABCDEF0");

    try testing.expectEqual(@as(u8, 0xf0), lean_uint8_of_big_nat(wide));
    try testing.expectEqual(@as(u16, 0xdef0), lean_uint16_of_big_nat(wide));
    try testing.expectEqual(@as(u32, 0x9abcdef0), lean_uint32_of_big_nat(wide));
    try testing.expectEqual(@as(u64, 0x123456789abcdef0), lean_uint64_of_big_nat(wide));
    try testing.expectEqual(@as(usize, 8), @sizeOf(usize));
    try testing.expectEqual(@as(usize, 0x123456789abcdef0), lean_usize_of_big_nat(wide));
}

test "unsigned width conversions match all-ones boundary and mix hash goldens" {
    const all_ones = nat_constructors.lean_cstr_to_nat("340282366920938463463374607431768211455");
    defer freeNatResult(all_ones);

    try testing.expectEqual(@as(u8, 0xff), lean_uint8_of_big_nat(all_ones.?));
    try testing.expectEqual(@as(u16, 0xffff), lean_uint16_of_big_nat(all_ones.?));
    try testing.expectEqual(@as(u32, 0xffffffff), lean_uint32_of_big_nat(all_ones.?));
    try testing.expectEqual(@as(u64, 0xffffffffffffffff), lean_uint64_of_big_nat(all_ones.?));
    try testing.expectEqual(@as(usize, 0xffffffffffffffff), lean_usize_of_big_nat(all_ones.?));

    try testing.expectEqual(@as(u64, 0x35a98f4d286a90b9), lean_uint64_mix_hash(0, 0));
    try testing.expectEqual(@as(u64, 0xe62129c84f35c59c), lean_uint64_mix_hash(1, 2));
    try testing.expectEqual(@as(u64, 0xf625c5a4385e7d54), lean_uint64_mix_hash(0x0123456789abcdef, 0xfedcba9876543210));
}
