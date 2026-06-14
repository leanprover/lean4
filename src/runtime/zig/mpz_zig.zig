// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

//! Thin Zig wrapper around GMP `mpz_t` used by the Lean runtime.
//!
//! The layout of `Mpz` matches GMP's `__mpz_struct` so that `lean.MpzObject`
//! can embed an `mpz_t` value with the same size and alignment as the C++
//! runtime's `mpz_object::m_value`.

const std = @import("std");

/// Matches GMP's `__mpz_struct` on 64-bit platforms.
pub const Mpz = extern struct {
    _mp_alloc: c_int,
    _mp_size: c_int,
    _mp_d: [*c]usize,

    pub fn init(_: std.mem.Allocator) error{OutOfMemory}!Mpz {
        var self: Mpz = undefined;
        __gmpz_init(&self);
        return self;
    }

    pub fn deinit(self: *Mpz) void {
        __gmpz_clear(self);
    }

    pub fn initSet(_: std.mem.Allocator, value: anytype) error{OutOfMemory}!Mpz {
        var self: Mpz = undefined;
        const T = @TypeOf(value);
        if (T == *const Mpz or T == *Mpz) {
            __gmpz_init_set(&self, value);
        } else if (T == Mpz) {
            __gmpz_init_set(&self, &value);
        } else {
            // integer types and comptime_int
            if (value < 0) {
                __gmpz_init_set_si(&self, @intCast(value));
            } else {
                __gmpz_init_set_ui(&self, @intCast(value));
            }
        }
        return self;
    }

    pub fn copy(self: *Mpz, other: *const Mpz) error{OutOfMemory}!void {
        __gmpz_set(self, other);
    }

    pub fn set(self: *Mpz, value: anytype) error{OutOfMemory}!void {
        const T = @TypeOf(value);
        if (T == *const Mpz or T == *Mpz) {
            __gmpz_set(self, value);
        } else if (T == Mpz) {
            __gmpz_set(self, &value);
        } else {
            // integer types and comptime_int
            if (value < 0) {
                __gmpz_set_si(self, @intCast(value));
            } else {
                __gmpz_set_ui(self, @intCast(value));
            }
        }
    }

    pub fn setStr(self: *Mpz, base: u8, str: []const u8) error{OutOfMemory, InvalidCharacter}!void {
        const zstr = std.heap.c_allocator.dupeZ(u8, str) catch return error.OutOfMemory;
        defer std.heap.c_allocator.free(zstr);
        if (__gmpz_set_str(self, zstr, @intCast(base)) != 0) {
            return error.InvalidCharacter;
        }
    }

    pub fn toString(self: *const Mpz, allocator: std.mem.Allocator, base: u8) error{OutOfMemory, InvalidCharacter}![]u8 {
        const raw = __gmpz_get_str(null, @intCast(base), self);
        defer std.c.free(raw);
        const len = std.mem.len(raw);
        return allocator.dupe(u8, raw[0..len]) catch return error.OutOfMemory;
    }

    pub fn cmp(self: *const Mpz, other: *const Mpz) i8 {
        return @intCast(__gmpz_cmp(self, other));
    }

    pub fn sgn(self: *const Mpz) i8 {
        if (self._mp_size > 0) return 1;
        if (self._mp_size < 0) return -1;
        return 0;
    }

    pub fn add(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_add(self, a, b);
    }

    pub fn sub(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_sub(self, a, b);
    }

    pub fn mul(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_mul(self, a, b);
    }

    pub fn neg(self: *Mpz, a: *const Mpz) error{OutOfMemory}!void {
        __gmpz_neg(self, a);
    }

    pub fn abs(self: *Mpz, a: *const Mpz) error{OutOfMemory}!void {
        __gmpz_abs(self, a);
    }

    pub fn divTruncQR(self: *Mpz, q: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_tdiv_qr(self, q, a, b);
    }

    pub fn divFloor(self: *Mpz, q: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_fdiv_qr(self, q, a, b);
    }

    pub fn divExact(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_divexact(self, a, b);
    }

    pub fn ediv(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        var r = try Mpz.init(std.heap.c_allocator);
        defer r.deinit();
        __gmpz_tdiv_qr(self, &r, a, b);
        if (r.sgn() < 0) {
            if (b.sgn() > 0) {
                __gmpz_sub_ui(self, self, 1);
            } else {
                __gmpz_add_ui(self, self, 1);
            }
        }
    }

    pub fn emod(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_tdiv_r(self, a, b);
        if (self.sgn() < 0) {
            if (b.sgn() > 0) {
                __gmpz_add(self, self, b);
            } else {
                __gmpz_sub(self, self, b);
            }
        }
    }

    pub fn div2k(self: *Mpz, a: *const Mpz, k: usize) error{OutOfMemory}!void {
        __gmpz_fdiv_q_2exp(self, a, @intCast(k));
    }

    pub fn mul2k(self: *Mpz, a: *const Mpz, k: usize) error{OutOfMemory}!void {
        __gmpz_mul_2exp(self, a, @intCast(k));
    }

    pub fn bitAnd(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_and(self, a, b);
    }

    pub fn bitOr(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_ior(self, a, b);
    }

    pub fn bitXor(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_xor(self, a, b);
    }

    pub fn pow(self: *Mpz, a: *const Mpz, exp: u32) error{OutOfMemory}!void {
        __gmpz_pow_ui(self, a, @intCast(exp));
    }

    pub fn gcd(self: *Mpz, a: *const Mpz, b: *const Mpz) error{OutOfMemory}!void {
        __gmpz_gcd(self, a, b);
    }

    pub fn getLimb(self: *const Mpz, i: usize) usize {
        return @intCast(__gmpz_getlimbn(self, i));
    }

    pub fn log2(self: *const Mpz) usize {
        if (self.sgn() <= 0) return 0;
        const bits = __gmpz_sizeinbase(self, 2);
        return @intCast(bits - 1);
    }

    pub fn fitsSizeT(self: *const Mpz) bool {
        if (self.sgn() < 0) return false;
        return __gmpz_fits_ulong_p(self) != 0;
    }

    pub fn getSizeT(self: *const Mpz) error{OutOfMemory}!usize {
        return @intCast(__gmpz_get_ui(self));
    }

    pub fn fitsInt(self: *const Mpz) bool {
        return __gmpz_fits_slong_p(self) != 0;
    }

    pub fn getInt(self: *const Mpz) error{OutOfMemory}!i64 {
        return @intCast(__gmpz_get_si(self));
    }

    pub fn fitsUint(self: *const Mpz) bool {
        return __gmpz_fits_ulong_p(self) != 0;
    }

    pub fn getUint(self: *const Mpz) error{OutOfMemory}!u64 {
        return @intCast(__gmpz_get_ui(self));
    }

    pub fn smodPow2(self: *Mpz, a: *const Mpz, k: usize) error{OutOfMemory}!void {
        __gmpz_fdiv_r_2exp(self, a, @intCast(k));
        if (k == 0) return;

        var half = try Mpz.init(std.heap.c_allocator);
        defer half.deinit();
        __gmpz_ui_pow_ui(&half, 2, @intCast(k - 1));

        if (__gmpz_cmp(self, &half) >= 0) {
            var pow2 = try Mpz.init(std.heap.c_allocator);
            defer pow2.deinit();
            __gmpz_ui_pow_ui(&pow2, 2, @intCast(k));
            __gmpz_sub(self, self, &pow2);
        }
    }
};

extern fn __gmpz_init(x: *Mpz) void;
extern fn __gmpz_clear(x: *Mpz) void;
extern fn __gmpz_init_set(x: *Mpz, y: *const Mpz) void;
extern fn __gmpz_init_set_ui(x: *Mpz, y: c_ulong) void;
extern fn __gmpz_init_set_si(x: *Mpz, y: c_long) void;
extern fn __gmpz_set(x: *Mpz, y: *const Mpz) void;
extern fn __gmpz_set_ui(x: *Mpz, y: c_ulong) void;
extern fn __gmpz_set_si(x: *Mpz, y: c_long) void;
extern fn __gmpz_set_str(x: *Mpz, str: [*:0]const u8, base: c_int) c_int;
extern fn __gmpz_get_str(str: ?[*:0]u8, base: c_int, x: *const Mpz) [*:0]u8;
extern fn __gmpz_get_ui(x: *const Mpz) c_ulong;
extern fn __gmpz_get_si(x: *const Mpz) c_long;
extern fn __gmpz_getlimbn(x: *const Mpz, n: usize) c_ulong;
extern fn __gmpz_cmp(x: *const Mpz, y: *const Mpz) c_int;
extern fn __gmpz_cmp_ui(x: *const Mpz, y: c_ulong) c_int;
extern fn __gmpz_add(x: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_sub(x: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_add_ui(x: *Mpz, a: *const Mpz, y: c_ulong) void;
extern fn __gmpz_sub_ui(x: *Mpz, a: *const Mpz, y: c_ulong) void;
extern fn __gmpz_mul(x: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_neg(x: *Mpz, a: *const Mpz) void;
extern fn __gmpz_abs(x: *Mpz, a: *const Mpz) void;
extern fn __gmpz_tdiv_qr(q: *Mpz, r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_tdiv_r(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_fdiv_qr(q: *Mpz, r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_fdiv_q(q: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_fdiv_r(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_divexact(q: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_fdiv_q_2exp(q: *Mpz, a: *const Mpz, k: c_ulong) void;
extern fn __gmpz_fdiv_r_2exp(r: *Mpz, a: *const Mpz, k: c_ulong) void;
extern fn __gmpz_mul_2exp(r: *Mpz, a: *const Mpz, k: c_ulong) void;
extern fn __gmpz_and(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_ior(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_xor(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_pow_ui(r: *Mpz, a: *const Mpz, exp: c_ulong) void;
extern fn __gmpz_gcd(r: *Mpz, a: *const Mpz, b: *const Mpz) void;
extern fn __gmpz_sizeinbase(x: *const Mpz, base: c_int) usize;
extern fn __gmpz_fits_ulong_p(x: *const Mpz) c_int;
extern fn __gmpz_fits_slong_p(x: *const Mpz) c_int;
extern fn __gmpz_ui_pow_ui(r: *Mpz, base: c_ulong, exp: c_ulong) void;

test "mpz_zig basic roundtrip" {
    var a = try Mpz.init(std.testing.allocator);
    defer a.deinit();
    try a.set(@as(usize, 12345678901234567890));

    var b = try Mpz.initSet(std.testing.allocator, &a);
    defer b.deinit();

    try std.testing.expectEqual(@as(i8, 0), a.cmp(&b));
    try std.testing.expect(a.fitsSizeT());
    try std.testing.expectEqual(@as(usize, 12345678901234567890), try a.getSizeT());
}

test "mpz_zig smodPow2 handles 64-bit signed truncation" {
    var a = try Mpz.initSet(std.testing.allocator, @as(i64, -1));
    defer a.deinit();
    var r = try Mpz.init(std.testing.allocator);
    defer r.deinit();
    try r.smodPow2(&a, 64);
    try std.testing.expectEqual(@as(i64, -1), try r.getInt());
}
