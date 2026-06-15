// Nat runtime entry point.
//
// Big-natural-number constructors live in `nat_constructors.zig` and
// arithmetic/bitwise/comparison operations live in `nat_arithmetic.zig`.
// This file re-exports their public API so that the rest of the runtime
// can depend on a single module name.

const std = @import("std");
const lean = @import("lean_object.zig");
const mpz_zig = @import("mpz_zig");
const object = @import("object.zig");
const runtime_options = @import("runtime_options");

const nat_constructors = @import("nat_constructors.zig");
const nat_arithmetic = @import("nat_arithmetic.zig");

extern fn lean_mk_string_unchecked(s: [*:0]const u8, sz: usize, len: usize) callconv(.c) *anyopaque;

fn natReprFast(n: *anyopaque) callconv(.c) *anyopaque {
    if (object.lean_is_scalar(n)) {
        const value = object.lean_unbox(n);
        var buf: [64]u8 = undefined;
        const str = std.fmt.bufPrint(&buf, "{}", .{value}) catch @panic("Nat.reprFast overflow");
        return lean_mk_string_unchecked(@ptrCast(str.ptr), str.len, str.len);
    } else {
        const mpz_obj: *lean.MpzObject = @ptrCast(@alignCast(n));
        const mpz: *mpz_zig.Mpz = @ptrCast(@alignCast(&mpz_obj.m_value));
        const raw = mpz.toString(std.heap.c_allocator, 10) catch @panic("Nat.reprFast overflow");
        defer std.heap.c_allocator.free(raw);
        return lean_mk_string_unchecked(@ptrCast(raw.ptr), raw.len, raw.len);
    }
}

comptime {
    if (runtime_options.export_lean_helpers) {
        @export(&natReprFast, .{ .name = "l_Nat_reprFast" });
    }
}

test "nat module re-exports compile" {
    _ = nat_constructors;
    _ = nat_arithmetic;
}
