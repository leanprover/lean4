const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const mpz_zig = @import("mpz_zig");

fn asMpzObject(o: *anyopaque) *lean.MpzObject {
    return @ptrCast(@alignCast(o));
}

pub fn initMpzHeader(o: *lean.MpzObject) void {
    o.m_header = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanMPZ,
    };
}

pub fn mpzObjectByteSize() usize {
    return @sizeOf(lean.MpzObject);
}

pub fn mpzValue(o: *anyopaque) *mpz_zig.Mpz {
    return @ptrCast(@alignCast(&asMpzObject(o).m_value));
}

pub export fn lean_alloc_mpz() callconv(.c) *anyopaque {
    const obj: *lean.MpzObject = @ptrCast(@alignCast(alloc.allocTrackedPayload(@sizeOf(lean.MpzObject), alloc.allocation_kind_mpz)));
    initMpzHeader(obj);
    mpzValue(obj).* = mpz_zig.Mpz.init(std.heap.c_allocator) catch {
        alloc.freeTrackedPayload(obj);
        @panic("lean_alloc_mpz: alloc");
    };
    return obj;
}

pub export fn lean_extract_mpz_value(o: *anyopaque) callconv(.c) *mpz_zig.Mpz {
    return mpzValue(o);
}

pub export fn leanrt_test_alloc_mpz_from_cstr(value: [*:0]const u8) callconv(.c) *anyopaque {
    const obj = lean_alloc_mpz();
    errdefer alloc.lean_free_object(obj);
    mpzValue(obj).setStr(10, std.mem.span(value)) catch @panic("leanrt_test_alloc_mpz_from_cstr: invalid decimal");
    return obj;
}

pub export fn leanrt_test_mpz_eq_cstr(o: *anyopaque, value: [*:0]const u8) callconv(.c) u8 {
    var expected = mpz_zig.Mpz.init(std.heap.c_allocator) catch @panic("leanrt_test_mpz_eq_cstr: OOM");
    defer expected.deinit();
    expected.setStr(10, std.mem.span(value)) catch @panic("leanrt_test_mpz_eq_cstr: invalid decimal");
    return @intFromBool(mpzValue(o).cmp(&expected) == 0);
}

pub export fn leanrt_test_mpz_object_size() callconv(.c) usize {
    return @sizeOf(lean.MpzObject);
}

pub export fn leanrt_test_mpz_value_offset() callconv(.c) usize {
    return @offsetOf(lean.MpzObject, "m_value");
}

test "lean_alloc_mpz initializes LeanMPZ header and zero payload" {
    const obj = lean_alloc_mpz();
    defer alloc.lean_free_object(obj);

    const mpz_obj = asMpzObject(obj);
    try testing.expectEqual(@as(i32, 1), mpz_obj.m_header.m_rc);
    try testing.expectEqual(@as(u16, 0), mpz_obj.m_header.m_cs_sz);
    try testing.expectEqual(@as(u8, 0), mpz_obj.m_header.m_other);
    try testing.expectEqual(lean.LeanMPZ, mpz_obj.m_header.m_tag);
    try testing.expectEqual(@as(i8, 0), mpzValue(obj).sgn());
    try testing.expectEqual(@intFromPtr(mpzValue(obj)), @intFromPtr(lean_extract_mpz_value(obj)));
}

test "leanrt_test_alloc_mpz_from_cstr and equality helper round-trip decimal values" {
    const obj = leanrt_test_alloc_mpz_from_cstr("123456789012345678901234567890");
    defer alloc.lean_free_object(obj);

    try testing.expectEqual(@as(u8, 1), leanrt_test_mpz_eq_cstr(obj, "123456789012345678901234567890"));
    try testing.expectEqual(@as(u8, 0), leanrt_test_mpz_eq_cstr(obj, "123456789012345678901234567891"));
    try testing.expectEqual(@sizeOf(lean.MpzObject), leanrt_test_mpz_object_size());
    try testing.expectEqual(@offsetOf(lean.MpzObject, "m_value"), leanrt_test_mpz_value_offset());
}
