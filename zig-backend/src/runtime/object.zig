const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const mpz_object = @import("mpz_object.zig");

fn ptrBits(o: ?*anyopaque) usize {
    return if (o) |ptr| @intFromPtr(ptr) else 0;
}

fn header(o: *anyopaque) *align(1) lean.lean_object {
    return @ptrCast(o);
}

fn ptrTag(o: *anyopaque) u8 {
    return header(o).m_tag;
}

var g_external_classes: [256]lean.lean_external_class = undefined;
var g_external_class_count: usize = 0;

fn closureByteSize(o: *lean.lean_closure_object) usize {
    return @sizeOf(lean.lean_closure_object) + (@sizeOf(?*anyopaque) * o.m_num_fixed);
}

fn arrayByteSize(o: *lean.lean_array_object) usize {
    return @sizeOf(lean.lean_array_object) + (@sizeOf(?*anyopaque) * o.m_capacity);
}

fn arrayDataByteSize(o: *lean.lean_array_object) usize {
    return @sizeOf(lean.lean_array_object) + (@sizeOf(?*anyopaque) * o.m_size);
}

fn sarrayByteSize(o: *lean.lean_sarray_object) usize {
    return @sizeOf(lean.lean_sarray_object) + (@as(usize, o.m_header.m_other) * o.m_capacity);
}

fn sarrayDataByteSize(o: *lean.lean_sarray_object) usize {
    return @sizeOf(lean.lean_sarray_object) + (@as(usize, o.m_header.m_other) * o.m_size);
}

fn stringByteSize(o: *lean.lean_string_object) usize {
    return @sizeOf(lean.lean_string_object) + o.m_capacity;
}

fn stringDataByteSize(o: *lean.lean_string_object) usize {
    return @sizeOf(lean.lean_string_object) + o.m_size;
}

fn defaultObjectSize(o: *anyopaque) usize {
    return alloc.allocationPayloadSize(o) orelse alloc.legacyPayloadSize(o);
}

pub export fn lean_register_external_class(
    finalize: lean.lean_external_finalize_proc,
    foreach: lean.lean_external_foreach_proc,
) callconv(.c) *lean.lean_external_class {
    if (g_external_class_count >= g_external_classes.len) {
        @panic("external class registry exhausted");
    }

    g_external_classes[g_external_class_count] = .{
        .m_finalize = finalize,
        .m_foreach = foreach,
    };
    g_external_class_count += 1;
    return &g_external_classes[g_external_class_count - 1];
}

pub export fn lean_object_byte_size(o: *anyopaque) callconv(.c) usize {
    switch (ptrTag(o)) {
        lean.LeanArray => {
            const array: *lean.lean_array_object = @ptrCast(@alignCast(o));
            return arrayByteSize(array);
        },
        lean.LeanScalarArray => {
            const array: *lean.lean_sarray_object = @ptrCast(@alignCast(o));
            return sarrayByteSize(array);
        },
        lean.LeanString => {
            const string: *lean.lean_string_object = @ptrCast(@alignCast(o));
            return stringByteSize(string);
        },
        lean.LeanClosure => {
            const closure: *lean.lean_closure_object = @ptrCast(@alignCast(o));
            return closureByteSize(closure);
        },
        lean.LeanMPZ => return mpz_object.mpzObjectByteSize(),
        else => return defaultObjectSize(o),
    }
}

pub export fn lean_object_data_byte_size(o: *anyopaque) callconv(.c) usize {
    switch (ptrTag(o)) {
        lean.LeanArray => {
            const array: *lean.lean_array_object = @ptrCast(@alignCast(o));
            return arrayDataByteSize(array);
        },
        lean.LeanScalarArray => {
            const array: *lean.lean_sarray_object = @ptrCast(@alignCast(o));
            return sarrayDataByteSize(array);
        },
        lean.LeanString => {
            const string: *lean.lean_string_object = @ptrCast(@alignCast(o));
            return stringDataByteSize(string);
        },
        lean.LeanClosure => {
            const closure: *lean.lean_closure_object = @ptrCast(@alignCast(o));
            return closureByteSize(closure);
        },
        lean.LeanMPZ => return mpz_object.mpzObjectByteSize(),
        else => return defaultObjectSize(o),
    }
}

pub export fn lean_box(n: usize) callconv(.c) ?*anyopaque {
    return @ptrFromInt((n << 1) | 1);
}

pub export fn lean_unbox(o: ?*anyopaque) callconv(.c) usize {
    return ptrBits(o) >> 1;
}

pub export fn lean_is_scalar(o: ?*anyopaque) callconv(.c) bool {
    return (ptrBits(o) & 1) == 1;
}

pub export fn lean_obj_tag(o: ?*anyopaque) callconv(.c) c_uint {
    return if (lean_is_scalar(o))
        @as(c_uint, @truncate(lean_unbox(o)))
    else
        @as(c_uint, ptrTag(o.?));
}

pub export fn lean_ptr_tag(o: *anyopaque) callconv(.c) u8 {
    return ptrTag(o);
}

test "lean object layouts match lean.h" {
    try testing.expectEqual(@as(usize, 8), @sizeOf(lean.lean_object));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_object, "m_rc"));
    try testing.expectEqual(@as(usize, 4), @offsetOf(lean.lean_object, "m_cs_sz"));
    try testing.expectEqual(@as(usize, 6), @offsetOf(lean.lean_object, "m_other"));
    try testing.expectEqual(@as(usize, 7), @offsetOf(lean.lean_object, "m_tag"));

    try testing.expectEqual(@as(usize, 8), @sizeOf(lean.lean_ctor_object));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean.lean_ctor_object, "m_header"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_ctor_object, "m_objs"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_array_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_array_object, "m_size"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_array_object, "m_capacity"));
    try testing.expectEqual(@as(usize, 24), @offsetOf(lean.lean_array_object, "m_data"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_sarray_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_sarray_object, "m_size"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_sarray_object, "m_capacity"));
    try testing.expectEqual(@as(usize, 24), @offsetOf(lean.lean_sarray_object, "m_data"));

    try testing.expectEqual(@as(usize, 32), @sizeOf(lean.lean_string_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_string_object, "m_size"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_string_object, "m_capacity"));
    try testing.expectEqual(@as(usize, 24), @offsetOf(lean.lean_string_object, "m_length"));
    try testing.expectEqual(@as(usize, 32), @offsetOf(lean.lean_string_object, "m_data"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_closure_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_closure_object, "m_fun"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_closure_object, "m_arity"));
    try testing.expectEqual(@as(usize, 18), @offsetOf(lean.lean_closure_object, "m_num_fixed"));
    try testing.expectEqual(@as(usize, 24), @offsetOf(lean.lean_closure_object, "m_objs"));

    try testing.expectEqual(@as(usize, 16), @sizeOf(lean.lean_ref_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_ref_object, "m_value"));

    try testing.expectEqual(@as(usize, 24), @sizeOf(lean.lean_thunk_object));
    try testing.expectEqual(@as(usize, 8), @offsetOf(lean.lean_thunk_object, "m_value"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(lean.lean_thunk_object, "m_closure"));
}

test "tag constants match lean.h" {
    try testing.expectEqual(@as(u8, 243), lean.LeanMaxCtorTag);
    try testing.expectEqual(@as(u8, 244), lean.LeanPromise);
    try testing.expectEqual(@as(u8, 245), lean.LeanClosure);
    try testing.expectEqual(@as(u8, 246), lean.LeanArray);
    try testing.expectEqual(@as(u8, 247), lean.LeanStructArray);
    try testing.expectEqual(@as(u8, 248), lean.LeanScalarArray);
    try testing.expectEqual(@as(u8, 249), lean.LeanString);
    try testing.expectEqual(@as(u8, 250), lean.LeanMPZ);
    try testing.expectEqual(@as(u8, 251), lean.LeanThunk);
    try testing.expectEqual(@as(u8, 252), lean.LeanTask);
    try testing.expectEqual(@as(u8, 253), lean.LeanRef);
    try testing.expectEqual(@as(u8, 254), lean.LeanExternal);
    try testing.expectEqual(@as(u8, 255), lean.LeanReserved);
}

test "scalar helpers follow tagged-pointer ABI" {
    const values = [_]usize{ 0, 1, 42, @divTrunc(@as(usize, @intCast(std.math.maxInt(c_int))), 2) };
    for (values) |value| {
        const boxed = lean_box(value);
        try testing.expect(lean_is_scalar(boxed));
        try testing.expectEqual(@as(usize, 1), @intFromPtr(boxed.?) & 1);
        try testing.expectEqual(value, lean_unbox(boxed));
        try testing.expectEqual(@as(c_uint, @intCast(value)), lean_obj_tag(boxed));
    }
}

test "pointer tag helpers read heap header tag" {
    var object = lean.lean_object{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanArray,
    };
    const ptr: *anyopaque = @ptrCast(&object);
    try testing.expectEqual(lean.LeanArray, lean_ptr_tag(ptr));
    try testing.expectEqual(@as(c_uint, lean.LeanArray), lean_obj_tag(ptr));
}

fn allocLegacySmallObject(payload_size: usize, tag: u8) *anyopaque {
    const payload = std.c.malloc(payload_size) orelse @panic("out of memory");
    @memset(@as([*]u8, @ptrCast(payload))[0..payload_size], 0);

    const hdr: *lean.lean_object = @ptrCast(@alignCast(payload));
    hdr.* = .{
        .m_rc = 1,
        .m_cs_sz = @intCast(payload_size),
        .m_other = 0,
        .m_tag = tag,
    };
    return payload;
}

fn noopFinalize(_: *anyopaque) callconv(.c) void {}

fn noopForeach(_: *anyopaque, _: ?*anyopaque) callconv(.c) void {}

test "lean_object byte sizes accept legacy small allocations" {
    const ptr = allocLegacySmallObject(@sizeOf(lean.lean_thunk_object), lean.LeanThunk);
    defer std.c.free(ptr);

    try testing.expectEqual(@as(usize, @sizeOf(lean.lean_thunk_object)), lean_object_byte_size(ptr));
    try testing.expectEqual(@as(usize, @sizeOf(lean.lean_thunk_object)), lean_object_data_byte_size(ptr));
}

test "lean_register_external_class stores callbacks" {
    const cls = lean_register_external_class(@ptrCast(&noopFinalize), @ptrCast(&noopForeach));
    try testing.expectEqual(&noopFinalize, cls.*.m_finalize);
    try testing.expectEqual(&noopForeach, cls.*.m_foreach);
}
