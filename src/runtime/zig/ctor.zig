// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const box = @import("box.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

fn header(o: *anyopaque) *lean.lean_object {
    return @ptrCast(@alignCast(o));
}

fn allocCtor(tag: u8, num_objs: u8, scalar_sz: u16) *anyopaque {
    return alloc.lean_alloc_ctor(tag, num_objs, scalar_sz);
}

fn forceFree(o: *anyopaque) void {
    if (!object.lean_is_scalar(o)) {
        alloc.lean_free_object(o);
    }
}

fn asCtor(o: *anyopaque) *lean.lean_ctor_object {
    return @ptrCast(@alignCast(o));
}

fn ctorSlots(o: *anyopaque) [*]?*anyopaque {
    return @ptrCast(&asCtor(o).m_objs);
}

fn ctorNumObjs(o: *anyopaque) usize {
    return header(o).m_other;
}

fn ctorObjectBytes(o: *anyopaque) usize {
    return ctorNumObjs(o) * @sizeOf(?*anyopaque);
}

fn ctorScalarBytes(o: *anyopaque) usize {
    return header(o).m_cs_sz;
}

fn scalarBaseAddr(o: *anyopaque) usize {
    return @intFromPtr(o) + @sizeOf(lean.lean_ctor_object) + ctorObjectBytes(o);
}

fn scalarFieldPtr(comptime T: type, o: *anyopaque, offset: usize) *T {
    const object_bytes = ctorObjectBytes(o);
    std.debug.assert(offset >= object_bytes);
    std.debug.assert(offset + @sizeOf(T) <= object_bytes + ctorScalarBytes(o));
    return @ptrFromInt(scalarBaseAddr(o) + (offset - object_bytes));
}

fn usizeFieldPtr(o: *anyopaque, index: usize) *usize {
    const num_objs = ctorNumObjs(o);
    std.debug.assert(index >= num_objs);
    return scalarFieldPtr(usize, o, index * @sizeOf(?*anyopaque));
}

pub export fn lean_ctor_get(o: *anyopaque, i: c_uint) callconv(.c) ?*anyopaque {
    std.debug.assert(i < ctorNumObjs(o));
    return ctorSlots(o)[i];
}

pub export fn lean_ctor_set(o: *anyopaque, i: c_uint, v: ?*anyopaque) callconv(.c) void {
    std.debug.assert(i < ctorNumObjs(o));
    ctorSlots(o)[i] = v;
}

pub export fn lean_ctor_set_tag(o: *anyopaque, new_tag: u8) callconv(.c) void {
    std.debug.assert(new_tag <= lean.LeanMaxCtorTag);
    header(o).m_tag = new_tag;
}

pub export fn lean_ctor_release(o: *anyopaque, i: c_uint) callconv(.c) void {
    std.debug.assert(i < ctorNumObjs(o));
    const slots = ctorSlots(o);
    rc.lean_dec(slots[i]);
    slots[i] = object.lean_box(0);
}

pub export fn lean_ctor_get_usize(o: *anyopaque, i: c_uint) callconv(.c) usize {
    return usizeFieldPtr(o, i).*;
}

pub export fn lean_ctor_get_uint8(o: *anyopaque, offset: c_uint) callconv(.c) u8 {
    return scalarFieldPtr(u8, o, offset).*;
}

pub export fn lean_ctor_get_uint16(o: *anyopaque, offset: c_uint) callconv(.c) u16 {
    return scalarFieldPtr(u16, o, offset).*;
}

pub export fn lean_ctor_get_uint32(o: *anyopaque, offset: c_uint) callconv(.c) u32 {
    return scalarFieldPtr(u32, o, offset).*;
}

pub export fn lean_ctor_get_uint64(o: *anyopaque, offset: c_uint) callconv(.c) u64 {
    return scalarFieldPtr(u64, o, offset).*;
}

pub export fn lean_ctor_get_float(o: *anyopaque, offset: c_uint) callconv(.c) f64 {
    return scalarFieldPtr(f64, o, offset).*;
}

pub export fn lean_ctor_get_float32(o: *anyopaque, offset: c_uint) callconv(.c) f32 {
    return scalarFieldPtr(f32, o, offset).*;
}

pub export fn lean_ctor_set_usize(o: *anyopaque, i: c_uint, v: usize) callconv(.c) void {
    usizeFieldPtr(o, i).* = v;
}

pub export fn lean_ctor_set_uint8(o: *anyopaque, offset: c_uint, v: u8) callconv(.c) void {
    scalarFieldPtr(u8, o, offset).* = v;
}

pub export fn lean_ctor_set_uint16(o: *anyopaque, offset: c_uint, v: u16) callconv(.c) void {
    scalarFieldPtr(u16, o, offset).* = v;
}

pub export fn lean_ctor_set_uint32(o: *anyopaque, offset: c_uint, v: u32) callconv(.c) void {
    scalarFieldPtr(u32, o, offset).* = v;
}

pub export fn lean_ctor_set_uint64(o: *anyopaque, offset: c_uint, v: u64) callconv(.c) void {
    scalarFieldPtr(u64, o, offset).* = v;
}

pub export fn lean_ctor_set_float(o: *anyopaque, offset: c_uint, v: f64) callconv(.c) void {
    scalarFieldPtr(f64, o, offset).* = v;
}

pub export fn lean_ctor_set_float32(o: *anyopaque, offset: c_uint, v: f32) callconv(.c) void {
    scalarFieldPtr(f32, o, offset).* = v;
}

test "lean_ctor_set and lean_ctor_get round-trip object fields" {
    const ctor = allocCtor(3, 3, 0);
    defer forceFree(ctor);

    const v0 = object.lean_box(1);
    const v1 = object.lean_box(2);
    const v2 = object.lean_box(3);

    lean_ctor_set(ctor, 0, v0);
    lean_ctor_set(ctor, 1, v1);
    lean_ctor_set(ctor, 2, v2);

    try testing.expectEqual(v0, lean_ctor_get(ctor, 0));
    try testing.expectEqual(v1, lean_ctor_get(ctor, 1));
    try testing.expectEqual(v2, lean_ctor_get(ctor, 2));
}

test "lean_ctor_set_tag updates the object tag" {
    const ctor = allocCtor(4, 0, 0);
    defer forceFree(ctor);

    try testing.expectEqual(@as(c_uint, 4), object.lean_obj_tag(ctor));
    lean_ctor_set_tag(ctor, 9);
    try testing.expectEqual(@as(c_uint, 9), object.lean_obj_tag(ctor));
}

test "lean_ctor_release decrements and replaces slot with lean_box(0)" {
    const ctor = allocCtor(5, 1, 0);
    defer forceFree(ctor);

    const child = alloc.lean_alloc_ctor(0, 0, 0);
    lean_ctor_set(ctor, 0, child);
    rc.lean_inc(child);

    try testing.expectEqual(@as(i32, 2), header(child).m_rc);
    lean_ctor_release(ctor, 0);
    try testing.expectEqual(object.lean_box(0), lean_ctor_get(ctor, 0));
    try testing.expectEqual(@as(i32, 1), header(child).m_rc);

    forceFree(child);
}

test "lean_ctor_get and set usize use scalar storage after object slots" {
    const ctor = allocCtor(6, 2, @sizeOf(usize));
    defer forceFree(ctor);

    lean_ctor_set(ctor, 0, object.lean_box(11));
    lean_ctor_set(ctor, 1, object.lean_box(22));
    lean_ctor_set_usize(ctor, 2, 0xfeed_beef);

    try testing.expectEqual(@as(usize, 0xfeed_beef), lean_ctor_get_usize(ctor, 2));
    try testing.expectEqual(object.lean_box(11), lean_ctor_get(ctor, 0));
    try testing.expectEqual(object.lean_box(22), lean_ctor_get(ctor, 1));
}

test "lean_ctor scalar accessors round-trip packed fields" {
    const scalar_sz = 28;
    const ctor = allocCtor(7, 1, scalar_sz);
    defer forceFree(ctor);

    const base = @sizeOf(?*anyopaque);
    lean_ctor_set(ctor, 0, object.lean_box(7));
    lean_ctor_set_uint8(ctor, base + 0, 0xab);
    lean_ctor_set_uint16(ctor, base + 2, 0xcdef);
    lean_ctor_set_uint32(ctor, base + 4, 0x89ab_cdef);
    lean_ctor_set_uint64(ctor, base + 8, 0x0123_4567_89ab_cdef);
    lean_ctor_set_float(ctor, base + 16, @bitCast(@as(u64, 0x4009_21fb_5444_2d18)));
    lean_ctor_set_float32(ctor, base + 24, @bitCast(@as(u32, 0x4049_0fdb)));

    try testing.expectEqual(@as(u8, 0xab), lean_ctor_get_uint8(ctor, base + 0));
    try testing.expectEqual(@as(u16, 0xcdef), lean_ctor_get_uint16(ctor, base + 2));
    try testing.expectEqual(@as(u32, 0x89ab_cdef), lean_ctor_get_uint32(ctor, base + 4));
    try testing.expectEqual(@as(u64, 0x0123_4567_89ab_cdef), lean_ctor_get_uint64(ctor, base + 8));
    try testing.expectEqual(@as(u64, 0x4009_21fb_5444_2d18), @as(u64, @bitCast(lean_ctor_get_float(ctor, base + 16))));
    try testing.expectEqual(@as(u32, 0x4049_0fdb), @as(u32, @bitCast(lean_ctor_get_float32(ctor, base + 24))));
}
