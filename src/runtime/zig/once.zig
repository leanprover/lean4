// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");

pub const lean_once_cell_t = extern struct {
    state: std.atomic.Value(c_int),
    lock: std.atomic.Value(c_int),
};

pub fn initOnceCell() lean_once_cell_t {
    return .{
        .state = std.atomic.Value(c_int).init(0),
        .lock = std.atomic.Value(c_int).init(0),
    };
}

fn lockOnce(tok: *lean_once_cell_t) void {
    while (tok.lock.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) {
        while (tok.lock.load(.monotonic) != 0) {
            std.atomic.spinLoopHint();
        }
    }
}

fn unlockOnce(tok: *lean_once_cell_t) void {
    tok.lock.store(0, .release);
}

pub fn onceCold(comptime T: type, loc: *T, tok: *lean_once_cell_t, init: *const fn () callconv(.c) T) T {
    lockOnce(tok);
    defer unlockOnce(tok);

    if (tok.state.load(.acquire) != 1) {
        loc.* = init();
        tok.state.store(1, .release);
    }
    return loc.*;
}

export fn lean_obj_once_cold(loc: *?*anyopaque, tok: *lean_once_cell_t, init: *const fn () callconv(.c) ?*anyopaque) callconv(.c) ?*anyopaque {
    const value = onceCold(?*anyopaque, loc, tok, init);
    if (value) |ptr| {
        if (!object.lean_is_scalar(ptr)) {
            @as(*lean.lean_object, @ptrCast(@alignCast(ptr))).m_rc = 0;
        }
    }
    return value;
}

export fn lean_uint8_once_cold(loc: *u8, tok: *lean_once_cell_t, init: *const fn () callconv(.c) u8) callconv(.c) u8 {
    return onceCold(u8, loc, tok, init);
}

export fn lean_uint16_once_cold(loc: *u16, tok: *lean_once_cell_t, init: *const fn () callconv(.c) u16) callconv(.c) u16 {
    return onceCold(u16, loc, tok, init);
}

export fn lean_uint32_once_cold(loc: *u32, tok: *lean_once_cell_t, init: *const fn () callconv(.c) u32) callconv(.c) u32 {
    return onceCold(u32, loc, tok, init);
}

export fn lean_uint64_once_cold(loc: *u64, tok: *lean_once_cell_t, init: *const fn () callconv(.c) u64) callconv(.c) u64 {
    return onceCold(u64, loc, tok, init);
}

export fn lean_usize_once_cold(loc: *usize, tok: *lean_once_cell_t, init: *const fn () callconv(.c) usize) callconv(.c) usize {
    return onceCold(usize, loc, tok, init);
}

var obj_once_count: usize = 0;
var heap_obj_once_count: usize = 0;
var uint8_once_count: usize = 0;
var uint16_once_count: usize = 0;
var uint32_once_count: usize = 0;
var uint64_once_count: usize = 0;
var usize_once_count: usize = 0;

fn initObjValue() callconv(.c) ?*anyopaque {
    obj_once_count += 1;
    return leanBox(1);
}

fn initUint8Value() callconv(.c) u8 {
    uint8_once_count += 1;
    return 0x8f;
}

fn initUint16Value() callconv(.c) u16 {
    uint16_once_count += 1;
    return 0x8fed;
}

fn initUint32Value() callconv(.c) u32 {
    uint32_once_count += 1;
    return 0x8fed_c0de;
}

fn initUint64Value() callconv(.c) u64 {
    uint64_once_count += 1;
    return 0x8fed_c0de_dead_beef;
}

fn initUsizeValue() callconv(.c) usize {
    usize_once_count += 1;
    return 0x1234_5678;
}

fn leanBox(n: usize) ?*anyopaque {
    return @ptrFromInt((n << 1) | 1);
}

fn makeHeapObject() callconv(.c) ?*anyopaque {
    heap_obj_once_count += 1;
    const ptr = alloc.lean_alloc_object(@sizeOf(lean.lean_object));
    const hdr: *lean.lean_object = @ptrCast(@alignCast(ptr));
    hdr.* = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = 0,
    };
    return ptr;
}

test "lean_once_cell_t matches lean.h layout" {
    try testing.expectEqual(@as(usize, 8), @sizeOf(lean_once_cell_t));
    try testing.expectEqual(@as(usize, 0), @offsetOf(lean_once_cell_t, "state"));
    try testing.expectEqual(@as(usize, 4), @offsetOf(lean_once_cell_t, "lock"));
}

test "lean_obj_once_cold initializes once" {
    obj_once_count = 0;
    var loc: ?*anyopaque = null;
    var tok = initOnceCell();

    const first = lean_obj_once_cold(&loc, &tok, &initObjValue);
    const second = lean_obj_once_cold(&loc, &tok, &initObjValue);

    try testing.expectEqual(leanBox(1), first);
    try testing.expectEqual(first, second);
    try testing.expectEqual(first, loc);
    try testing.expectEqual(@as(usize, 1), obj_once_count);
}

test "lean_obj_once_cold marks heap objects persistent" {
    heap_obj_once_count = 0;
    var loc: ?*anyopaque = null;
    var tok = initOnceCell();

    const first = lean_obj_once_cold(&loc, &tok, &makeHeapObject).?;
    const second = lean_obj_once_cold(&loc, &tok, &makeHeapObject).?;
    const hdr: *lean.lean_object = @ptrCast(@alignCast(first));
    defer {
        hdr.m_rc = 1;
        alloc.lean_free_object(first);
    }

    try testing.expectEqual(first, second);
    try testing.expectEqual(first, loc);
    try testing.expectEqual(@as(i32, 0), hdr.m_rc);
    try testing.expectEqual(@as(usize, 1), heap_obj_once_count);
}

test "lean_uint8_once_cold initializes once" {
    uint8_once_count = 0;
    var loc: u8 = 0;
    var tok = initOnceCell();

    try testing.expectEqual(@as(u8, 0x8f), lean_uint8_once_cold(&loc, &tok, &initUint8Value));
    try testing.expectEqual(@as(u8, 0x8f), lean_uint8_once_cold(&loc, &tok, &initUint8Value));
    try testing.expectEqual(@as(u8, 0x8f), loc);
    try testing.expectEqual(@as(usize, 1), uint8_once_count);
}

test "lean_uint16_once_cold initializes once" {
    uint16_once_count = 0;
    var loc: u16 = 0;
    var tok = initOnceCell();

    try testing.expectEqual(@as(u16, 0x8fed), lean_uint16_once_cold(&loc, &tok, &initUint16Value));
    try testing.expectEqual(@as(u16, 0x8fed), lean_uint16_once_cold(&loc, &tok, &initUint16Value));
    try testing.expectEqual(@as(u16, 0x8fed), loc);
    try testing.expectEqual(@as(usize, 1), uint16_once_count);
}

test "lean_uint32_once_cold initializes once" {
    uint32_once_count = 0;
    var loc: u32 = 0;
    var tok = initOnceCell();

    try testing.expectEqual(@as(u32, 0x8fed_c0de), lean_uint32_once_cold(&loc, &tok, &initUint32Value));
    try testing.expectEqual(@as(u32, 0x8fed_c0de), lean_uint32_once_cold(&loc, &tok, &initUint32Value));
    try testing.expectEqual(@as(u32, 0x8fed_c0de), loc);
    try testing.expectEqual(@as(usize, 1), uint32_once_count);
}

test "lean_uint64_once_cold initializes once" {
    uint64_once_count = 0;
    var loc: u64 = 0;
    var tok = initOnceCell();

    try testing.expectEqual(@as(u64, 0x8fed_c0de_dead_beef), lean_uint64_once_cold(&loc, &tok, &initUint64Value));
    try testing.expectEqual(@as(u64, 0x8fed_c0de_dead_beef), lean_uint64_once_cold(&loc, &tok, &initUint64Value));
    try testing.expectEqual(@as(u64, 0x8fed_c0de_dead_beef), loc);
    try testing.expectEqual(@as(usize, 1), uint64_once_count);
}

test "lean_usize_once_cold initializes once" {
    usize_once_count = 0;
    var loc: usize = 0;
    var tok = initOnceCell();

    try testing.expectEqual(@as(usize, 0x1234_5678), lean_usize_once_cold(&loc, &tok, &initUsizeValue));
    try testing.expectEqual(@as(usize, 0x1234_5678), lean_usize_once_cold(&loc, &tok, &initUsizeValue));
    try testing.expectEqual(@as(usize, 0x1234_5678), loc);
    try testing.expectEqual(@as(usize, 1), usize_once_count);
}
