const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const box = @import("box.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

const Obj = ?*anyopaque;

fn asArray(o: *anyopaque) *lean.lean_array_object {
    return @ptrCast(@alignCast(o));
}

fn asSArray(o: *anyopaque) *lean.lean_sarray_object {
    return @ptrCast(@alignCast(o));
}

fn arraySlots(o: *anyopaque) [*]Obj {
    return @ptrCast(&asArray(o).m_data);
}

fn sarrayBytes(o: *anyopaque) [*]u8 {
    return @ptrCast(&asSArray(o).m_data);
}

fn floatSlots(o: *anyopaque) [*]f64 {
    return @ptrCast(@alignCast(sarrayBytes(o)));
}

fn allocObjectArray(size: usize, capacity: usize) *anyopaque {
    return alloc.lean_alloc_array(size, capacity);
}

fn allocByteArray(size: usize, capacity: usize) *anyopaque {
    return alloc.lean_alloc_sarray(1, size, capacity);
}

fn allocFloatArray(size: usize, capacity: usize) *anyopaque {
    return alloc.lean_alloc_sarray(@sizeOf(f64), size, capacity);
}

fn freeIfHeap(o: Obj) void {
    if (o) |ptr| {
        if (!object.lean_is_scalar(ptr)) {
            alloc.lean_free_object(ptr);
        }
    }
}

fn fillArraySlot(o: *anyopaque, i: usize, value: Obj) void {
    arraySlots(o)[i] = value;
}

fn checkedAdd(a: usize, b: usize) usize {
    const result = @addWithOverflow(a, b);
    if (result[1] != 0) @panic("array size overflow");
    return result[0];
}

fn checkedMul(a: usize, b: usize) usize {
    const result = @mulWithOverflow(a, b);
    if (result[1] != 0) @panic("array size overflow");
    return result[0];
}

fn growCapacity(min_cap: usize) usize {
    return checkedMul(min_cap, 2);
}

pub fn lean_array_size(o: *anyopaque) usize {
    return asArray(o).m_size;
}

fn lean_array_capacity(o: *anyopaque) usize {
    return asArray(o).m_capacity;
}

fn lean_array_set_size(o: *anyopaque, sz: usize) void {
    std.debug.assert(sz <= lean_array_capacity(o));
    asArray(o).m_size = sz;
}

fn lean_array_get_core(o: *anyopaque, i: usize) Obj {
    std.debug.assert(i < lean_array_size(o));
    return arraySlots(o)[i];
}

fn lean_array_set_core(o: *anyopaque, i: usize, v: Obj) void {
    std.debug.assert(i < lean_array_size(o));
    arraySlots(o)[i] = v;
}

pub fn lean_mk_empty_array() *anyopaque {
    return allocObjectArray(0, 0);
}

fn lean_ensure_exclusive_array(a: *anyopaque) *anyopaque {
    if (rc.lean_is_exclusive(a)) return a;
    return lean_copy_expand_array_nonlinear(a, false);
}

pub fn lean_array_uget(a: *anyopaque, i: usize) Obj {
    const result = lean_array_get_core(a, i);
    rc.lean_inc(result);
    return result;
}

pub fn lean_array_fget(a: *anyopaque, i: Obj) Obj {
    return lean_array_uget(a, object.lean_unbox(i));
}

pub fn lean_array_get(def_val: Obj, a: *anyopaque, i: Obj) Obj {
    if (object.lean_is_scalar(i)) {
        const idx = object.lean_unbox(i);
        if (idx < lean_array_size(a)) {
            return lean_array_uget(a, idx);
        }
    }
    rc.lean_inc(def_val);
    return lean_array_get_panic(def_val.?);
}

pub fn lean_array_uset(a: *anyopaque, i: usize, v: Obj) *anyopaque {
    const result = lean_ensure_exclusive_array(a);
    std.debug.assert(i < lean_array_size(result));
    const slots = arraySlots(result);
    rc.lean_dec(slots[i]);
    slots[i] = v;
    return result;
}

pub fn lean_array_fset(a: *anyopaque, i: Obj, v: Obj) *anyopaque {
    return lean_array_uset(a, object.lean_unbox(i), v);
}

pub fn lean_array_set(a: *anyopaque, i: Obj, v: Obj) *anyopaque {
    if (object.lean_is_scalar(i)) {
        const idx = object.lean_unbox(i);
        if (idx < lean_array_size(a)) {
            return lean_array_uset(a, idx, v);
        }
    }
    return lean_array_set_panic(a, v.?);
}

pub fn lean_array_pop(a: *anyopaque) *anyopaque {
    const result = lean_ensure_exclusive_array(a);
    const size = lean_array_size(result);
    if (size == 0) return result;

    const last_idx = size - 1;
    rc.lean_dec(lean_array_get_core(result, last_idx));
    lean_array_set_size(result, last_idx);
    return result;
}

pub fn lean_array_uswap(a: *anyopaque, i: usize, j: usize) *anyopaque {
    const result = lean_ensure_exclusive_array(a);
    const slots = arraySlots(result);
    const tmp = slots[i];
    slots[i] = slots[j];
    slots[j] = tmp;
    return result;
}

pub fn lean_array_fswap(a: *anyopaque, i: Obj, j: Obj) *anyopaque {
    return lean_array_uswap(a, object.lean_unbox(i), object.lean_unbox(j));
}

pub fn lean_array_swap(a: *anyopaque, i: Obj, j: Obj) *anyopaque {
    if (!object.lean_is_scalar(i) or !object.lean_is_scalar(j)) return a;
    const ui = object.lean_unbox(i);
    const uj = object.lean_unbox(j);
    if (ui >= lean_array_size(a) or uj >= lean_array_size(a)) return a;
    return lean_array_uswap(a, ui, uj);
}

fn sarrayElemSize(o: *anyopaque) usize {
    return asSArray(o).m_header.m_other;
}

pub fn lean_sarray_size(o: *anyopaque) usize {
    return asSArray(o).m_size;
}

fn lean_sarray_capacity(o: *anyopaque) usize {
    return asSArray(o).m_capacity;
}

fn lean_sarray_set_size(o: *anyopaque, sz: usize) void {
    std.debug.assert(sz <= lean_sarray_capacity(o));
    asSArray(o).m_size = sz;
}

fn copySArray(a: *anyopaque, cap: usize) *anyopaque {
    const elem_size = sarrayElemSize(a);
    const size = lean_sarray_size(a);
    std.debug.assert(cap >= size);

    const result = alloc.lean_alloc_sarray(@intCast(elem_size), size, cap);
    @memcpy(sarrayBytes(result)[0 .. checkedMul(elem_size, size)], sarrayBytes(a)[0 .. checkedMul(elem_size, size)]);
    rc.lean_dec(a);
    return result;
}

fn ensureExclusiveSArray(a: *anyopaque) *anyopaque {
    if (rc.lean_is_exclusive(a)) return a;
    return copySArray(a, lean_sarray_capacity(a));
}

fn ensureCapacitySArray(a: *anyopaque, min_cap: usize, exact: bool) *anyopaque {
    const cap = lean_sarray_capacity(a);
    if (min_cap <= cap) return a;
    return copySArray(a, if (exact) min_cap else growCapacity(min_cap));
}

pub fn lean_byte_array_get(a: *anyopaque, i: Obj) u8 {
    if (object.lean_is_scalar(i)) {
        const idx = object.lean_unbox(i);
        return if (idx < lean_sarray_size(a)) sarrayBytes(a)[idx] else 0;
    }
    return 0;
}

fn lean_byte_array_uget(a: *anyopaque, i: usize) u8 {
    std.debug.assert(i < lean_sarray_size(a));
    return sarrayBytes(a)[i];
}

pub fn lean_byte_array_uset(a: *anyopaque, i: usize, v: u8) *anyopaque {
    const result = ensureExclusiveSArray(a);
    std.debug.assert(i < lean_sarray_size(result));
    sarrayBytes(result)[i] = v;
    return result;
}

pub fn lean_byte_array_set(a: *anyopaque, i: Obj, b: u8) *anyopaque {
    if (!object.lean_is_scalar(i)) return a;
    const idx = object.lean_unbox(i);
    if (idx >= lean_sarray_size(a)) return a;
    return lean_byte_array_uset(a, idx, b);
}

pub fn lean_float_array_get(a: *anyopaque, i: Obj) f64 {
    if (object.lean_is_scalar(i)) {
        const idx = object.lean_unbox(i);
        return if (idx < lean_sarray_size(a)) floatSlots(a)[idx] else 0.0;
    }
    return 0.0;
}

fn lean_float_array_uget(a: *anyopaque, i: usize) f64 {
    std.debug.assert(i < lean_sarray_size(a));
    return floatSlots(a)[i];
}

pub fn lean_float_array_uset(a: *anyopaque, i: usize, d: f64) *anyopaque {
    const result = ensureExclusiveSArray(a);
    std.debug.assert(i < lean_sarray_size(result));
    floatSlots(result)[i] = d;
    return result;
}

pub fn lean_float_array_set(a: *anyopaque, i: Obj, d: f64) *anyopaque {
    if (!object.lean_is_scalar(i)) return a;
    const idx = object.lean_unbox(i);
    if (idx >= lean_sarray_size(a)) return a;
    return lean_float_array_uset(a, idx, d);
}

fn lean_array_mk(_l: *anyopaque) callconv(.c) *anyopaque {
    _ = _l;
    @panic("unimplemented: lean_array_mk");
}

fn lean_array_to_list(_a: *anyopaque) callconv(.c) *anyopaque {
    _ = _a;
    @panic("unimplemented: lean_array_to_list");
}

export fn lean_array_get_panic(def_val: *anyopaque) callconv(.c) *anyopaque {
    rc.lean_dec(def_val);
    @panic("array index out of bounds");
}

export fn lean_copy_expand_array(a: *anyopaque, expand: bool) callconv(.c) *anyopaque {
    const size = lean_array_size(a);
    var cap = lean_array_capacity(a);
    if (expand) {
        cap = checkedMul(checkedAdd(cap, 1), 2);
    }

    const result = allocObjectArray(size, cap);
    const src = arraySlots(a);
    const dest = arraySlots(result);

    if (rc.lean_is_exclusive(a)) {
        @memcpy(dest[0..size], src[0..size]);
        alloc.lean_free_object(a);
    } else {
        for (0..size) |i| {
            dest[i] = src[i];
            rc.lean_inc(src[i]);
        }
        rc.lean_dec(a);
    }

    return result;
}

export fn lean_copy_expand_array_nonlinear(a: *anyopaque, expand: bool) callconv(.c) *anyopaque {
    return lean_copy_expand_array(a, expand);
}

export fn lean_array_set_panic(a: *anyopaque, v: *anyopaque) callconv(.c) *anyopaque {
    rc.lean_dec(a);
    rc.lean_dec(v);
    @panic("array index out of bounds");
}

export fn lean_array_push(a: *anyopaque, v: *anyopaque) callconv(.c) *anyopaque {
    const result = if (rc.lean_is_exclusive(a))
        if (lean_array_capacity(a) > lean_array_size(a))
            a
        else
            lean_copy_expand_array(a, true)
    else
        lean_copy_expand_array_nonlinear(a, lean_array_capacity(a) < checkedAdd(checkedMul(2, lean_array_size(a)), 1));

    const size = lean_array_size(result);
    std.debug.assert(lean_array_capacity(result) > size);
    arraySlots(result)[size] = v;
    lean_array_set_size(result, size + 1);
    return result;
}

export fn lean_mk_array(n: *anyopaque, v: *anyopaque) callconv(.c) *anyopaque {
    if (!object.lean_is_scalar(n)) {
        rc.lean_dec(n);
        rc.lean_dec(v);
        @panic("large natural array sizes are not implemented");
    }

    const size = object.lean_unbox(n);
    const result = allocObjectArray(size, size);
    for (0..size) |i| {
        arraySlots(result)[i] = v;
    }

    if (size == 0) {
        rc.lean_dec(v);
    } else if (size > 1) {
        rc.lean_inc_n(v, size - 1);
    }

    return result;
}

export fn lean_sarray_eq_cold(a1: *anyopaque, a2: *anyopaque) callconv(.c) bool {
    const elem_size = sarrayElemSize(a1);
    const len = checkedMul(elem_size, lean_sarray_size(a1));
    return std.mem.eql(u8, sarrayBytes(a1)[0..len], sarrayBytes(a2)[0..len]);
}

export fn lean_byte_array_mk(a: *anyopaque) callconv(.c) *anyopaque {
    const size = lean_array_size(a);
    const result = allocByteArray(size, size);
    for (0..size) |i| {
        sarrayBytes(result)[i] = @intCast(object.lean_unbox(lean_array_get_core(a, i)));
    }
    rc.lean_dec(a);
    return result;
}

export fn lean_byte_array_data(a: *anyopaque) callconv(.c) *anyopaque {
    const size = lean_sarray_size(a);
    const result = allocObjectArray(size, size);
    for (0..size) |i| {
        arraySlots(result)[i] = object.lean_box(@as(usize, sarrayBytes(a)[i]));
    }
    rc.lean_dec(a);
    return result;
}

export fn lean_copy_byte_array(a: *anyopaque) callconv(.c) *anyopaque {
    return copySArray(a, lean_sarray_capacity(a));
}

export fn lean_byte_array_hash(a: *anyopaque) callconv(.c) u64 {
    return std.hash.Wyhash.hash(11, sarrayBytes(a)[0..lean_sarray_size(a)]);
}

export fn lean_byte_array_push(a: *anyopaque, b: u8) callconv(.c) *anyopaque {
    const result = ensureExclusiveSArray(ensureCapacitySArray(a, lean_sarray_size(a) + 1, false));
    const size = lean_sarray_size(result);
    sarrayBytes(result)[size] = b;
    lean_sarray_set_size(result, size + 1);
    return result;
}

export fn lean_float_array_mk(a: *anyopaque) callconv(.c) *anyopaque {
    const size = lean_array_size(a);
    const result = allocFloatArray(size, size);
    for (0..size) |i| {
        floatSlots(result)[i] = box.lean_unbox_float(lean_array_get_core(a, i));
    }
    rc.lean_dec(a);
    return result;
}

export fn lean_float_array_data(a: *anyopaque) callconv(.c) *anyopaque {
    const size = lean_sarray_size(a);
    const result = allocObjectArray(size, size);
    for (0..size) |i| {
        arraySlots(result)[i] = box.lean_box_float(floatSlots(a)[i]);
    }
    rc.lean_dec(a);
    return result;
}

export fn lean_copy_float_array(a: *anyopaque) callconv(.c) *anyopaque {
    return copySArray(a, lean_sarray_capacity(a));
}

export fn lean_float_array_push(a: *anyopaque, d: f64) callconv(.c) *anyopaque {
    const result = ensureExclusiveSArray(ensureCapacitySArray(a, lean_sarray_size(a) + 1, false));
    const size = lean_sarray_size(result);
    floatSlots(result)[size] = d;
    lean_sarray_set_size(result, size + 1);
    return result;
}

test "lean_array_push increases size and stores value at last slot" {
    const array = allocObjectArray(0, 0);
    const pushed = lean_array_push(array, object.lean_box(42).?);
    defer freeIfHeap(pushed);

    try testing.expectEqual(@as(usize, 1), asArray(pushed).m_size);
    try testing.expectEqual(@as(usize, 42), object.lean_unbox(arraySlots(pushed)[0]));
}

test "lean_array_set and lean_array_get round-trip boxed values" {
    const array = allocObjectArray(2, 2);
    defer freeIfHeap(array);
    fillArraySlot(array, 0, object.lean_box(1));
    fillArraySlot(array, 1, object.lean_box(2));

    const updated = lean_array_set(array, object.lean_box(1), object.lean_box(7));
    const got = lean_array_get(object.lean_box(0), updated, object.lean_box(1));

    try testing.expectEqual(@as(usize, 7), object.lean_unbox(got));
}

test "lean_byte_array_push and get round-trip bytes" {
    const array = allocByteArray(0, 0);
    const pushed = lean_byte_array_push(array, 0x2a);
    defer freeIfHeap(pushed);

    try testing.expectEqual(@as(usize, 1), asSArray(pushed).m_size);
    try testing.expectEqual(@as(u8, 0x2a), lean_byte_array_get(pushed, object.lean_box(0)));
}

test "lean_float_array_set and get round-trip doubles" {
    const array = allocFloatArray(1, 1);
    defer freeIfHeap(array);
    floatSlots(array)[0] = 1.5;

    const updated = lean_float_array_set(array, object.lean_box(0), 3.25);

    try testing.expectEqual(@as(f64, 3.25), lean_float_array_get(updated, object.lean_box(0)));
}

test "non-exclusive object arrays copy before mutation" {
    const array = allocObjectArray(1, 1);
    defer freeIfHeap(array);
    fillArraySlot(array, 0, object.lean_box(5));
    rc.lean_inc(array);

    const updated = lean_array_set(array, object.lean_box(0), object.lean_box(9));
    defer freeIfHeap(updated);

    try testing.expect(updated != array);
    try testing.expectEqual(@as(usize, 5), object.lean_unbox(arraySlots(array)[0]));
    try testing.expectEqual(@as(usize, 9), object.lean_unbox(arraySlots(updated)[0]));
}
