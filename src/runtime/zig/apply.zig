const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");

const Obj = ?*anyopaque;
const max_direct_args = 16;

const Fn1 = *const fn (Obj) callconv(.c) Obj;
const Fn2 = *const fn (Obj, Obj) callconv(.c) Obj;
const Fn3 = *const fn (Obj, Obj, Obj) callconv(.c) Obj;
const Fn4 = *const fn (Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn5 = *const fn (Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn6 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn7 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn8 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn9 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn10 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn11 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn12 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn13 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn14 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn15 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fn16 = *const fn (Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) callconv(.c) Obj;
const Fnn = *const fn ([*]Obj) callconv(.c) Obj;

fn closurePtr(o: *anyopaque) *lean.lean_closure_object {
    return @ptrCast(@alignCast(o));
}

fn closureSlots(o: *lean.lean_closure_object) [*]Obj {
    return @ptrCast(&o.m_objs);
}

fn opaqueFunPtr(fun: anytype) Obj {
    return @ptrCast(@constCast(fun));
}

fn castFun(comptime F: type, raw: Obj) F {
    return @ptrFromInt(@intFromPtr(raw orelse @panic("null closure function")));
}

fn initCallArgs(arity: usize, stack: *[max_direct_args]Obj) []Obj {
    if (arity <= max_direct_args) return stack[0..arity];
    return std.heap.page_allocator.alloc(Obj, arity) catch @panic("out of memory");
}

fn deinitCallArgs(arity: usize, args: []Obj) void {
    if (arity > max_direct_args) std.heap.page_allocator.free(args);
}

fn copyExistingFixed(target: []Obj, source: [*]Obj, fixed: usize, exclusive: bool) void {
    for (0..fixed) |i| {
        const value = source[i];
        if (!exclusive) rc.lean_inc(value);
        target[i] = value;
    }
}

fn fillProvidedArgs(target: []Obj, start: usize, provided: []const Obj, count: usize) void {
    for (0..count) |i| {
        target[start + i] = provided[i];
    }
}

fn callFunction(fun: Obj, args: []const Obj) Obj {
    return switch (args.len) {
        1 => castFun(Fn1, fun)(args[0]),
        2 => castFun(Fn2, fun)(args[0], args[1]),
        3 => castFun(Fn3, fun)(args[0], args[1], args[2]),
        4 => castFun(Fn4, fun)(args[0], args[1], args[2], args[3]),
        5 => castFun(Fn5, fun)(args[0], args[1], args[2], args[3], args[4]),
        6 => castFun(Fn6, fun)(args[0], args[1], args[2], args[3], args[4], args[5]),
        7 => castFun(Fn7, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]),
        8 => castFun(Fn8, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]),
        9 => castFun(Fn9, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8]),
        10 => castFun(Fn10, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9]),
        11 => castFun(Fn11, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10]),
        12 => castFun(Fn12, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11]),
        13 => castFun(Fn13, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12]),
        14 => castFun(Fn14, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13]),
        15 => castFun(Fn15, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14]),
        16 => castFun(Fn16, fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15]),
        else => castFun(Fnn, fun)(@constCast(args.ptr)),
    };
}

fn fixArgs(f: *anyopaque, provided: []const Obj) *anyopaque {
    const closure = closurePtr(f);
    const fixed: usize = closure.m_num_fixed;
    const new_fixed = fixed + provided.len;
    std.debug.assert(new_fixed < closure.m_arity);

    const result_ptr = alloc.lean_alloc_closure(closure.m_fun, closure.m_arity, @intCast(new_fixed));
    const result: *lean.lean_closure_object = @ptrCast(@alignCast(result_ptr));
    const source = closureSlots(closure);
    const target = closureSlots(result);

    if (rc.lean_is_exclusive(f)) {
        for (0..fixed) |i| target[i] = source[i];
        alloc.lean_free_object(f);
    } else {
        for (0..fixed) |i| {
            target[i] = source[i];
            rc.lean_inc(target[i]);
        }
        rc.lean_dec_ref(f);
    }

    for (provided, fixed..) |arg, i| target[i] = arg;
    return result_ptr;
}

fn applySlice(f: *anyopaque, provided: []const Obj) Obj {
    if (provided.len == 0) @panic("lean_apply_n requires at least one argument");

    if (object.lean_is_scalar(f)) {
        for (provided) |arg| rc.lean_dec(arg);
        return f;
    }

    const closure = closurePtr(f);
    const arity: usize = closure.m_arity;
    const fixed: usize = closure.m_num_fixed;
    const total = fixed + provided.len;

    if (total < arity) {
        return fixArgs(f, provided);
    }

    var stack: [max_direct_args]Obj = undefined;
    const args = initCallArgs(arity, &stack);
    defer deinitCallArgs(arity, args);

    if (total == arity) {
        const exclusive = rc.lean_is_exclusive(f);
        copyExistingFixed(args, closureSlots(closure), fixed, exclusive);
        fillProvidedArgs(args, fixed, provided, provided.len);
        const result = callFunction(closure.m_fun, args);
        if (exclusive) {
            alloc.lean_free_object(f);
        } else {
            rc.lean_dec_ref(f);
        }
        return result;
    }

    copyExistingFixed(args, closureSlots(closure), fixed, false);
    const consumed_from_provided = arity - fixed;
    fillProvidedArgs(args, fixed, provided, consumed_from_provided);
    const next = callFunction(closure.m_fun, args) orelse @panic("closure application returned null");
    rc.lean_dec_ref(f);
    return applySlice(next, provided[consumed_from_provided..]);
}

pub export fn lean_apply_1(f: *anyopaque, a1: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{a1};
    return applySlice(f, args[0..]);
}

export fn lean_apply_2(f: *anyopaque, a1: *anyopaque, a2: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_3(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_4(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_5(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_6(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_7(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_8(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_9(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_10(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_11(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_12(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque, a12: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_13(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque, a12: *anyopaque, a13: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_14(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque, a12: *anyopaque, a13: *anyopaque, a14: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_15(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque, a12: *anyopaque, a13: *anyopaque, a14: *anyopaque, a15: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_16(f: *anyopaque, a1: *anyopaque, a2: *anyopaque, a3: *anyopaque, a4: *anyopaque, a5: *anyopaque, a6: *anyopaque, a7: *anyopaque, a8: *anyopaque, a9: *anyopaque, a10: *anyopaque, a11: *anyopaque, a12: *anyopaque, a13: *anyopaque, a14: *anyopaque, a15: *anyopaque, a16: *anyopaque) callconv(.c) Obj {
    const args = [_]Obj{ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 };
    return applySlice(f, args[0..]);
}

export fn lean_apply_n(f: *anyopaque, n: c_uint, args: [*]Obj) callconv(.c) Obj {
    return switch (n) {
        0 => @panic("lean_apply_n requires at least one argument"),
        1 => lean_apply_1(f, args[0].?),
        2 => lean_apply_2(f, args[0].?, args[1].?),
        3 => lean_apply_3(f, args[0].?, args[1].?, args[2].?),
        4 => lean_apply_4(f, args[0].?, args[1].?, args[2].?, args[3].?),
        5 => lean_apply_5(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?),
        6 => lean_apply_6(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?),
        7 => lean_apply_7(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?),
        8 => lean_apply_8(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?),
        9 => lean_apply_9(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?),
        10 => lean_apply_10(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?),
        11 => lean_apply_11(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?),
        12 => lean_apply_12(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?, args[11].?),
        13 => lean_apply_13(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?, args[11].?, args[12].?),
        14 => lean_apply_14(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?, args[11].?, args[12].?, args[13].?),
        15 => lean_apply_15(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?, args[11].?, args[12].?, args[13].?, args[14].?),
        16 => lean_apply_16(f, args[0].?, args[1].?, args[2].?, args[3].?, args[4].?, args[5].?, args[6].?, args[7].?, args[8].?, args[9].?, args[10].?, args[11].?, args[12].?, args[13].?, args[14].?, args[15].?),
        else => lean_apply_m(f, n, args),
    };
}

export fn lean_apply_m(f: *anyopaque, n: c_uint, args: [*]Obj) callconv(.c) Obj {
    return applySlice(f, args[0..n]);
}

fn testFn2(a1: Obj, a2: Obj) callconv(.c) Obj {
    return object.lean_box(object.lean_unbox(a1) + object.lean_unbox(a2));
}

fn testFn3(a1: Obj, a2: Obj, a3: Obj) callconv(.c) Obj {
    return object.lean_box(object.lean_unbox(a1) + object.lean_unbox(a2) + object.lean_unbox(a3));
}

fn outerCurried(a1: Obj) callconv(.c) Obj {
    const closure_ptr = alloc.lean_alloc_closure(opaqueFunPtr(&testFn2), 2, 1);
    const closure = closurePtr(closure_ptr);
    closureSlots(closure)[0] = a1;
    return closure_ptr;
}

fn testFn17(args: [*]Obj) callconv(.c) Obj {
    var sum: usize = 0;
    for (0..17) |i| sum += object.lean_unbox(args[i]);
    return object.lean_box(sum);
}

test "lean_alloc_closure returns a closure with expected metadata" {
    const fn_ptr = opaqueFunPtr(&testFn2);
    const ptr = alloc.lean_alloc_closure(fn_ptr, 2, 1);
    defer alloc.lean_free_object(ptr);

    const closure = closurePtr(ptr);
    try testing.expectEqual(lean.LeanClosure, closure.m_header.m_tag);
    try testing.expectEqual(fn_ptr, closure.m_fun);
    try testing.expectEqual(@as(u16, 2), closure.m_arity);
    try testing.expectEqual(@as(u16, 1), closure.m_num_fixed);
}

test "lean_apply_2 exact arity calls the underlying function" {
    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&testFn2), 2, 0);
    const result = lean_apply_2(
        closure,
        object.lean_box(20).?,
        object.lean_box(22).?,
    );

    try testing.expectEqual(@as(usize, 42), object.lean_unbox(result));
}

test "lean_apply_2 under arity returns a partial closure with existing and new fixed args" {
    const closure_ptr = alloc.lean_alloc_closure(opaqueFunPtr(&testFn3), 4, 1);
    const closure = closurePtr(closure_ptr);
    closureSlots(closure)[0] = object.lean_box(7);

    const partial_ptr = lean_apply_2(
        closure_ptr,
        object.lean_box(8).?,
        object.lean_box(9).?,
    ) orelse @panic("expected partial closure");
    defer alloc.lean_free_object(partial_ptr);

    const partial = closurePtr(partial_ptr);
    const slots = closureSlots(partial);
    try testing.expectEqual(lean.LeanClosure, partial.m_header.m_tag);
    try testing.expectEqual(@as(u16, 4), partial.m_arity);
    try testing.expectEqual(@as(u16, 3), partial.m_num_fixed);
    try testing.expectEqual(@as(usize, 7), object.lean_unbox(slots[0]));
    try testing.expectEqual(@as(usize, 8), object.lean_unbox(slots[1]));
    try testing.expectEqual(@as(usize, 9), object.lean_unbox(slots[2]));
}

test "lean_apply_2 over arity re-applies remaining arguments to the returned closure" {
    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&outerCurried), 1, 0);
    const result = lean_apply_2(
        closure,
        object.lean_box(4).?,
        object.lean_box(5).?,
    );

    try testing.expectEqual(@as(usize, 9), object.lean_unbox(result));
}

test "lean_apply_n dispatches through the fixed-arity helpers" {
    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&testFn2), 2, 0);
    var args = [_]Obj{ object.lean_box(6), object.lean_box(7) };
    const result = lean_apply_n(closure, 2, &args);

    try testing.expectEqual(@as(usize, 13), object.lean_unbox(result));
}

test "lean_apply_m supports closures above the direct arity limit" {
    const closure = alloc.lean_alloc_closure(opaqueFunPtr(&testFn17), 17, 0);
    var args: [17]Obj = undefined;
    for (0..17) |i| args[i] = object.lean_box(i + 1);

    const result = lean_apply_m(closure, 17, &args);
    try testing.expectEqual(@as(usize, 153), object.lean_unbox(result));
}
