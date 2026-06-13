// Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

const mpz_zig = @import("mpz_zig");

pub const lean_object = extern struct {
    m_rc: i32,
    m_cs_sz: u16,
    m_other: u8,
    m_tag: u8,
};

pub const lean_ctor_object = extern struct {
    m_header: lean_object,
    m_objs: [0]?*anyopaque,
};

pub const lean_array_object = extern struct {
    m_header: lean_object,
    m_size: usize,
    m_capacity: usize,
    m_data: [0]?*anyopaque,
};

pub const lean_sarray_object = extern struct {
    m_header: lean_object,
    m_size: usize,
    m_capacity: usize,
    m_data: [0]u8,
};

pub const lean_string_object = extern struct {
    m_header: lean_object,
    m_size: usize,
    m_capacity: usize,
    m_length: usize,
    m_data: [0]u8,
};

pub const lean_closure_object = extern struct {
    m_header: lean_object,
    m_fun: ?*anyopaque,
    m_arity: u16,
    m_num_fixed: u16,
    m_objs: [0]?*anyopaque,
};

pub const lean_ref_object = extern struct {
    m_header: lean_object,
    m_value: ?*anyopaque,
};

pub const lean_thunk_object = extern struct {
    m_header: lean_object,
    m_value: ?*anyopaque,
    m_closure: ?*anyopaque,
};

pub const lean_task_imp = extern struct {
    m_closure: ?*anyopaque,
    m_head_dep: ?*lean_task_object,
    m_next_dep: ?*lean_task_object,
    m_prio: c_uint,
    m_canceled: u8,
    m_keep_alive: u8,
    m_deleted: u8,
};

pub const lean_task_object = extern struct {
    m_header: lean_object,
    m_value: ?*anyopaque,
    m_imp: ?*lean_task_imp,
};

pub const lean_promise_object = extern struct {
    m_header: lean_object,
    m_result: ?*lean_task_object,
};

pub const lean_external_finalize_proc = *const fn (*anyopaque) callconv(.c) void;
pub const lean_external_foreach_proc = *const fn (*anyopaque, ?*anyopaque) callconv(.c) void;

pub const lean_external_class = extern struct {
    m_finalize: lean_external_finalize_proc,
    m_foreach: lean_external_foreach_proc,
};

pub const lean_external_object = extern struct {
    m_header: lean_object,
    m_class: *lean_external_class,
    m_data: ?*anyopaque,
};

pub const MpzObject = extern struct {
    m_header: lean_object,
    m_value: [@sizeOf(mpz_zig.Mpz)]u8 align(@alignOf(mpz_zig.Mpz)),
};

pub const LeanMaxCtorTag: u8 = 243;
pub const LeanPromise: u8 = 244;
pub const LeanClosure: u8 = 245;
pub const LeanArray: u8 = 246;
pub const LeanStructArray: u8 = 247;
pub const LeanScalarArray: u8 = 248;
pub const LeanString: u8 = 249;
pub const LeanMPZ: u8 = 250;
pub const LeanThunk: u8 = 251;
pub const LeanTask: u8 = 252;
pub const LeanRef: u8 = 253;
pub const LeanExternal: u8 = 254;
pub const LeanReserved: u8 = 255;

comptime {
    if (@sizeOf(lean_object) != 8) @compileError("lean_object must be 8 bytes");
    if (@sizeOf(lean_thunk_object) != 24) @compileError("lean_thunk_object must be 24 bytes");
    if (@offsetOf(lean_thunk_object, "m_header") != 0) @compileError("lean_thunk_object.m_header must be at offset 0");
    if (@offsetOf(lean_thunk_object, "m_value") != 8) @compileError("lean_thunk_object.m_value must be at offset 8");
    if (@offsetOf(lean_thunk_object, "m_closure") != 16) @compileError("lean_thunk_object.m_closure must be at offset 16");
    if (@sizeOf(lean_task_imp) != 32) @compileError("lean_task_imp must be 32 bytes");
    if (@offsetOf(lean_task_imp, "m_closure") != 0) @compileError("lean_task_imp.m_closure must be at offset 0");
    if (@offsetOf(lean_task_imp, "m_head_dep") != 8) @compileError("lean_task_imp.m_head_dep must be at offset 8");
    if (@offsetOf(lean_task_imp, "m_next_dep") != 16) @compileError("lean_task_imp.m_next_dep must be at offset 16");
    if (@offsetOf(lean_task_imp, "m_prio") != 24) @compileError("lean_task_imp.m_prio must be at offset 24");
    if (@offsetOf(lean_task_imp, "m_canceled") != 28) @compileError("lean_task_imp.m_canceled must be at offset 28");
    if (@offsetOf(lean_task_imp, "m_keep_alive") != 29) @compileError("lean_task_imp.m_keep_alive must be at offset 29");
    if (@offsetOf(lean_task_imp, "m_deleted") != 30) @compileError("lean_task_imp.m_deleted must be at offset 30");
    if (@sizeOf(lean_task_object) != 24) @compileError("lean_task_object must be 24 bytes");
    if (@offsetOf(lean_task_object, "m_header") != 0) @compileError("lean_task_object.m_header must be at offset 0");
    if (@offsetOf(lean_task_object, "m_value") != 8) @compileError("lean_task_object.m_value must be at offset 8");
    if (@offsetOf(lean_task_object, "m_imp") != 16) @compileError("lean_task_object.m_imp must be at offset 16");
    if (@sizeOf(lean_promise_object) != 16) @compileError("lean_promise_object must be 16 bytes");
    if (@offsetOf(lean_promise_object, "m_header") != 0) @compileError("lean_promise_object.m_header must be at offset 0");
    if (@offsetOf(lean_promise_object, "m_result") != 8) @compileError("lean_promise_object.m_result must be at offset 8");
    if (@offsetOf(MpzObject, "m_header") != 0) @compileError("MpzObject header must start at offset 0");
    if (@offsetOf(MpzObject, "m_value") != @sizeOf(lean_object)) @compileError("MpzObject payload must follow lean_object header");
}
