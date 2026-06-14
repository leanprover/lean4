const std = @import("std");
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const io_error = @import("io_error.zig");
const io_result = @import("io_result.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");

var g_exit_on_panic = false;
var g_panic_messages = true;

fn writeStderr(bytes: []const u8) void {
    std.debug.print("{s}", .{bytes});
}

fn panicMessage(msg: []const u8, force_stderr: bool) void {
    if (!(force_stderr or g_panic_messages or g_exit_on_panic)) return;
    writeStderr(msg);
    writeStderr("\n");
}

fn internalPanicMessage(msg: []const u8) void {
    writeStderr("INTERNAL PANIC: ");
    writeStderr(msg);
    writeStderr("\n");
}

fn exitWithCodeOne() noreturn {
    std.process.exit(1);
}

fn asString(msg: *anyopaque) *lean.lean_string_object {
    return @ptrCast(@alignCast(msg));
}

fn stringMessage(msg: *anyopaque) []const u8 {
    const str = asString(msg);
    const size = if (str.m_size == 0) 0 else str.m_size - 1;
    const bytes: [*]const u8 = @ptrCast(&str.m_data);
    return bytes[0..size];
}

pub export fn lean_set_exit_on_panic(flag: bool) callconv(.c) void {
    g_exit_on_panic = flag;
}

pub export fn lean_set_panic_messages(flag: bool) callconv(.c) void {
    g_panic_messages = flag;
}

pub export fn lean_panic(msg: [*:0]const u8, force_stderr: bool) callconv(.c) void {
    panicMessage(std.mem.span(msg), force_stderr);
    exitWithCodeOne();
}

pub export fn lean_panic_fn(default_val: ?*anyopaque, msg: *anyopaque) callconv(.c) ?*anyopaque {
    _ = default_val;
    panicMessage(stringMessage(msg), false);
    exitWithCodeOne();
}

pub export fn lean_panic_fn_borrowed(default_val: ?*anyopaque, msg: *anyopaque) callconv(.c) ?*anyopaque {
    _ = default_val;
    panicMessage(stringMessage(msg), false);
    exitWithCodeOne();
}

pub export fn lean_internal_panic(msg: [*:0]const u8) callconv(.c) void {
    internalPanicMessage(std.mem.span(msg));
    exitWithCodeOne();
}

pub export fn lean_internal_panic_out_of_memory() callconv(.c) void {
    internalPanicMessage("out of memory");
    exitWithCodeOne();
}

pub export fn lean_internal_panic_unreachable() callconv(.c) void {
    internalPanicMessage("unreachable code has been reached");
    exitWithCodeOne();
}

pub export fn lean_internal_panic_rc_overflow() callconv(.c) void {
    internalPanicMessage("reference counter overflowed");
    exitWithCodeOne();
}

pub export fn lean_internal_panic_overflow() callconv(.c) void {
    internalPanicMessage("integer overflow in runtime computation");
    exitWithCodeOne();
}


pub const lean_io_initializing = io_result.lean_io_initializing;
pub const lean_io_mark_end_initialization = io_result.lean_io_mark_end_initialization;
pub const lean_io_result_get_error = io_result.lean_io_result_get_error;
pub const lean_io_result_get_value = io_result.lean_io_result_get_value;
pub const lean_io_result_is_error = io_result.lean_io_result_is_error;
pub const lean_io_result_is_ok = io_result.lean_io_result_is_ok;
pub const lean_io_result_mk_error = io_result.lean_io_result_mk_error;
pub const lean_io_result_mk_ok = io_result.lean_io_result_mk_ok;
pub const lean_io_result_show_error = io_result.lean_io_result_show_error;

fn lean_mk_io_error_already_exists(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_already_exists(os_code, details);
}

fn lean_mk_io_error_already_exists_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_already_exists_file(filename, os_code, details);
}

fn lean_mk_io_error_eof(unit: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_eof(unit);
}

fn lean_mk_io_error_hardware_fault(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_hardware_fault(os_code, details);
}

fn lean_mk_io_error_illegal_operation(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_illegal_operation(os_code, details);
}

fn lean_mk_io_error_inappropriate_type(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_inappropriate_type(os_code, details);
}

fn lean_mk_io_error_inappropriate_type_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_inappropriate_type_file(filename, os_code, details);
}

fn lean_mk_io_error_interrupted(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_interrupted(filename, os_code, details);
}

fn lean_mk_io_error_invalid_argument(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_invalid_argument(os_code, details);
}

fn lean_mk_io_error_invalid_argument_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_invalid_argument_file(filename, os_code, details);
}

fn lean_mk_io_error_no_file_or_directory(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_no_file_or_directory(filename, os_code, details);
}

fn lean_mk_io_error_no_such_thing(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_no_such_thing(os_code, details);
}

fn lean_mk_io_error_no_such_thing_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_no_such_thing_file(filename, os_code, details);
}

fn lean_mk_io_error_other_error(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_other_error(os_code, details);
}

fn lean_mk_io_error_permission_denied(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_permission_denied(os_code, details);
}

fn lean_mk_io_error_permission_denied_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_permission_denied_file(filename, os_code, details);
}

fn lean_mk_io_error_protocol_error(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_protocol_error(os_code, details);
}

fn lean_mk_io_error_resource_busy(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_resource_busy(os_code, details);
}

fn lean_mk_io_error_resource_exhausted(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_resource_exhausted(os_code, details);
}

fn lean_mk_io_error_resource_exhausted_file(filename: *anyopaque, os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_resource_exhausted_file(filename, os_code, details);
}

fn lean_mk_io_error_resource_vanished(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_resource_vanished(os_code, details);
}

fn lean_mk_io_error_time_expired(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_time_expired(os_code, details);
}

fn lean_mk_io_error_unsatisfied_constraints(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_unsatisfied_constraints(os_code, details);
}

fn lean_mk_io_error_unsupported_operation(os_code: u32, details: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_error_unsupported_operation(os_code, details);
}


// Minimal stub implementations for programs that link the Zig runtime without
// the Lean standard library. These are sufficient for trivial IO smoke tests.

fn stringBytes(msg: *anyopaque) []const u8 {
    const str: *lean.lean_string_object = @ptrCast(@alignCast(msg));
    const size = if (str.m_size == 0) 0 else str.m_size - 1;
    const bytes: [*]const u8 = @ptrCast(&str.m_data);
    return bytes[0..size];
}

fn stdoutPutStr(str_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    const bytes = stringBytes(str_obj);
    _ = std.c.write(1, bytes.ptr, bytes.len);
    return io_result.lean_io_result_mk_ok(world_obj);
}

export fn initialize_Init(builtin: u8) callconv(.c) *anyopaque {
    _ = builtin;
    return io_result.lean_io_result_mk_ok(object.lean_box(0).?);
}

export fn lean_get_stdout() callconv(.c) *anyopaque {
    const stream = alloc.lean_alloc_ctor(0, 6, 0);
    const put_str = alloc.lean_alloc_closure(@constCast(@ptrCast(&stdoutPutStr)), 2, 0);
    ctor.lean_ctor_set(stream, 0, object.lean_box(0).?); // flush
    ctor.lean_ctor_set(stream, 1, object.lean_box(0).?); // read
    ctor.lean_ctor_set(stream, 2, object.lean_box(0).?); // write
    ctor.lean_ctor_set(stream, 3, object.lean_box(0).?); // getLine
    ctor.lean_ctor_set(stream, 4, put_str);              // putStr
    ctor.lean_ctor_set(stream, 5, object.lean_box(0).?); // isTty
    return stream;
}
fn lean_mk_io_user_error(msg: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_user_error(msg);
}
