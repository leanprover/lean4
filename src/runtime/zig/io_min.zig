const std = @import("std");
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const io_error = @import("io_error.zig");
const io_result = @import("io_result.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const mpz_zig = @import("mpz_zig");
const runtime_options = @import("runtime_options");

const gmp = struct {
    extern fn __gmpz_get_d(op: *const mpz_zig.Mpz) callconv(.c) f64;
};
var g_exit_on_panic = false;
var g_panic_messages = true;
var g_stdout: ?*anyopaque = null;
var g_stderr: ?*anyopaque = null;
var g_stdin: ?*anyopaque = null;

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


// Minimal IO implementation for programs that link the Zig runtime without the
// Lean standard library. `initialize_Init` creates the standard streams; the
// getters return cached objects and the setters swap them, matching the C++
// runtime convention used by `Init.System.IO`.

extern fn lean_mk_string_unchecked(s: [*:0]const u8, sz: usize, len: usize) callconv(.c) *anyopaque;

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

fn stderrPutStr(str_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    const bytes = stringBytes(str_obj);
    _ = std.c.write(2, bytes.ptr, bytes.len);
    return io_result.lean_io_result_mk_ok(world_obj);
}

fn streamWriteFd(fd: c_int, ba_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    const ba: *lean.lean_sarray_object = @ptrCast(@alignCast(ba_obj));
    const bytes: [*]const u8 = @ptrCast(&ba.m_data);
    _ = std.c.write(fd, bytes, ba.m_size);
    return io_result.lean_io_result_mk_ok(world_obj);
}

fn stdoutWrite(ba_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    return streamWriteFd(1, ba_obj, world_obj);
}

fn stderrWrite(ba_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    return streamWriteFd(2, ba_obj, world_obj);
}

fn streamFlush(world_obj: *anyopaque) callconv(.c) *anyopaque {
    return io_result.lean_io_result_mk_ok(world_obj);
}

fn streamReadEmpty(n_obj: *anyopaque, _: *anyopaque) callconv(.c) *anyopaque {
    const n = object.lean_unbox(n_obj);
    const ba: *lean.lean_sarray_object = @ptrCast(@alignCast(alloc.lean_alloc_sarray(1, 0, n)));
    return io_result.lean_io_result_mk_ok(ba);
}

fn stdinRead(n_obj: *anyopaque, _: *anyopaque) callconv(.c) *anyopaque {
    const n = object.lean_unbox(n_obj);
    const ba: *lean.lean_sarray_object = @ptrCast(@alignCast(alloc.lean_alloc_sarray(1, 0, n)));
    if (n > 0) {
        const bytes: [*]u8 = @ptrCast(&ba.m_data);
        const got = std.c.read(0, bytes, n);
        if (got >= 0) {
            ba.m_size = @intCast(got);
        }
    }
    return io_result.lean_io_result_mk_ok(ba);
}
fn streamGetLineEmpty(_: *anyopaque) callconv(.c) *anyopaque {
    return io_result.lean_io_result_mk_ok(lean_mk_string_unchecked(@ptrCast("".ptr), 0, 0));
}

fn streamIsTtyFalse(_: *anyopaque) callconv(.c) *anyopaque {
    return io_result.lean_io_result_mk_ok(object.lean_box(0).?);
}

fn makeStreamClosure(comptime fun: anytype) *anyopaque {
    return alloc.lean_alloc_closure(@constCast(@ptrCast(&fun)), 1, 0);
}

fn makeStreamClosure2(comptime fun: anytype) *anyopaque {
    return alloc.lean_alloc_closure(@constCast(@ptrCast(&fun)), 2, 0);
}

fn makeOutputStream(put_str: anytype, write_fn: anytype) *anyopaque {
    const stream = alloc.lean_alloc_ctor(0, 6, 0);
    ctor.lean_ctor_set(stream, 0, makeStreamClosure(streamFlush));
    ctor.lean_ctor_set(stream, 1, makeStreamClosure2(streamReadEmpty));
    ctor.lean_ctor_set(stream, 2, makeStreamClosure2(write_fn));
    ctor.lean_ctor_set(stream, 3, makeStreamClosure(streamGetLineEmpty));
    ctor.lean_ctor_set(stream, 4, makeStreamClosure2(put_str));
    ctor.lean_ctor_set(stream, 5, makeStreamClosure(streamIsTtyFalse));
    return stream;
}

fn makeInputStream() *anyopaque {
    const stream = alloc.lean_alloc_ctor(0, 6, 0);
    ctor.lean_ctor_set(stream, 0, makeStreamClosure(streamFlush));
    ctor.lean_ctor_set(stream, 1, makeStreamClosure2(stdinRead));
    ctor.lean_ctor_set(stream, 2, makeStreamClosure2(streamWriteFdNoop));
    ctor.lean_ctor_set(stream, 3, makeStreamClosure(streamGetLineEmpty));
    ctor.lean_ctor_set(stream, 4, makeStreamClosure2(streamWriteFdNoop));
    ctor.lean_ctor_set(stream, 5, makeStreamClosure(streamIsTtyFalse));
    return stream;
}

fn streamWriteFdNoop(_: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    return io_result.lean_io_result_mk_ok(world_obj);
}

fn ioPrintlnAction(str_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    const bytes = stringBytes(str_obj);
    _ = std.c.write(1, bytes.ptr, bytes.len);
    _ = std.c.write(1, "\n".ptr, 1);
    return io_result.lean_io_result_mk_ok(world_obj);
}

fn ioEprintlnAction(str_obj: *anyopaque, world_obj: *anyopaque) callconv(.c) *anyopaque {
    const bytes = stringBytes(str_obj);
    _ = std.c.write(2, bytes.ptr, bytes.len);
    _ = std.c.write(2, "\n".ptr, 1);
    return io_result.lean_io_result_mk_ok(world_obj);
}

// IO.println / IO.eprintln are compiled to functions that return an already-
// executed IO result (not a suspended closure), matching the convention used by
// the generated main wrapper.
export fn lean_io_println(str_obj: *anyopaque) callconv(.c) *anyopaque {
    return ioPrintlnAction(str_obj, object.lean_box(0).?);
}

fn lean_io_eprintln_impl(str_obj: *anyopaque) callconv(.c) *anyopaque {
    return ioEprintlnAction(str_obj, object.lean_box(0).?);
}
// Mangled name emitted by the Lean compiler for IO.eprintln in some modules.
fn l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(str_obj: *anyopaque) callconv(.c) *anyopaque {
    return lean_io_eprintln_impl(str_obj);
}
comptime {
    if (runtime_options.export_lean_helpers) {
        @export(&lean_io_eprintln_impl, .{ .name = "lean_io_eprintln" });
        @export(&l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0, .{ .name = "l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0" });
    }
}

fn natToF64(n: *anyopaque) f64 {
    if (object.lean_is_scalar(n)) {
        return @floatFromInt(object.lean_unbox(n));
    } else {
        const mpz_obj: *lean.MpzObject = @ptrCast(@alignCast(n));
        const mpz: *mpz_zig.Mpz = @ptrCast(@alignCast(&mpz_obj.m_value));
        return gmp.__gmpz_get_d(mpz);
    }
}

// Mangled name emitted by the Lean compiler for Float.ofScientific.
fn l_Float_ofScientific(m: *anyopaque, s: u8, e: *anyopaque) callconv(.c) f64 {
    const mantissa = natToF64(m);
    const exponent = object.lean_unbox(e);
    const factor = std.math.pow(f64, 10.0, @floatFromInt(exponent));
    if (s != 0) {
        return mantissa / factor;
    } else {
        return mantissa * factor;
    }
}
comptime {
    if (runtime_options.export_lean_helpers) {
        @export(&l_Float_ofScientific, .{ .name = "l_Float_ofScientific" });
    }
}

export fn initialize_Init(builtin: u8) callconv(.c) *anyopaque {
    _ = builtin;
    if (g_stdout == null) g_stdout = makeOutputStream(stdoutPutStr, stdoutWrite);
    if (g_stderr == null) g_stderr = makeOutputStream(stderrPutStr, stderrWrite);
    if (g_stdin == null) g_stdin = makeInputStream();
    return io_result.lean_io_result_mk_ok(object.lean_box(0).?);
}

fn getStreamOrInit(current: *?*anyopaque, make: *const fn () callconv(.c) *anyopaque) *anyopaque {
    const s = current.* orelse make();
    rc.lean_inc_ref(s);
    return s;
}

export fn lean_get_stdout() callconv(.c) *anyopaque {
    return getStreamOrInit(&g_stdout, struct {
        fn make() callconv(.c) *anyopaque {
            return makeOutputStream(stdoutPutStr, stdoutWrite);
        }
    }.make);
}

export fn lean_get_stderr() callconv(.c) *anyopaque {
    return getStreamOrInit(&g_stderr, struct {
        fn make() callconv(.c) *anyopaque {
            return makeOutputStream(stderrPutStr, stderrWrite);
        }
    }.make);
}

export fn lean_get_stdin() callconv(.c) *anyopaque {
    return getStreamOrInit(&g_stdin, struct {
        fn make() callconv(.c) *anyopaque {
            return makeInputStream();
        }
    }.make);
}

fn setStream(current: *?*anyopaque, h: *anyopaque, fallback: *const fn () callconv(.c) *anyopaque) *anyopaque {
    const old = current.* orelse fallback();
    current.* = h;
    rc.lean_inc_ref(h);
    return old;
}

export fn lean_get_set_stdout(h: *anyopaque) callconv(.c) *anyopaque {
    return setStream(&g_stdout, h, struct {
        fn make() callconv(.c) *anyopaque {
            return makeOutputStream(stdoutPutStr, stdoutWrite);
        }
    }.make);
}

export fn lean_get_set_stderr(h: *anyopaque) callconv(.c) *anyopaque {
    return setStream(&g_stderr, h, struct {
        fn make() callconv(.c) *anyopaque {
            return makeOutputStream(stderrPutStr, stderrWrite);
        }
    }.make);
}

export fn lean_get_set_stdin(h: *anyopaque) callconv(.c) *anyopaque {
    return setStream(&g_stdin, h, struct {
        fn make() callconv(.c) *anyopaque {
            return makeInputStream();
        }
    }.make);
}

fn lean_mk_io_user_error(msg: *anyopaque) *anyopaque {
    return io_error.lean_mk_io_user_error(msg);
}
test "initialize_Init creates stdout, stderr, and stdin streams" {
    g_stdout = null;
    g_stderr = null;
    g_stdin = null;
    const res = initialize_Init(1);
    defer rc.lean_dec(res);
    try std.testing.expect(g_stdout != null);
    try std.testing.expect(g_stderr != null);
    try std.testing.expect(g_stdin != null);
}
test "lean_get_set_stdout swaps the current stream and returns the previous one" {
    g_stdout = null;
    const init_res = initialize_Init(1);
    defer rc.lean_dec(init_res);
    const original = lean_get_stdout();
    defer rc.lean_dec_ref(original);
    const replacement = makeOutputStream(stdoutPutStr, stdoutWrite);
    const old = lean_get_set_stdout(replacement);
    defer rc.lean_dec_ref(old);
    try std.testing.expectEqual(original, old);
    const current = lean_get_stdout();
    defer rc.lean_dec_ref(current);
    try std.testing.expectEqual(replacement, current);
}
