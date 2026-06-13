const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const ctor = @import("ctor.zig");
const io_error = @import("io_error.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const string = @import("string.zig");
const lean = @import("lean_object.zig");
const libc = struct {
    extern fn strerror(errnum: c_int) callconv(.c) [*:0]const u8;
};

const DecodeKind = enum {
    already_exists,
    hardware_fault,
    inappropriate_type,
    interrupted,
    invalid_argument,
    no_file_or_directory,
    other_error,
    permission_denied,
    resource_busy,
    resource_exhausted,
    resource_vanished,
    time_expired,
    unsupported_operation,
};

fn stringBytes(str_obj: *anyopaque) []const u8 {
    const str: *const lean.lean_string_object = @ptrCast(@alignCast(str_obj));
    const size = if (str.m_size == 0) 0 else str.m_size - 1;
    const data: [*]const u8 = @ptrCast(&str.m_data);
    return data[0..size];
}

fn errnoCode(errnum: c_int) u32 {
    return @bitCast(@as(i32, errnum));
}

var g_empty_filename: ?*anyopaque = null;
var g_details_enoent: ?*anyopaque = null;
var g_details_eacces: ?*anyopaque = null;
var g_details_eexist: ?*anyopaque = null;
var g_details_ebusy: ?*anyopaque = null;
var g_details_enospc: ?*anyopaque = null;
var g_details_eagain: ?*anyopaque = null;
var g_details_eintr: ?*anyopaque = null;
var g_details_epipe: ?*anyopaque = null;

fn persistentAscii(bytes: []const u8) *anyopaque {
    const value = string.mkAsciiStringBytes(bytes);
    rc.lean_mark_persistent(value);
    return value;
}

fn persistentErrnoDetails(errnum: c_int) *anyopaque {
    return persistentAscii(std.mem.span(libc.strerror(errnum)));
}

pub fn initializeDecodeCache() void {
    if (g_empty_filename != null) return;

    g_empty_filename = persistentAscii("");
    g_details_enoent = persistentErrnoDetails(@intFromEnum(std.posix.E.NOENT));
    g_details_eacces = persistentErrnoDetails(@intFromEnum(std.posix.E.ACCES));
    g_details_eexist = persistentErrnoDetails(@intFromEnum(std.posix.E.EXIST));
    g_details_ebusy = persistentErrnoDetails(@intFromEnum(std.posix.E.BUSY));
    g_details_enospc = persistentErrnoDetails(@intFromEnum(std.posix.E.NOSPC));
    g_details_eagain = persistentErrnoDetails(@intFromEnum(std.posix.E.AGAIN));
    g_details_eintr = persistentErrnoDetails(@intFromEnum(std.posix.E.INTR));
    g_details_epipe = persistentErrnoDetails(@intFromEnum(std.posix.E.PIPE));
}

fn ensureDecodeCache() void {
    if (g_empty_filename == null) initializeDecodeCache();
}

fn cachedErrnoDetails(errnum: c_int) ?*anyopaque {
    ensureDecodeCache();
    return switch (@as(std.posix.E, @enumFromInt(errnum))) {
        .NOENT => g_details_enoent,
        .ACCES => g_details_eacces,
        .EXIST => g_details_eexist,
        .BUSY => g_details_ebusy,
        .NOSPC => g_details_enospc,
        .AGAIN => g_details_eagain,
        .INTR => g_details_eintr,
        .PIPE => g_details_epipe,
        else => null,
    };
}

fn mkErrnoDetails(errnum: c_int) *anyopaque {
    return cachedErrnoDetails(errnum) orelse string.mkAsciiStringBytes(std.mem.span(libc.strerror(errnum)));
}

fn mkUnknownDetails(errnum: c_int) *anyopaque {
    var buf: [64]u8 = undefined;
    const msg = std.fmt.bufPrint(&buf, "unknown IO error {d}", .{errnum}) catch unreachable;
    return string.mkAsciiStringBytes(msg);
}

fn filenameOrEmpty(fname: ?*anyopaque) *anyopaque {
    if (fname) |name| {
        rc.lean_inc(name);
        return name;
    }
    ensureDecodeCache();
    return g_empty_filename.?;
}

fn withOptionalFilename(
    fname: ?*anyopaque,
    code: u32,
    details: *anyopaque,
    no_fname_ctor: *const fn (u32, *anyopaque) *anyopaque,
    fname_ctor: *const fn (*anyopaque, u32, *anyopaque) *anyopaque,
) *anyopaque {
    if (fname) |name| {
        rc.lean_inc(name);
        return fname_ctor(name, code, details);
    }
    return no_fname_ctor(code, details);
}

fn withDirectFilename(
    fname: ?*anyopaque,
    code: u32,
    details: *anyopaque,
    direct_ctor: *const fn (*anyopaque, u32, *anyopaque) *anyopaque,
) *anyopaque {
    return direct_ctor(filenameOrEmpty(fname), code, details);
}

fn matchesErrno(comptime name: []const u8, err: std.posix.E) bool {
    if (!@hasField(std.posix.E, name)) return false;
    return err == @field(std.posix.E, name);
}

fn classifyErrno(err: std.posix.E) DecodeKind {
    return switch (err) {
        .EXIST => .already_exists,
        .BUSY => .resource_busy,
        .ACCES, .PERM, .ROFS, .FBIG => .permission_denied,
        .AGAIN, .NOSPC, .NOMEM, .MFILE, .NFILE => .resource_exhausted,
        .INTR => .interrupted,
        .INVAL => .invalid_argument,
        .NOENT => .no_file_or_directory,
        .NOTDIR, .ISDIR => .inappropriate_type,
        .PIPE => .resource_vanished,
        .IO => .hardware_fault,
        .TIMEDOUT => .time_expired,
        else => if (matchesErrno("NOTSUP", err) or matchesErrno("OPNOTSUPP", err))
            .unsupported_operation
        else
            .other_error,
    };
}

fn decodeError(errnum: c_int, mapped_errnum: c_int, fname: ?*anyopaque) *anyopaque {
    const mapped: std.posix.E = @enumFromInt(mapped_errnum);
    const kind = classifyErrno(mapped);
    const details = if (kind == .other_error) mkUnknownDetails(errnum) else mkErrnoDetails(mapped_errnum);
    const code = errnoCode(errnum);

    return switch (kind) {
        .already_exists => withOptionalFilename(fname, code, details, io_error.lean_mk_io_error_already_exists, io_error.lean_mk_io_error_already_exists_file),
        .hardware_fault => io_error.lean_mk_io_error_hardware_fault(code, details),
        .inappropriate_type => withOptionalFilename(fname, code, details, io_error.lean_mk_io_error_inappropriate_type, io_error.lean_mk_io_error_inappropriate_type_file),
        .interrupted => withDirectFilename(fname, code, details, io_error.lean_mk_io_error_interrupted),
        .invalid_argument => withOptionalFilename(fname, code, details, io_error.lean_mk_io_error_invalid_argument, io_error.lean_mk_io_error_invalid_argument_file),
        .no_file_or_directory => withDirectFilename(fname, code, details, io_error.lean_mk_io_error_no_file_or_directory),
        .other_error => io_error.lean_mk_io_error_other_error(code, details),
        .permission_denied => withOptionalFilename(fname, code, details, io_error.lean_mk_io_error_permission_denied, io_error.lean_mk_io_error_permission_denied_file),
        .resource_busy => io_error.lean_mk_io_error_resource_busy(code, details),
        .resource_exhausted => withOptionalFilename(fname, code, details, io_error.lean_mk_io_error_resource_exhausted, io_error.lean_mk_io_error_resource_exhausted_file),
        .resource_vanished => io_error.lean_mk_io_error_resource_vanished(code, details),
        .time_expired => io_error.lean_mk_io_error_time_expired(code, details),
        .unsupported_operation => io_error.lean_mk_io_error_unsupported_operation(code, details),
    };
}

pub export fn lean_decode_io_error(errnum: c_int, fname: ?*anyopaque) callconv(.c) *anyopaque {
    return decodeError(errnum, errnum, fname);
}

pub export fn lean_decode_uv_error(errnum: c_int, fname: ?*anyopaque) callconv(.c) *anyopaque {
    const mapped_errnum = if (errnum < 0) -errnum else errnum;
    return decodeError(errnum, mapped_errnum, fname);
}

fn expectTag(result: *anyopaque, expected: u8) !void {
    try testing.expect(!object.lean_is_scalar(result));
    try testing.expectEqual(expected, object.lean_obj_tag(result));
}

test "lean_decode_io_error maps ENOENT to cpp tag" {
    const result = lean_decode_io_error(@intFromEnum(std.posix.E.NOENT), null);
    defer rc.lean_dec(result);

    try expectTag(result, 11);
}

test "lean_decode_io_error stores provided filename for permission errors" {
    const filename = string.mkAsciiStringBytes("secret.txt");
    const result = lean_decode_io_error(@intFromEnum(std.posix.E.ACCES), filename);
    defer rc.lean_dec(filename);
    defer rc.lean_dec(result);

    try expectTag(result, 13);
    try testing.expectEqual(@as(u8, 1), object.lean_obj_tag(ctor.lean_ctor_get(result, 0).?));
}

test "lean_decode_uv_error aliases negative errno values" {
    const from_uv = lean_decode_uv_error(-@as(c_int, @intFromEnum(std.posix.E.PIPE)), null);
    const from_io = lean_decode_io_error(@intFromEnum(std.posix.E.PIPE), null);
    defer rc.lean_dec(from_uv);
    defer rc.lean_dec(from_io);

    try testing.expectEqual(object.lean_obj_tag(from_io), object.lean_obj_tag(from_uv));
}

test "lean_decode_io_error falls back to other error for unknown errno" {
    const result = lean_decode_io_error(0xDEAD, null);
    defer rc.lean_dec(result);

    try expectTag(result, 1);
    const details = ctor.lean_ctor_get(result, 0).?;
    try testing.expect(std.mem.indexOf(u8, stringBytes(details), "57005") != null);
}

test "lean_decode_io_error result owns one reference" {
    initializeDecodeCache();
    alloc.resetTestCounters();
    for (0..100) |_| {
        const result = lean_decode_io_error(@intFromEnum(std.posix.E.NOENT), null);
        rc.lean_dec(result);
    }
    try testing.expectEqual(alloc.testAllocCount(), alloc.testFreeCount());
}
