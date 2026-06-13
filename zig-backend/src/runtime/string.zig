const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const utf8 = @import("utf8.zig");

fn asString(o: *anyopaque) *lean.lean_string_object {
    return @ptrCast(@alignCast(o));
}

fn stringCStr(o: *anyopaque) [*:0]const u8 {
    return @ptrCast(&asString(o).m_data);
}

fn stringData(o: *anyopaque) [*]const u8 {
    return @ptrCast(&asString(o).m_data);
}

fn stringDataMut(o: *anyopaque) [*]u8 {
    return @ptrCast(&asString(o).m_data);
}

fn stringSize(o: *anyopaque) usize {
    return asString(o).m_size;
}

fn stringLength(o: *anyopaque) usize {
    return asString(o).m_length;
}

fn stringEq(s1: *anyopaque, s2: *anyopaque) bool {
    return s1 == s2 or (stringSize(s1) == stringSize(s2) and lean_string_eq_cold(s1, s2));
}

fn stringDecEq(s1: *anyopaque, s2: *anyopaque) u8 {
    return @intFromBool(stringEq(s1, s2));
}

fn stringUtf8AtEnd(s: *anyopaque, i: ?*anyopaque) bool {
    return !object.lean_is_scalar(i) or object.lean_unbox(i) >= stringSize(s) - 1;
}

fn stringUtf8ByteSize(s: *anyopaque) ?*anyopaque {
    return object.lean_box(stringSize(s) - 1);
}

fn freeString(o: *anyopaque) void {
    rc.lean_dec(o);
}

fn checkedAdd(a: usize, b: usize) usize {
    const result = @addWithOverflow(a, b);
    if (result[1] != 0) @panic("integer overflow in string runtime");
    return result[0];
}

fn allocString(size: usize, capacity: usize, len: usize) *anyopaque {
    if (size == 0) @panic("Lean strings must include a trailing NUL");
    if (capacity < size) @panic("string capacity must cover string size");

    const total_size = checkedAdd(@sizeOf(lean.lean_string_object), capacity);
    const ptr = alloc.lean_alloc_object(total_size);
    const str = asString(ptr);
    str.m_header = .{
        .m_rc = 1,
        .m_cs_sz = 0,
        .m_other = 0,
        .m_tag = lean.LeanString,
    };
    str.m_size = size;
    str.m_capacity = capacity;
    str.m_length = len;
    return ptr;
}

fn mkStringUncheckedBytes(bytes: [*]const u8, sz: usize, len: usize) *anyopaque {
    const size = checkedAdd(sz, 1);
    const ptr = allocString(size, size, len);
    const dest = stringDataMut(ptr);
    @memcpy(dest[0..sz], bytes[0..sz]);
    dest[sz] = 0;
    return ptr;
}

pub fn mkAsciiStringBytes(bytes: []const u8) *anyopaque {
    return mkStringUncheckedBytes(bytes.ptr, bytes.len, bytes.len);
}

export fn lean_mk_string_unchecked(s: [*:0]const u8, sz: usize, len: usize) callconv(.c) *anyopaque {
    const bytes: [*]const u8 = @ptrCast(s);
    return mkStringUncheckedBytes(bytes, sz, len);
}

export fn lean_mk_string_from_bytes(s: [*:0]const u8, sz: usize) callconv(.c) *anyopaque {
    return lean_mk_string_from_bytes_unchecked(s, sz);
}

export fn lean_mk_string_from_bytes_unchecked(s: [*:0]const u8, sz: usize) callconv(.c) *anyopaque {
    return lean_mk_string_unchecked(s, sz, utf8.lean_utf8_n_strlen(s, sz));
}

export fn lean_mk_ascii_string_unchecked(s: [*:0]const u8) callconv(.c) *anyopaque {
    const sz = std.mem.len(s);
    return lean_mk_string_unchecked(s, sz, sz);
}

export fn lean_mk_string(s: [*:0]const u8) callconv(.c) *anyopaque {
    return lean_mk_string_from_bytes(s, std.mem.len(s));
}

export fn lean_string_push(s: *anyopaque, c: u32) callconv(.c) *anyopaque {
    var encoded: [4]u8 = undefined;
    const consumed = utf8.pushUnicodeScalar(&encoded, c);
    const old_size = stringSize(s);
    const new_size = checkedAdd(old_size, consumed);
    const result = allocString(new_size, new_size, checkedAdd(stringLength(s), 1));
    const dest = stringDataMut(result);
    const src = stringData(s);
    @memcpy(dest[0 .. old_size - 1], src[0 .. old_size - 1]);
    @memcpy(dest[old_size - 1 .. old_size - 1 + consumed], encoded[0..consumed]);
    dest[new_size - 1] = 0;
    rc.lean_dec(s);
    return result;
}

export fn lean_string_append(s1: *anyopaque, s2: *anyopaque) callconv(.c) *anyopaque {
    const size1 = stringSize(s1);
    const size2 = stringSize(s2);
    const new_size = checkedAdd(size1, size2 - 1);
    const result = allocString(new_size, new_size, checkedAdd(stringLength(s1), stringLength(s2)));
    const dest = stringDataMut(result);
    @memcpy(dest[0 .. size1 - 1], stringData(s1)[0 .. size1 - 1]);
    @memcpy(dest[size1 - 1 .. new_size], stringData(s2)[0..size2]);
    rc.lean_dec(s1);
    return result;
}

fn lean_string_mk(_cs: *anyopaque) callconv(.c) *anyopaque {
    _ = _cs;
    @panic("unimplemented: lean_string_mk");
}

fn lean_string_data(_s: *anyopaque) callconv(.c) *anyopaque {
    _ = _s;
    @panic("unimplemented: lean_string_data");
}

export fn lean_string_utf8_get(s: *anyopaque, i: *anyopaque) callconv(.c) u32 {
    if (!object.lean_is_scalar(i)) return 'A';
    const index = object.lean_unbox(i);
    const size = stringSize(s) - 1;
    if (index >= size) return 'A';
    return utf8.decodeAt(stringData(s), size, index) orelse 'A';
}

export fn lean_string_utf8_get_fast_cold(str: [*:0]const u8, i: usize, size: usize, c: u8) callconv(.c) u32 {
    _ = c;
    const bytes: [*]const u8 = @ptrCast(str);
    return utf8.decodeAt(bytes, size, i) orelse 'A';
}

export fn lean_string_utf8_next(s: *anyopaque, i: *anyopaque) callconv(.c) *anyopaque {
    if (!object.lean_is_scalar(i)) return object.lean_box(0).?;
    const index = object.lean_unbox(i);
    const size = stringSize(s) - 1;
    if (index >= size) return object.lean_box(index + 1).?;
    return object.lean_box(utf8.nextIndex(index, stringData(s)[index])).?;
}

export fn lean_string_utf8_next_fast_cold(i: usize, c: u8) callconv(.c) *anyopaque {
    return object.lean_box(utf8.nextIndex(i, c)).?;
}

export fn lean_string_utf8_prev(s: *anyopaque, i: *anyopaque) callconv(.c) *anyopaque {
    if (!object.lean_is_scalar(i)) return object.lean_box(0).?;
    const size = stringSize(s) - 1;
    var index = object.lean_unbox(i);
    if (index == 0) return object.lean_box(0).?;
    if (index > size) return object.lean_box(index - 1).?;

    index -= 1;
    const bytes = stringData(s);
    while (index > 0 and !utf8.isUtf8FirstByte(bytes[index])) {
        index -= 1;
    }
    return object.lean_box(index).?;
}

fn lean_string_utf8_set(_s: *anyopaque, _i: *anyopaque, _c: u32) callconv(.c) *anyopaque {
    _ = _s;
    _ = _i;
    _ = _c;
    @panic("unimplemented: lean_string_utf8_set");
}

fn lean_string_utf8_extract(_s: *anyopaque, _b: *anyopaque, _e: *anyopaque) callconv(.c) *anyopaque {
    _ = _s;
    _ = _b;
    _ = _e;
    @panic("unimplemented: lean_string_utf8_extract");
}

export fn lean_string_eq_cold(s1: *anyopaque, s2: *anyopaque) callconv(.c) bool {
    const size = stringSize(s1);
    if (size != stringSize(s2)) return false;
    return std.mem.eql(u8, stringData(s1)[0..size], stringData(s2)[0..size]);
}

export fn lean_string_lt(s1: *anyopaque, s2: *anyopaque) callconv(.c) bool {
    return std.mem.order(u8, stringData(s1)[0 .. stringSize(s1) - 1], stringData(s2)[0 .. stringSize(s2) - 1]) == .lt;
}

fn lean_string_hash(_arg0: *anyopaque) callconv(.c) u64 {
    _ = _arg0;
    @panic("unimplemented: lean_string_hash");
}

fn lean_string_of_usize(_arg0: usize) callconv(.c) *anyopaque {
    _ = _arg0;
    @panic("unimplemented: lean_string_of_usize");
}

fn lean_string_memcmp(_s1: *anyopaque, _s2: *anyopaque, _lstart: *anyopaque, _rstart: *anyopaque, _len: *anyopaque) callconv(.c) u8 {
    _ = _s1;
    _ = _s2;
    _ = _lstart;
    _ = _rstart;
    _ = _len;
    @panic("unimplemented: lean_string_memcmp");
}

test "lean_mk_string tracks ASCII byte size and UTF-8 length" {
    const s = lean_mk_string("hello, world");
    defer freeString(s);

    try testing.expectEqual(@as(c_uint, lean.LeanString), object.lean_obj_tag(s));
    try testing.expectEqual(@as(usize, 13), stringSize(s));
    try testing.expectEqual(@as(usize, 12), stringLength(s));
    try testing.expectEqualStrings("hello, world", std.mem.span(stringCStr(s)));
}

test "lean_mk_string and utf8 iterators handle non ASCII text" {
    const s = lean_mk_string("héllo");
    defer freeString(s);

    try testing.expectEqual(@as(usize, 7), stringSize(s));
    try testing.expectEqual(@as(usize, 5), stringLength(s));
    try testing.expectEqual(@as(u32, 'h'), lean_string_utf8_get(s, object.lean_box(0).?));
    try testing.expectEqual(@as(u32, 0xE9), lean_string_utf8_get(s, object.lean_box(1).?));
    try testing.expectEqual(@as(usize, 1), object.lean_unbox(lean_string_utf8_next(s, object.lean_box(0).?)));
    try testing.expectEqual(@as(usize, 3), object.lean_unbox(lean_string_utf8_next(s, object.lean_box(1).?)));
    try testing.expectEqual(@as(usize, 1), object.lean_unbox(lean_string_utf8_prev(s, object.lean_box(3).?)));
    try testing.expect(!stringUtf8AtEnd(s, object.lean_box(5)));
    try testing.expect(stringUtf8AtEnd(s, object.lean_box(6)));
    try testing.expectEqual(@as(usize, 6), object.lean_unbox(stringUtf8ByteSize(s)));
}

test "string equality ordering and append follow byte semantics" {
    const lhs = lean_mk_string("hé");
    const rhs = lean_mk_string("hé");
    const suffix = lean_mk_string("llo");
    const smaller = lean_mk_string("abc");
    const larger = lean_mk_string("abd");
    defer freeString(rhs);
    defer freeString(suffix);
    defer freeString(smaller);
    defer freeString(larger);

    try testing.expect(stringEq(lhs, rhs));
    try testing.expectEqual(@as(u8, 1), stringDecEq(lhs, rhs));
    try testing.expect(lean_string_lt(smaller, larger));

    const appended = lean_string_append(lhs, suffix);
    defer freeString(appended);

    try testing.expectEqual(@as(usize, 5), stringLength(appended));
    try testing.expectEqualStrings("héllo", std.mem.span(stringCStr(appended)));
}
