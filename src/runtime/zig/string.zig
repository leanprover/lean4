const std = @import("std");
const testing = std.testing;
const alloc = @import("alloc.zig");
const lean = @import("lean_object.zig");
const object = @import("object.zig");
const rc = @import("rc.zig");
const utf8 = @import("utf8.zig");
const ctor = @import("ctor.zig");

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

fn lean_string_mk(cs: *anyopaque) callconv(.c) *anyopaque {
    var bytes: std.ArrayListUnmanaged(u8) = .empty;
    defer bytes.deinit(std.heap.page_allocator);
    var len: usize = 0;
    var it: ?*anyopaque = cs;
    while (it) |node| {
        if (object.lean_is_scalar(node)) break;
        const c = @as(u32, @truncate(object.lean_unbox(ctor.lean_ctor_get(node, 0))));
        var buf: [4]u8 = undefined;
        const n = utf8.pushUnicodeScalar(&buf, c);
        bytes.appendSlice(std.heap.page_allocator, buf[0..n]) catch @panic("lean_string_mk: out of memory");
        len += 1;
        it = ctor.lean_ctor_get(node, 1);
    }
    rc.lean_dec(cs);
    const result = allocString(bytes.items.len + 1, bytes.items.len + 1, len);
    const dest = stringDataMut(result);
    @memcpy(dest[0..bytes.items.len], bytes.items);
    dest[bytes.items.len] = 0;
    return result;
}

fn lean_string_data(s: *anyopaque) callconv(.c) *anyopaque {
    const bytes = stringData(s);
    const size = stringSize(s) - 1;
    var result: ?*anyopaque = object.lean_box(0).?;
    var pos: usize = size;
    while (pos > 0) {
        const prev = utf8.prevIndex(bytes, pos);
        const code = utf8.decodeAt(bytes, size, prev) orelse 0xFFFD;
        const cell = alloc.lean_alloc_ctor(1, 2, 0);
        ctor.lean_ctor_set(cell, 0, object.lean_box(@as(usize, code)));
        ctor.lean_ctor_set(cell, 1, result);
        result = cell;
        pos = prev;
    }
    rc.lean_dec(s);
    return result.?;
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

fn lean_string_utf8_set(s: *anyopaque, idx_arg: *anyopaque, c: u32) callconv(.c) *anyopaque {
    if (!object.lean_is_scalar(idx_arg)) return s;
    const i = object.lean_unbox(idx_arg);
    const sz = stringSize(s) - 1;
    if (i >= sz) return s;
    const bytes = stringData(s);
    if (!utf8.isUtf8FirstByte(bytes[i])) return s;

    const old_size = utf8.getUtf8Size(bytes[i]);
    var new_encoded: [4]u8 = undefined;
    const new_size = utf8.pushUnicodeScalar(&new_encoded, c);
    const new_total = (sz - old_size) + new_size;

    const result = allocString(new_total + 1, new_total + 1, stringLength(s));
    const dest = stringDataMut(result);
    @memcpy(dest[0..i], bytes[0..i]);
    @memcpy(dest[i..i + new_size], new_encoded[0..new_size]);
    @memcpy(dest[i + new_size .. new_total], bytes[i + old_size .. sz]);
    dest[new_total] = 0;
    rc.lean_dec(s);
    return result;
}

fn lean_string_utf8_extract(s: *anyopaque, b0: *anyopaque, e0: *anyopaque) callconv(.c) *anyopaque {
    if (!object.lean_is_scalar(b0) or !object.lean_is_scalar(e0)) return s;
    const b_in = object.lean_unbox(b0);
    const e_in = object.lean_unbox(e0);
    const bytes = stringData(s);
    const sz = stringSize(s) - 1;
    if (b_in >= e_in or b_in >= sz) {
        rc.lean_dec(s);
        return mkStringUncheckedBytes("", 0, 0);
    }
    if (!utf8.isUtf8FirstByte(bytes[b_in])) {
        rc.lean_dec(s);
        return mkStringUncheckedBytes("", 0, 0);
    }
    const b = b_in;
    const e = if (e_in > sz) sz else (if (e_in < sz and !utf8.isUtf8FirstByte(bytes[e_in])) sz else e_in);
    const new_sz = e - b;
    var len: usize = 0;
    var pos = b;
    while (pos < e) : (len += 1) {
        pos += utf8.getUtf8Size(bytes[pos]);
    }
    const result = allocString(new_sz + 1, new_sz + 1, len);
    const dest = stringDataMut(result);
    @memcpy(dest[0..new_sz], bytes[b..e]);
    dest[new_sz] = 0;
    rc.lean_dec(s);
    return result;
}

export fn lean_string_eq_cold(s1: *anyopaque, s2: *anyopaque) callconv(.c) bool {
    const size = stringSize(s1);
    if (size != stringSize(s2)) return false;
    return std.mem.eql(u8, stringData(s1)[0..size], stringData(s2)[0..size]);
}

export fn lean_string_lt(s1: *anyopaque, s2: *anyopaque) callconv(.c) bool {
    return std.mem.order(u8, stringData(s1)[0 .. stringSize(s1) - 1], stringData(s2)[0 .. stringSize(s2) - 1]) == .lt;
}

fn lean_string_hash(s: *anyopaque) callconv(.c) u64 {
    const sz = stringSize(s) - 1;
    const bytes = stringData(s)[0..sz];
    return hashBytes(bytes, 11);
}

fn lean_string_of_usize(n: usize) callconv(.c) *anyopaque {
    var buf: [32]u8 = undefined;
    const str = std.fmt.bufPrint(&buf, "{}", .{n}) catch @panic("lean_string_of_usize overflow");
    return mkAsciiStringBytes(str);
}

fn hashBytes(bytes: []const u8, seed: u64) u64 {
    const m: u64 = 0xc6a4a7935bd1e995;
    const r = 47;
    var h: u64 = seed ^ (bytes.len *% m);

    var i: usize = 0;
    while (i + 8 <= bytes.len) : (i += 8) {
        var k: u64 = 0;
        @memcpy(std.mem.asBytes(&k), bytes[i..][0..8]);
        k *%= m;
        k ^= k >> r;
        k *%= m;
        h ^= k;
        h *%= m;
    }

    const rem = bytes.len & 7;
    if (rem >= 7) h ^= @as(u64, bytes[i + 6]) << 48;
    if (rem >= 6) h ^= @as(u64, bytes[i + 5]) << 40;
    if (rem >= 5) h ^= @as(u64, bytes[i + 4]) << 32;
    if (rem >= 4) h ^= @as(u64, bytes[i + 3]) << 24;
    if (rem >= 3) h ^= @as(u64, bytes[i + 2]) << 16;
    if (rem >= 2) h ^= @as(u64, bytes[i + 1]) << 8;
    if (rem >= 1) {
        h ^= @as(u64, bytes[i]);
        h *%= m;
    }

    h ^= h >> r;
    h *%= m;
    h ^= h >> r;
    return h;
}

fn lean_string_memcmp(s1: *anyopaque, s2: *anyopaque, lstart: *anyopaque, rstart: *anyopaque, len: *anyopaque) callconv(.c) u8 {
    const lbase = stringData(s1) + object.lean_unbox(lstart);
    const rbase = stringData(s2) + object.lean_unbox(rstart);
    const n = object.lean_unbox(len);
    return @intFromBool(std.mem.eql(u8, lbase[0..n], rbase[0..n]));
}

test "string mk builds string from List Char" {
    const nil = object.lean_box(0).?;
    var list: ?*anyopaque = nil;
    const chars = [_]u32{ 'h', 0xE9, 'l', 'l', 'o' };
    var i: usize = chars.len;
    while (i > 0) {
        i -= 1;
        const cell = alloc.lean_alloc_ctor(1, 2, 0);
        ctor.lean_ctor_set(cell, 0, object.lean_box(@as(usize, chars[i])));
        ctor.lean_ctor_set(cell, 1, list);
        list = cell;
    }

    const s = lean_string_mk(list.?);
    defer freeString(s);

    try testing.expectEqual(@as(usize, 7), stringSize(s));
    try testing.expectEqual(@as(usize, 5), stringLength(s));
    try testing.expectEqualStrings("héllo", std.mem.span(stringCStr(s)));
}

test "string data builds List Char from string" {
    const s = lean_mk_string("héllo");
    defer freeString(s);

    const list = lean_string_data(s);
    defer {
        var it: ?*anyopaque = list;
        while (it) |node| {
            if (object.lean_is_scalar(node)) break;
            const next = ctor.lean_ctor_get(node, 1);
            rc.lean_dec(node);
            it = next;
        }
    }

    const expected = [_]u32{ 'h', 0xE9, 'l', 'l', 'o' };
    var it: ?*anyopaque = list;
    var idx: usize = 0;
    while (it) |node| {
        if (object.lean_is_scalar(node)) break;
        try testing.expectEqual(@as(u32, @truncate(object.lean_unbox(ctor.lean_ctor_get(node, 0)))), expected[idx]);
        it = ctor.lean_ctor_get(node, 1);
        idx += 1;
    }
    try testing.expectEqual(expected.len, idx);
}

test "string hash matches C++ MurmurHash64A" {
    const cases = [_]struct { s: []const u8, h: u64 }{
        .{ .s = "", .h = 0x89133354f2041b41 },
        .{ .s = "a", .h = 0xdce594566b8c31f5 },
        .{ .s = "hello", .h = 0x884e46be8ed9fafd },
        .{ .s = "hello, world", .h = 0xd7a3f3d09f66d43e },
        .{ .s = "héllo", .h = 0xfb983514f98ab9e4 },
    };
    for (cases) |c| {
        const s = lean_mk_string_unchecked(@ptrCast(c.s.ptr), c.s.len, c.s.len);
        defer freeString(s);
        try testing.expectEqual(c.h, lean_string_hash(s));
    }
}

test "string of usize" {
    const s = lean_string_of_usize(12345);
    defer freeString(s);
    try testing.expectEqualStrings("12345", std.mem.span(stringCStr(s)));
    try testing.expectEqual(@as(usize, 6), stringSize(s));
}

test "string memcmp compares slices" {
    const s1 = lean_mk_string("hello, world");
    defer freeString(s1);
    const s2 = lean_mk_string("hello, world");
    defer freeString(s2);
    const s3 = lean_mk_string("hello, earth");
    defer freeString(s3);
    try testing.expectEqual(@as(u8, 1), lean_string_memcmp(s1, s2, object.lean_box(0).?, object.lean_box(0).?, object.lean_box(12).?));
    try testing.expectEqual(@as(u8, 0), lean_string_memcmp(s1, s3, object.lean_box(0).?, object.lean_box(0).?, object.lean_box(12).?));
    try testing.expectEqual(@as(u8, 1), lean_string_memcmp(s1, s2, object.lean_box(7).?, object.lean_box(7).?, object.lean_box(5).?));
}

test "string utf8 set replaces codepoint" {
    const s = lean_mk_string("héllo");
    defer freeString(s);
    const replaced = lean_string_utf8_set(s, object.lean_box(1).?, 'a');
    defer freeString(replaced);
    try testing.expectEqual(@as(usize, 6), stringSize(replaced));
    try testing.expectEqualStrings("hallo", std.mem.span(stringCStr(replaced)));
}

test "string utf8 extract slices by byte positions" {
    const s = lean_mk_string("héllo");
    defer freeString(s);
    const extracted = lean_string_utf8_extract(s, object.lean_box(0).?, object.lean_box(4).?);
    defer freeString(extracted);
    try testing.expectEqual(@as(usize, 5), stringSize(extracted));
    try testing.expectEqualStrings("hél", std.mem.span(stringCStr(extracted)));
}

test "lean_mk_string tracks ASCII byte size and UTF-8 length" {
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
