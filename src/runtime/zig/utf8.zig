const std = @import("std");
const testing = std.testing;

pub fn getUtf8Size(c: u8) usize {
    if ((c & 0x80) == 0) return 1;
    if ((c & 0xE0) == 0xC0) return 2;
    if ((c & 0xF0) == 0xE0) return 3;
    if ((c & 0xF8) == 0xF0) return 4;
    if ((c & 0xFC) == 0xF8) return 5;
    if ((c & 0xFE) == 0xFC) return 6;
    return 1;
}

pub fn isUtf8FirstByte(c: u8) bool {
    return (c & 0x80) == 0 or
        (c & 0xE0) == 0xC0 or
        (c & 0xF0) == 0xE0 or
        (c & 0xF8) == 0xF0;
}

pub fn validateUtf8One(str: [*]const u8, size: usize, pos: *usize) bool {
    const c = str[pos.*];
    if ((c & 0x80) == 0) {
        pos.* += 1;
        return true;
    }

    if ((c & 0xE0) == 0xC0) {
        if (pos.* + 1 >= size) return false;
        const c1 = str[pos.* + 1];
        if ((c1 & 0xC0) != 0x80) return false;
        const r: u32 = ((@as(u32, c) & 0x1F) << 6) | (@as(u32, c1) & 0x3F);
        if (r < 0x80) return false;
        pos.* += 2;
        return true;
    }

    if ((c & 0xF0) == 0xE0) {
        if (pos.* + 2 >= size) return false;
        const c1 = str[pos.* + 1];
        const c2 = str[pos.* + 2];
        if ((c1 & 0xC0) != 0x80 or (c2 & 0xC0) != 0x80) return false;
        const r: u32 = ((@as(u32, c) & 0x0F) << 12) |
            ((@as(u32, c1) & 0x3F) << 6) |
            (@as(u32, c2) & 0x3F);
        if (r < 0x800 or (r >= 0xD800 and r <= 0xDFFF)) return false;
        pos.* += 3;
        return true;
    }

    if ((c & 0xF8) == 0xF0) {
        if (pos.* + 3 >= size) return false;
        const c1 = str[pos.* + 1];
        const c2 = str[pos.* + 2];
        const c3 = str[pos.* + 3];
        if ((c1 & 0xC0) != 0x80 or (c2 & 0xC0) != 0x80 or (c3 & 0xC0) != 0x80) return false;
        const r: u32 = ((@as(u32, c) & 0x07) << 18) |
            ((@as(u32, c1) & 0x3F) << 12) |
            ((@as(u32, c2) & 0x3F) << 6) |
            (@as(u32, c3) & 0x3F);
        if (r < 0x10000 or r > 0x10FFFF) return false;
        pos.* += 4;
        return true;
    }

    return false;
}

pub fn validateUtf8(str: [*]const u8, size: usize, pos: *usize, codepoints: *usize) bool {
    while (pos.* < size) {
        if (!validateUtf8One(str, size, pos)) return false;
        codepoints.* += 1;
    }
    return true;
}

pub fn decodeAt(str: [*]const u8, size: usize, i: usize) ?u32 {
    if (i >= size) return null;
    const c = str[i];
    if ((c & 0x80) == 0) return c;

    if ((c & 0xE0) == 0xC0 and i + 1 < size) {
        const c1 = str[i + 1];
        const r: u32 = ((@as(u32, c) & 0x1F) << 6) | (@as(u32, c1) & 0x3F);
        if (r >= 0x80) return r;
    }

    if ((c & 0xF0) == 0xE0 and i + 2 < size) {
        const c1 = str[i + 1];
        const c2 = str[i + 2];
        const r: u32 = ((@as(u32, c) & 0x0F) << 12) |
            ((@as(u32, c1) & 0x3F) << 6) |
            (@as(u32, c2) & 0x3F);
        if (r >= 0x800 and (r < 0xD800 or r > 0xDFFF)) return r;
    }

    if ((c & 0xF8) == 0xF0 and i + 3 < size) {
        const c1 = str[i + 1];
        const c2 = str[i + 2];
        const c3 = str[i + 3];
        const r: u32 = ((@as(u32, c) & 0x07) << 18) |
            ((@as(u32, c1) & 0x3F) << 12) |
            ((@as(u32, c2) & 0x3F) << 6) |
            (@as(u32, c3) & 0x3F);
        if (r >= 0x10000 and r <= 0x10FFFF) return r;
    }

    return null;
}

pub fn nextIndex(i: usize, c: u8) usize {
    if ((c & 0x80) == 0) return i + 1;
    if ((c & 0xE0) == 0xC0) return i + 2;
    if ((c & 0xF0) == 0xE0) return i + 3;
    if ((c & 0xF8) == 0xF0) return i + 4;
    return i + 1;
}

pub fn prevIndex(str: [*]const u8, pos: usize) usize {
    var i = pos;
    while (i > 0) {
        i -= 1;
        if (isUtf8FirstByte(str[i])) return i;
    }
    return 0;
}


pub fn pushUnicodeScalar(dest: [*]u8, code: u32) usize {
    if (code < 0x80) {
        dest[0] = @intCast(code);
        return 1;
    }
    if (code < 0x800) {
        dest[0] = @intCast((code >> 6) & 0x1F | 0xC0);
        dest[1] = @intCast((code & 0x3F) | 0x80);
        return 2;
    }
    if (code < 0x10000) {
        dest[0] = @intCast((code >> 12) & 0x0F | 0xE0);
        dest[1] = @intCast((code >> 6) & 0x3F | 0x80);
        dest[2] = @intCast((code & 0x3F) | 0x80);
        return 3;
    }

    dest[0] = @intCast((code >> 18) & 0x07 | 0xF0);
    dest[1] = @intCast((code >> 12) & 0x3F | 0x80);
    dest[2] = @intCast((code >> 6) & 0x3F | 0x80);
    dest[3] = @intCast((code & 0x3F) | 0x80);
    return 4;
}

pub export fn lean_utf8_strlen(str: [*:0]const u8) callconv(.c) usize {
    var i: usize = 0;
    var count: usize = 0;
    while (str[i] != 0) {
        i += getUtf8Size(str[i]);
        count += 1;
    }
    return count;
}

pub export fn lean_utf8_n_strlen(str: [*:0]const u8, n: usize) callconv(.c) usize {
    var i: usize = 0;
    var count: usize = 0;
    while (i < n) {
        i += getUtf8Size(str[i]);
        count += 1;
    }
    return count;
}

test "utf8 strlen counts ASCII and multibyte codepoints" {
    try testing.expectEqual(@as(usize, 12), lean_utf8_strlen("hello, world"));
    try testing.expectEqual(@as(usize, 5), lean_utf8_strlen("héllo"));
    try testing.expectEqual(@as(usize, 1), lean_utf8_strlen("🙂"));
}

test "utf8 n strlen uses byte length rather than sentinel" {
    const s = "héllo";
    try testing.expectEqual(@as(usize, 5), lean_utf8_n_strlen(s, 6));
    try testing.expectEqual(@as(usize, 2), lean_utf8_n_strlen(s, 3));
}
