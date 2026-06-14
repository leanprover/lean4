// Slice operations are implemented in `misc.zig` (`lean_slice_hash`, `lean_slice_dec_lt`).
// This file is intentionally empty and kept for future slice-related helpers.

const misc = @import("misc.zig");

test "slice module compiles" {
    _ = misc;
}
