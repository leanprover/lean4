const std = @import("std");

// Paths are relative to the zig-backend root; the build system runs this
// binary with that directory as cwd.
const golden_path = "tests/scheduler-smoke/reference/golden.json";
const reference_bin = "tests/scheduler-smoke/reference/scheduler_cpp";
const post_bin = ".zig-cache/scheduler_zig";
const results_path = "tests/scheduler-smoke/results.json";

const TaggedAllocBalance = struct {
    alloc: usize,
    free: usize,
    net: i64,
};

const Snapshot = struct {
    seed: u64,
    rc_total: u64,
    dep_shape_hash: u64,
    sync_prio_order: [4]u32,
    tagged_alloc_balance: TaggedAllocBalance,
};

const RunResult = struct {
    snapshot: Snapshot,
    wall_ms: u64,
};

fn wallClockNanos() u64 {
    var tv: std.c.timeval = undefined;
    if (std.c.gettimeofday(&tv, null) != 0) @panic("gettimeofday failed");
    return @as(u64, @intCast(tv.sec)) * std.time.ns_per_s +
        @as(u64, @intCast(tv.usec)) * std.time.ns_per_us;
}

fn readSnapshot(gpa: std.mem.Allocator, io: std.Io, path: []const u8) !Snapshot {
    var buf: [2048]u8 = undefined;
    const json_bytes = try std.Io.Dir.cwd().readFile(io, path, &buf);
    const parsed = try std.json.parseFromSlice(Snapshot, gpa, json_bytes, .{});
    defer parsed.deinit();
    return parsed.value;
}

fn checkExitedOk(term: std.process.Child.Term, stderr: []const u8) !void {
    switch (term) {
        .exited => |code| {
            if (code == 0) return;
            std.debug.print("{s}", .{stderr});
            return error.ChildExitedNonZero;
        },
        .signal => |sig| {
            std.debug.print("child terminated by signal {any}\n{s}", .{ sig, stderr });
            return error.ChildExitedNonZero;
        },
        .stopped => |sig| {
            std.debug.print("child stopped by signal {any}\n{s}", .{ sig, stderr });
            return error.ChildExitedNonZero;
        },
        .unknown => |value| {
            std.debug.print("child terminated unexpectedly ({d})\n{s}", .{ value, stderr });
            return error.ChildExitedNonZero;
        },
    }
}

fn runSnapshotBinary(gpa: std.mem.Allocator, io: std.Io, path: []const u8) !RunResult {
    const started = wallClockNanos();
    const result = try std.process.run(gpa, io, .{
        .argv = &.{path},
        .cwd = .{ .path = repo_root },
        .stdout_limit = .limited(4096),
        .stderr_limit = .limited(4096),
    });
    defer gpa.free(result.stdout);
    defer gpa.free(result.stderr);
    const elapsed = wallClockNanos() - started;

    try checkExitedOk(result.term, result.stderr);
    if (result.stderr.len != 0) {
        std.debug.print("{s}", .{result.stderr});
    }

    const parsed = try std.json.parseFromSlice(Snapshot, gpa, result.stdout, .{});
    defer parsed.deinit();
    return .{
        .snapshot = parsed.value,
        .wall_ms = elapsed / std.time.ns_per_ms,
    };
}

fn expectArrayEqual(actual: [4]u32, expected: [4]u32, label: []const u8) !void {
    if (!std.mem.eql(u32, &actual, &expected)) {
        std.debug.print(
            "{s} mismatch: expected [{d}, {d}, {d}, {d}] got [{d}, {d}, {d}, {d}]\n",
            .{
                label,
                expected[0],
                expected[1],
                expected[2],
                expected[3],
                actual[0],
                actual[1],
                actual[2],
                actual[3],
            },
        );
        return error.SnapshotMismatch;
    }
}

fn expectSnapshotMatches(actual: Snapshot, expected: Snapshot, label: []const u8, comptime require_alloc_counts: bool) !void {
    if (actual.seed != expected.seed) return error.SnapshotMismatch;
    if (actual.rc_total != expected.rc_total) return error.SnapshotMismatch;
    if (actual.dep_shape_hash != expected.dep_shape_hash) return error.SnapshotMismatch;
    try expectArrayEqual(actual.sync_prio_order, expected.sync_prio_order, label);
    if (actual.tagged_alloc_balance.net != expected.tagged_alloc_balance.net) return error.SnapshotMismatch;
    if (require_alloc_counts) {
        if (actual.tagged_alloc_balance.alloc != expected.tagged_alloc_balance.alloc) return error.SnapshotMismatch;
        if (actual.tagged_alloc_balance.free != expected.tagged_alloc_balance.free) return error.SnapshotMismatch;
    }
}

fn writeResults(io: std.Io, golden: Snapshot, reference: RunResult, post: RunResult) !void {
    const json = try std.fmt.allocPrint(std.heap.page_allocator,
        \\{{
        \\  "golden": {{
        \\    "seed": {d},
        \\    "rc_total": {d},
        \\    "dep_shape_hash": {d},
        \\    "sync_prio_order": [{d}, {d}, {d}, {d}],
        \\    "tagged_alloc_balance": {{
        \\      "alloc": {d},
        \\      "free": {d},
        \\      "net": {d}
        \\    }}
        \\  }},
        \\  "reference": {{
        \\    "wall_ms": {d},
        \\    "snapshot": {{
        \\      "seed": {d},
        \\      "rc_total": {d},
        \\      "dep_shape_hash": {d},
        \\      "sync_prio_order": [{d}, {d}, {d}, {d}],
        \\      "tagged_alloc_balance": {{
        \\        "alloc": {d},
        \\        "free": {d},
        \\        "net": {d}
        \\      }}
        \\    }}
        \\  }},
        \\  "post_swap": {{
        \\    "wall_ms": {d},
        \\    "snapshot": {{
        \\      "seed": {d},
        \\      "rc_total": {d},
        \\      "dep_shape_hash": {d},
        \\      "sync_prio_order": [{d}, {d}, {d}, {d}],
        \\      "tagged_alloc_balance": {{
        \\        "alloc": {d},
        \\        "free": {d},
        \\        "net": {d}
        \\      }}
        \\    }}
        \\  }},
        \\  "mismatches": 0
        \\}}
    , .{
        golden.seed,
        golden.rc_total,
        golden.dep_shape_hash,
        golden.sync_prio_order[0],
        golden.sync_prio_order[1],
        golden.sync_prio_order[2],
        golden.sync_prio_order[3],
        golden.tagged_alloc_balance.alloc,
        golden.tagged_alloc_balance.free,
        golden.tagged_alloc_balance.net,
        reference.wall_ms,
        reference.snapshot.seed,
        reference.snapshot.rc_total,
        reference.snapshot.dep_shape_hash,
        reference.snapshot.sync_prio_order[0],
        reference.snapshot.sync_prio_order[1],
        reference.snapshot.sync_prio_order[2],
        reference.snapshot.sync_prio_order[3],
        reference.snapshot.tagged_alloc_balance.alloc,
        reference.snapshot.tagged_alloc_balance.free,
        reference.snapshot.tagged_alloc_balance.net,
        post.wall_ms,
        post.snapshot.seed,
        post.snapshot.rc_total,
        post.snapshot.dep_shape_hash,
        post.snapshot.sync_prio_order[0],
        post.snapshot.sync_prio_order[1],
        post.snapshot.sync_prio_order[2],
        post.snapshot.sync_prio_order[3],
        post.snapshot.tagged_alloc_balance.alloc,
        post.snapshot.tagged_alloc_balance.free,
        post.snapshot.tagged_alloc_balance.net,
    });
    defer std.heap.page_allocator.free(json);

    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = results_path,
        .data = json,
    });
}

pub fn main() !void {
    var gpa_state: std.heap.DebugAllocator(.{}) = .init;
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    var threaded: std.Io.Threaded = .init(gpa, .{});
    defer threaded.deinit();
    const io = threaded.io();

    const golden = try readSnapshot(gpa, io, golden_path);
    const reference = try runSnapshotBinary(gpa, io, reference_bin);
    const post = try runSnapshotBinary(gpa, io, post_bin);

    try expectSnapshotMatches(reference.snapshot, golden, "reference", true);
    try expectSnapshotMatches(post.snapshot, golden, "post", false);
    try expectSnapshotMatches(post.snapshot, reference.snapshot, "differential", false);

    if (post.snapshot.tagged_alloc_balance.net != 0) return error.LeakDetected;
    if (post.wall_ms >= 30_000) return error.TimeoutExceeded;

    try writeResults(io, golden, reference, post);
    std.debug.print(
        "scheduler-diff: rc_total={d} dep_shape_hash={d} post_wall_ms={d} mismatches=0 leaks=0\n",
        .{ post.snapshot.rc_total, post.snapshot.dep_shape_hash, post.wall_ms },
    );
}
