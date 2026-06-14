const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const mpz_mod = b.addModule("mpz_zig", .{
        .root_source_file = b.path("mpz_zig.zig"),
    });
    const opts_mod = b.addModule("runtime_options", .{
        .root_source_file = b.path("runtime_options.zig"),
    });

    const root_mod = b.createModule(.{
        .root_source_file = b.path("root.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    root_mod.addImport("mpz_zig", mpz_mod);
    root_mod.addImport("runtime_options", opts_mod);
    root_mod.linkSystemLibrary("gmp", .{});

    const lib = b.addLibrary(.{
        .name = "leanrt_zig",
        .root_module = root_mod,
        .linkage = .static,
    });
    b.installArtifact(lib);

    const tests = b.addTest(.{
        .root_module = root_mod,
    });

    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_tests.step);
}
