const std = @import("std");

/// Resolve a configurable path: `-D<name>=` build option first, then the
/// `<env_name>` environment variable, then the given default.
fn pathOption(
    b: *std.Build,
    name: []const u8,
    env_name: []const u8,
    description: []const u8,
    default: []const u8,
) []const u8 {
    if (b.option([]const u8, name, description)) |value| return value;
    if (b.graph.environ_map.get(env_name)) |value| return b.dupe(value);
    return default;
}

fn createRuntimeModule(
    b: *std.Build,
    root_source: []const u8,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    export_allocator_symbols: bool,
) *std.Build.Module {
    const runtime_options = b.addOptions();
    runtime_options.addOption(bool, "export_allocator_symbols", export_allocator_symbols);

    const module = b.createModule(.{
        .root_source_file = b.path(root_source),
        .target = target,
        .optimize = optimize,
    });
    module.link_libc = true;
    module.addIncludePath(b.path("include"));
    module.addImport("runtime_options", runtime_options.createModule());
    module.addImport("mpz_zig", b.createModule(.{
        .root_source_file = b.path("src/mpz_zig.zig"),
        .target = target,
        .optimize = optimize,
    }));
    return module;
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const install_step = b.getInstallStep();
    const lean4_dir = pathOption(
        b,
        "lean4-dir",
        "LEAN4_DIR",
        "Path to the lean4 repository root (default: parent of zig-backend)",
        b.pathResolve(&.{ b.build_root.path orelse ".", ".." }),
    );
    const gmp_prefix = pathOption(
        b,
        "gmp-prefix",
        "GMP_PREFIX",
        "GMP installation prefix",
        "/opt/homebrew/opt/gmp",
    );
    const libuv_prefix = pathOption(
        b,
        "libuv-prefix",
        "LIBUV_PREFIX",
        "libuv installation prefix",
        "/opt/homebrew/opt/libuv",
    );
    const lean_src = b.pathJoin(&.{ lean4_dir, "src" });
    const lean_include = b.pathJoin(&.{ lean4_dir, "src", "include" });
    const lean_stage1_include = b.pathJoin(&.{ lean4_dir, "build", "release", "stage1", "include" });
    const lean_stage1_lib = b.pathJoin(&.{ lean4_dir, "build", "release", "stage1", "lib", "lean" });
    const gmp_include = b.pathJoin(&.{ gmp_prefix, "include" });
    const gmp_lib = b.pathJoin(&.{ gmp_prefix, "lib" });
    const libuv_lib = b.pathJoin(&.{ libuv_prefix, "lib" });

    const lib = b.addLibrary(.{
        .linkage = .static,
        .name = "leanrt-zig",
        .root_module = createRuntimeModule(
            b,
            "src/runtime/root.zig",
            target,
            optimize,
            true,
        ),
    });
    lib.root_module.addCSourceFile(.{
        .file = b.path("src/runtime/box_weak_exports.c"),
    });
    lib.root_module.addCSourceFile(.{
        .file = b.path("src/runtime/io_error_weak_exports.c"),
    });

    b.installArtifact(lib);

    const abi_lib = b.addLibrary(.{
        .linkage = .static,
        .name = "leanrt-zig-testabi",
        .root_module = createRuntimeModule(
            b,
            "src/runtime/root.zig",
            target,
            optimize,
            true,
        ),
    });
    abi_lib.root_module.addCSourceFile(.{
        .file = b.path("src/runtime/box_weak_exports.c"),
    });
    abi_lib.root_module.addCSourceFile(.{
        .file = b.path("src/runtime/io_error_weak_exports.c"),
    });
    abi_lib.root_module.addCSourceFile(.{
        .file = b.path("src/runtime/testabi_hidden_shims.c"),
    });

    b.installArtifact(abi_lib);

    const cmake_configure = b.addSystemCommand(&.{"cmake"});
    cmake_configure.setCwd(b.path("."));
    cmake_configure.addArgs(&.{
        "-S",
        "cmake/leanrt_cpp_partial",
        "-B",
        ".zig-cache/leanrt_cpp_partial",
        "-DCMAKE_BUILD_TYPE=Release",
        b.fmt("-DLEAN4_DIR={s}", .{lean4_dir}),
        b.fmt("-DGMP_PREFIX={s}", .{gmp_prefix}),
        b.fmt("-DLIBUV_PREFIX={s}", .{libuv_prefix}),
    });

    const cmake_build = b.addSystemCommand(&.{"cmake"});
    cmake_build.setCwd(b.path("."));
    cmake_build.addArgs(&.{
        "--build",
        ".zig-cache/leanrt_cpp_partial",
        "--target",
        "leanrt_cpp_partial",
        "--config",
        "Release",
    });
    cmake_build.step.dependOn(&cmake_configure.step);

    const install_cpp_partial = b.addInstallFileWithDir(
        b.path(".zig-cache/leanrt_cpp_partial/libleanrt_cpp_partial.a"),
        .lib,
        "libleanrt_cpp_partial.a",
    );
    install_cpp_partial.step.dependOn(&cmake_build.step);
    install_step.dependOn(&install_cpp_partial.step);

    const cpp_partial_step = b.step(
        "cpp-partial",
        "Build and install the delegated C++ runtime archive",
    );
    cpp_partial_step.dependOn(&install_cpp_partial.step);

    // Unit tests for runtime modules
    const test_step = b.step("test", "Run Zig unit tests for runtime modules");

    const runtime_modules = &[_][]const u8{
        "mpz_zig",
        "object",
        "alloc",
        "rc",
        "apply",
        "box",
        "ctor",
        "dbg",
        "string",
        "utf8",
        "array",
        "io_error",
        "io_errno",
        "io_result",
        "io_min",
        "init",
        "task",
        "task_manager",
        "task_manager_export",
        "misc",
        "nat_constructors",
        "nat_arithmetic",
        "nat",
        "int",
        "uint",
        "int_conv",
        "float",
        "debug",
        "st",
        "st_ref",
        "sync",
        "thread",
        "thunk",
        "once",
        "mpz_object",
    };

    for (runtime_modules) |mod| {
        const mod_test = b.addTest(.{
            .root_module = createRuntimeModule(
                b,
                if (std.mem.eql(u8, mod, "mpz_zig"))
                    "src/mpz_zig.zig"
                else
                    b.fmt("src/runtime/{s}.zig", .{mod}),
                target,
                optimize,
                true,
            ),
        });
        if (std.mem.eql(u8, mod, "mpz_zig")) {
            mod_test.root_module.addCSourceFile(.{
                .file = b.path("tests/gmp_oracle.c"),
            });
            mod_test.root_module.addIncludePath(.{ .cwd_relative = gmp_include });
            mod_test.root_module.addLibraryPath(.{ .cwd_relative = gmp_lib });
            mod_test.root_module.linkSystemLibrary("gmp", .{ .use_pkg_config = .no });
        }
        const run_mod_test = b.addRunArtifact(mod_test);
        test_step.dependOn(&run_mod_test.step);
    }

    const AbiSmokeTest = struct {
        name: []const u8,
        source: []const u8,
        use_split_runtime: bool = false,
        support_cpp: ?[]const u8 = null,
        extra_support_cpp: ?[]const u8 = null,
        needs_gmp: bool = false,
        needs_stage1_libs: bool = true,
        expect_nonzero: bool = false,
        stderr_contains: ?[]const u8 = null,
    };

    const abi_smoke_tests = [_]AbiSmokeTest{
        .{
            .name = "layout",
            .source = "tests/abi-smoke/layout.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_pool_shape",
            .source = "tests/abi-smoke/task_pool_shape.c",
            .support_cpp = "tests/abi-smoke/task_pool_shape_support.cpp",
        },
        .{
            .name = "rc",
            .source = "tests/abi-smoke/rc.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "closure",
            .source = "tests/abi-smoke/closure.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "strings",
            .source = "tests/abi-smoke/strings.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "arrays",
            .source = "tests/abi-smoke/arrays.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "ctor",
            .source = "tests/abi-smoke/ctor.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "box",
            .source = "tests/abi-smoke/box.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "thunk",
            .source = "tests/abi-smoke/thunk.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_pure",
            .source = "tests/abi-smoke/task_pure.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_alloc",
            .source = "tests/abi-smoke/task_alloc.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_rc",
            .source = "tests/abi-smoke/task_rc.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_spawn_rc",
            .source = "tests/abi-smoke/task_spawn_rc.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_bind",
            .source = "tests/abi-smoke/task_bind.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_bind_pending",
            .source = "tests/abi-smoke/task_bind_pending.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_map",
            .source = "tests/abi-smoke/task_map.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_get",
            .source = "tests/abi-smoke/task_get.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_get_from_worker",
            .source = "tests/abi-smoke/task_get_from_worker.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_sync_panic",
            .source = "tests/abi-smoke/task_sync_panic.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
            .expect_nonzero = true,
            .stderr_contains = "`Task.get` called from a `(sync := true)` task",
        },
        .{
            .name = "task_dep_chain",
            .source = "tests/abi-smoke/task_dep_chain.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_handle_finished",
            .source = "tests/abi-smoke/task_handle_finished.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_cancel",
            .source = "tests/abi-smoke/task_cancel.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_state",
            .source = "tests/abi-smoke/task_state.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_wait_any",
            .source = "tests/abi-smoke/task_wait_any.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_mark_mt",
            .source = "tests/abi-smoke/task_mark_mt.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_stress_fanout",
            .source = "tests/abi-smoke/task_stress_fanout.c",
            .use_split_runtime = true,
            .support_cpp = "tests/scheduler-smoke/link_support.cpp",
            .extra_support_cpp = "tests/abi-smoke/io_error_compat.cpp",
            .needs_stage1_libs = true,
        },
        .{
            .name = "task_heartbeat",
            .source = "tests/abi-smoke/task_heartbeat.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_init",
            .source = "tests/abi-smoke/task_init.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_finalize",
            .source = "tests/abi-smoke/task_finalize.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "task_double_init",
            .source = "tests/abi-smoke/task_double_init.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
            .expect_nonzero = true,
            .stderr_contains = "lean task manager already initialized; call lean_finalize_task_manager() before re-initializing",
        },
        .{
            .name = "run_main_inline",
            .source = "tests/abi-smoke/run_main_inline.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "run_main_stack",
            .source = "tests/abi-smoke/run_main_stack.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "run_main_io",
            .source = "tests/abi-smoke/run_main_io.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "promise_basic",
            .source = "tests/abi-smoke/promise_basic.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "promise_resolve",
            .source = "tests/abi-smoke/promise_resolve.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "promise_result_opt",
            .source = "tests/abi-smoke/promise_result_opt.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "promise_double_resolve",
            .source = "tests/abi-smoke/promise_double_resolve.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "promise_rc",
            .source = "tests/abi-smoke/promise_rc.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "current_task_tls",
            .source = "tests/abi-smoke/current_task_tls.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/current_task_tls_support.cpp",
            .extra_support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "bignum",
            .source = "tests/abi-smoke/bignum.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/mpz_alloc_support.cpp",
            .needs_gmp = true,
        },
        .{
            .name = "mpz_alloc",
            .source = "tests/abi-smoke/mpz_alloc.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/mpz_alloc_support.cpp",
        },
        .{
            .name = "bignum_link_check",
            .source = "tests/bignum-smoke/link_check.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/mpz_alloc_support.cpp",
            .needs_gmp = true,
        },
        .{
            .name = "compactor_xarchive",
            .source = "tests/bignum-smoke/compactor_xarchive.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/mpz_alloc_support.cpp",
        },
        .{
            .name = "float",
            .source = "tests/abi-smoke/float.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "once_cold",
            .source = "tests/abi-smoke/once_cold.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "st_ref",
            .source = "tests/abi-smoke/st_ref.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "misc",
            .source = "tests/abi-smoke/misc.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "io_result",
            .source = "tests/abi-smoke/io_result.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "io_result_show_error",
            .source = "tests/abi-smoke/io_result_show_error.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "io_error",
            .source = "tests/abi-smoke/io_error.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "io_error_no_libinit",
            .source = "tests/abi-smoke/io_error_no_libinit.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "decode_io_error",
            .source = "tests/abi-smoke/decode_io_error.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "dbg",
            .source = "tests/abi-smoke/dbg.c",
            .use_split_runtime = true,
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
        },
        .{
            .name = "panic",
            .source = "tests/abi-smoke/panic.c",
            .support_cpp = "tests/abi-smoke/io_error_compat.cpp",
            .expect_nonzero = true,
            .stderr_contains = "boom",
        },
    };

    const abi_test_step = b.step("test-abi", "Build and run the ABI smoke tests");
    abi_test_step.dependOn(install_step);

    for (abi_smoke_tests) |abi_test| {
        const compile = b.addSystemCommand(&.{"cc"});
        compile.setCwd(b.path("."));
        compile.step.dependOn(install_step);
        compile.addArgs(&.{
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-pedantic",
            "-I",
            lean_include,
            "-I",
            lean_stage1_include,
        });
        compile.addFileArg(b.path(abi_test.source));
        if (abi_test.needs_gmp) {
            compile.addArgs(&.{ "-I", gmp_include });
        }
        const support_obj = if (abi_test.support_cpp) |support_cpp| blk: {
            const support_compile = b.addSystemCommand(&.{"c++"});
            support_compile.setCwd(b.path("."));
            support_compile.step.dependOn(install_step);
            support_compile.addArgs(&.{
                "-Wall",
                "-Wextra",
                "-pedantic",
                "-std=c++17",
                "-c",
                "-I",
                lean_include,
                "-I",
                lean_stage1_include,
                "-I",
                lean_src,
            });
            support_compile.addFileArg(b.path(support_cpp));
            support_compile.addArg("-o");
            break :blk support_compile.addOutputFileArg(b.fmt("abi-smoke-{s}-support.o", .{abi_test.name}));
        } else null;
        const extra_support_obj = if (abi_test.extra_support_cpp) |support_cpp| blk: {
            const support_compile = b.addSystemCommand(&.{"c++"});
            support_compile.setCwd(b.path("."));
            support_compile.step.dependOn(install_step);
            support_compile.addArgs(&.{
                "-Wall",
                "-Wextra",
                "-pedantic",
                "-std=c++17",
                "-c",
                "-I",
                lean_include,
                "-I",
                lean_stage1_include,
                "-I",
                lean_src,
            });
            support_compile.addFileArg(b.path(support_cpp));
            support_compile.addArg("-o");
            break :blk support_compile.addOutputFileArg(b.fmt("abi-smoke-{s}-extra-support.o", .{abi_test.name}));
        } else null;

        if (support_obj) |obj| {
            compile.addFileArg(obj);
        }
        if (extra_support_obj) |obj| {
            compile.addFileArg(obj);
        }

        if (abi_test.use_split_runtime) {
            compile.addArgs(&.{
                "zig-out/lib/libleanrt-zig.a",
                "zig-out/lib/libleanrt_cpp_partial.a",
            });
            if (abi_test.needs_stage1_libs) {
                compile.addArgs(&.{
                    "-L",
                    lean_stage1_lib,
                    "-lleanrt",
                    "-lleancpp",
                    "-lInit",
                    "-lStd",
                    "-lLean",
                    "-lLake",
                });
            }
            compile.addArgs(&.{
                "-L",
                gmp_lib,
                "-lgmp",
                "-L",
                libuv_lib,
                "-luv",
                "-lc++",
                "-lpthread",
                "-lm",
            });
        } else {
            compile.addArg("zig-out/lib/libleanrt-zig-testabi.a");
        }
        if (abi_test.needs_gmp and !abi_test.use_split_runtime) {
            compile.addArgs(&.{
                "-L",
                gmp_lib,
                "-lgmp",
            });
        }
        compile.addArg("-o");
        const abi_binary = compile.addOutputFileArg(b.fmt("abi-smoke-{s}", .{abi_test.name}));

        const run = if (abi_test.expect_nonzero)
            b.addSystemCommand(&.{
                "/bin/sh",
                "-c",
                "stderr_file=$(mktemp); \"$1\" 2>\"$stderr_file\"; status=$?; if [ \"$status\" -eq 0 ]; then echo \"panic: FAIL (expected non-zero exit)\" >&2; cat \"$stderr_file\" >&2; rm -f \"$stderr_file\"; exit 1; fi; if ! grep -q -- \"$2\" \"$stderr_file\"; then echo \"panic: FAIL (missing stderr substring '$2')\" >&2; cat \"$stderr_file\" >&2; rm -f \"$stderr_file\"; exit 1; fi; echo \"panic: PASS (exited non-zero and printed '$2' to stderr)\"; rm -f \"$stderr_file\";",
                "panic-check",
            })
        else
            b.addSystemCommand(&.{"/usr/bin/env"});
        run.setCwd(b.path("."));
        run.step.dependOn(&compile.step);
        run.addFileArg(abi_binary);
        if (abi_test.stderr_contains) |needle| {
            run.addArg(needle);
        }
        abi_test_step.dependOn(&run.step);
        if (std.mem.eql(u8, abi_test.name, "task_handle_finished")) {
            const single_test_step = b.step(
                "abi-smoke-task_handle_finished",
                "Build and run the task_handle_finished ABI smoke test",
            );
            single_test_step.dependOn(&run.step);
        }
    }

    const link_check_compile = b.addSystemCommand(&.{"cc"});
    link_check_compile.setCwd(b.path("."));
    link_check_compile.step.dependOn(install_step);
    link_check_compile.addArgs(&.{
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
    });
    link_check_compile.addFileArg(b.path("tests/bignum-smoke/link_check.c"));
    const link_support_compile = b.addSystemCommand(&.{"c++"});
    link_support_compile.setCwd(b.path("."));
    link_support_compile.step.dependOn(install_step);
    link_support_compile.addArgs(&.{
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-std=c++17",
        "-c",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
        "-I",
        lean_src,
    });
    link_support_compile.addFileArg(b.path("tests/abi-smoke/mpz_alloc_support.cpp"));
    link_support_compile.addArg("-o");
    const link_support_obj = link_support_compile.addOutputFileArg("bignum-link-check-support.o");
    link_check_compile.addFileArg(link_support_obj);
    link_check_compile.addArgs(&.{
        "zig-out/lib/libleanrt-zig.a",
        "zig-out/lib/libleanrt_cpp_partial.a",
        "-L",
        lean_stage1_lib,
        "-lleancpp",
        "-lInit",
        "-lStd",
        "-lLean",
        "-lLake",
        "-L",
        gmp_lib,
        "-lgmp",
        "-L",
        libuv_lib,
        "-luv",
        "-lc++",
        "-lpthread",
        "-lm",
        "-o",
    });
    const link_check_bin = link_check_compile.addOutputFileArg("bignum-link-check");

    const link_check = b.addSystemCommand(&.{"/usr/bin/env"});
    link_check.setCwd(b.path("."));
    link_check.step.dependOn(&link_check_compile.step);
    link_check.addFileArg(link_check_bin);

    const link_check_step = b.step(
        "link-check",
        "Link a mixed Zig/C++ consumer to catch duplicate symbols",
    );
    link_check_step.dependOn(&link_check.step);

    const emitzig_smoke_step = b.step(
        "emitzig-smoke",
        "Build and run the EmitZig smoke programs",
    );
    emitzig_smoke_step.dependOn(install_step);

    const emitzig_smoke_scripts = [_][]const u8{
        "tests/emitzig-smoke/hello/run.sh",
        "tests/emitzig-smoke/arith/run.sh",
        "tests/emitzig-smoke/array_loop/run.sh",
        "tests/emitzig-smoke/bignum/run.sh",
    };

    for (emitzig_smoke_scripts) |script| {
        const run_smoke = b.addSystemCommand(&.{
            "/usr/bin/env",
            "EMITZIG_SMOKE_SKIP_ZIG_BUILD=1",
            b.fmt("LEAN4_DIR={s}", .{lean4_dir}),
            b.fmt("GMP_PREFIX={s}", .{gmp_prefix}),
            b.fmt("LIBUV_PREFIX={s}", .{libuv_prefix}),
            "bash",
            script,
        });
        run_smoke.setCwd(b.path("."));
        run_smoke.step.dependOn(install_step);
        emitzig_smoke_step.dependOn(&run_smoke.step);
    }

    const emitzig_diff_step = b.step(
        "emitzig-diff",
        "Run the EmitZig vs EmitC differential smoke programs",
    );
    emitzig_diff_step.dependOn(install_step);

    const emitzig_diff_scripts = [_][]const u8{
        "tests/emitzig-smoke/hello/run_diff.sh",
        "tests/emitzig-smoke/arith/run_diff.sh",
        "tests/emitzig-smoke/array_loop/run_diff.sh",
        "tests/emitzig-smoke/bignum/run_diff.sh",
    };

    for (emitzig_diff_scripts) |script| {
        const run_diff = b.addSystemCommand(&.{
            "/usr/bin/env",
            "EMITZIG_SMOKE_SKIP_ZIG_BUILD=1",
            b.fmt("LEAN4_DIR={s}", .{lean4_dir}),
            b.fmt("GMP_PREFIX={s}", .{gmp_prefix}),
            b.fmt("LIBUV_PREFIX={s}", .{libuv_prefix}),
            "bash",
            script,
        });
        run_diff.setCwd(b.path("."));
        run_diff.step.dependOn(install_step);
        emitzig_diff_step.dependOn(&run_diff.step);
    }

    const task_smoke_step = b.step(
        "task-smoke",
        "Build and diff the M5 task EmitZig smoke programs",
    );
    task_smoke_step.dependOn(install_step);

    const task_smoke_scripts = [_][]const u8{
        "tests/emitzig-smoke/task_spawn/run.sh",
        "tests/emitzig-smoke/task_bind/run.sh",
        "tests/emitzig-smoke/promise_basic/run.sh",
        "tests/emitzig-smoke/task_spawn/run_diff.sh",
        "tests/emitzig-smoke/task_bind/run_diff.sh",
        "tests/emitzig-smoke/promise_basic/run_diff.sh",
    };

    for (task_smoke_scripts) |script| {
        const run_task_smoke = b.addSystemCommand(&.{
            "/usr/bin/env",
            "EMITZIG_SMOKE_SKIP_ZIG_BUILD=1",
            b.fmt("LEAN4_DIR={s}", .{lean4_dir}),
            b.fmt("GMP_PREFIX={s}", .{gmp_prefix}),
            b.fmt("LIBUV_PREFIX={s}", .{libuv_prefix}),
            "bash",
            script,
        });
        run_task_smoke.setCwd(b.path("."));
        run_task_smoke.step.dependOn(install_step);
        task_smoke_step.dependOn(&run_task_smoke.step);
    }

    const bignum_diff_step = b.step(
        "bignum-diff",
        "Build and run the bignum differential harness",
    );
    bignum_diff_step.dependOn(install_step);

    const run_bignum_diff = b.addSystemCommand(&.{
        "/usr/bin/env",
        "BIGNUM_DIFF_SKIP_ZIG_BUILD=1",
        b.fmt("LEAN4_DIR={s}", .{lean4_dir}),
        b.fmt("GMP_PREFIX={s}", .{gmp_prefix}),
        b.fmt("LIBUV_PREFIX={s}", .{libuv_prefix}),
        "bash",
        "tests/bignum-smoke/run.sh",
    });
    run_bignum_diff.setCwd(b.path("."));
    run_bignum_diff.step.dependOn(install_step);
    bignum_diff_step.dependOn(&run_bignum_diff.step);

    const scheduler_support_compile = b.addSystemCommand(&.{"c++"});
    scheduler_support_compile.setCwd(b.path("."));
    scheduler_support_compile.step.dependOn(install_step);
    scheduler_support_compile.addArgs(&.{
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-std=c++17",
        "-c",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
        "-I",
        lean_src,
        "tests/scheduler-smoke/link_support.cpp",
        "-o",
        ".zig-cache/scheduler-link-support.o",
    });

    const scheduler_link_check_compile = b.addSystemCommand(&.{"cc"});
    scheduler_link_check_compile.setCwd(b.path("."));
    scheduler_link_check_compile.step.dependOn(&scheduler_support_compile.step);
    scheduler_link_check_compile.addArgs(&.{
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
        "tests/scheduler-smoke/link_check.c",
        ".zig-cache/scheduler-link-support.o",
        "zig-out/lib/libleanrt-zig.a",
        "zig-out/lib/libleanrt_cpp_partial.a",
        "-L",
        lean_stage1_lib,
        "-lleanrt",
        "-lleancpp",
        "-lInit",
        "-lStd",
        "-lLean",
        "-lLake",
        "-L",
        gmp_lib,
        "-lgmp",
        "-L",
        libuv_lib,
        "-luv",
        "-lc++",
        "-lpthread",
        "-lm",
        "-o",
        ".zig-cache/scheduler_link_check",
    });

    const scheduler_fairness_compile = b.addSystemCommand(&.{"cc"});
    scheduler_fairness_compile.setCwd(b.path("."));
    scheduler_fairness_compile.step.dependOn(&scheduler_support_compile.step);
    scheduler_fairness_compile.addArgs(&.{
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
        "tests/scheduler-smoke/fairness.c",
        ".zig-cache/scheduler-link-support.o",
        "zig-out/lib/libleanrt-zig.a",
        "zig-out/lib/libleanrt_cpp_partial.a",
        "-L",
        lean_stage1_lib,
        "-lleanrt",
        "-lleancpp",
        "-lInit",
        "-lStd",
        "-lLean",
        "-lLake",
        "-L",
        gmp_lib,
        "-lgmp",
        "-L",
        libuv_lib,
        "-luv",
        "-lc++",
        "-lpthread",
        "-lm",
        "-o",
        ".zig-cache/scheduler_fairness",
    });

    const scheduler_post_compile = b.addSystemCommand(&.{"cc"});
    scheduler_post_compile.setCwd(b.path("."));
    scheduler_post_compile.step.dependOn(&scheduler_support_compile.step);
    scheduler_post_compile.addArgs(&.{
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-pedantic",
        "-I",
        lean_include,
        "-I",
        lean_stage1_include,
        "tests/scheduler-smoke/fanout.c",
        ".zig-cache/scheduler-link-support.o",
        "zig-out/lib/libleanrt-zig.a",
        "zig-out/lib/libleanrt_cpp_partial.a",
        "-L",
        lean_stage1_lib,
        "-lleanrt",
        "-lleancpp",
        "-lInit",
        "-lStd",
        "-lLean",
        "-lLake",
        "-L",
        gmp_lib,
        "-lgmp",
        "-L",
        libuv_lib,
        "-luv",
        "-lc++",
        "-lpthread",
        "-lm",
        "-o",
        ".zig-cache/scheduler_zig",
    });

    const scheduler_diff_runner = b.addExecutable(.{
        .name = "scheduler_diff_runner",
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/scheduler-smoke/diff.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
    });

    const run_scheduler_link_check = b.addSystemCommand(&.{"/usr/bin/env", ".zig-cache/scheduler_link_check"});
    run_scheduler_link_check.setCwd(b.path("."));
    run_scheduler_link_check.step.dependOn(&scheduler_link_check_compile.step);

    const run_scheduler_fairness = b.addSystemCommand(&.{"/usr/bin/env", ".zig-cache/scheduler_fairness"});
    run_scheduler_fairness.setCwd(b.path("."));
    run_scheduler_fairness.step.dependOn(&scheduler_fairness_compile.step);

    const run_scheduler_diff = b.addRunArtifact(scheduler_diff_runner);
    run_scheduler_diff.setCwd(b.path("."));
    run_scheduler_diff.step.dependOn(&scheduler_post_compile.step);

    const scheduler_diff_step = b.step(
        "scheduler-diff",
        "M5b-F14 differential vs frozen reference",
    );
    scheduler_diff_step.dependOn(&run_scheduler_link_check.step);
    scheduler_diff_step.dependOn(&run_scheduler_fairness.step);
    scheduler_diff_step.dependOn(&run_scheduler_diff.step);

    const run_lean_smoke = b.addSystemCommand(&.{
        "/usr/bin/env",
        "LEAN_SMOKE_SKIP_ZIG_BUILD=1",
        b.fmt("LEAN4_DIR={s}", .{lean4_dir}),
        b.fmt("GMP_PREFIX={s}", .{gmp_prefix}),
        b.fmt("LIBUV_PREFIX={s}", .{libuv_prefix}),
        "bash",
        "tests/lean-smoke/run.sh",
    });
    run_lean_smoke.setCwd(b.path("."));
    run_lean_smoke.step.dependOn(install_step);

    const lean_smoke_step = b.step(
        "lean-smoke",
        "End-to-end Lean -> C -> split-runtime smoke test",
    );
    lean_smoke_step.dependOn(&run_lean_smoke.step);

    const test_all_step = b.step(
        "test-all",
        "Run every suite: unit, abi, link, smoke, and differential tests",
    );
    test_all_step.dependOn(test_step);
    test_all_step.dependOn(abi_test_step);
    test_all_step.dependOn(link_check_step);
    test_all_step.dependOn(emitzig_smoke_step);
    test_all_step.dependOn(emitzig_diff_step);
    test_all_step.dependOn(task_smoke_step);
    test_all_step.dependOn(bignum_diff_step);
    test_all_step.dependOn(lean_smoke_step);
    // scheduler-diff is intentionally excluded: its binaries link the full
    // upstream libleanrt (real mimalloc), and the Zig allocator's legacy
    // free path currently segfaults in that mixed-runtime configuration.
    // See docs/ROADMAP.md (M8: allocator ownership across mixed links).
}
