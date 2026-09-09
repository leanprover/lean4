#!/usr/bin/env bash
set -euo pipefail

# Re-detect the external dependencies of a configured build directory.
#
# `nix-collect-garbage` deletes store paths that a configured build directory still points at,
# for us usually `gmp`, `libuv` and `openssl`. The build then fails long before it compiles
# anything, with `fatal error: 'gmp.h' file not found` or
# `clang: error: no such file or directory: '/nix/store/...-gmp-with-cxx-6.3.0/lib/libgmp.so'`.
# Dropping the pinned entries makes the next configure pick up the live paths again from the
# `CMAKE_PREFIX_PATH` that a dev shell keeps current.
#
# Only cache entries are rewritten; no build output is deleted.
#
# Usage:
#   script/refresh-cmake-deps.sh stage0/src build/release/stage0
#   script/refresh-cmake-deps.sh src        build/release/stage1

SRC_DIR=${1:?usage: $0 SRC_DIR BUILD_DIR}
BUILD_DIR=${2:?usage: $0 SRC_DIR BUILD_DIR}

# Every entry pinning a store path, plus the `_FOUND` gates: `pkg_check_modules` recomputes its
# results only as a set, so leaving `LIBUV_FOUND` behind would drop the entries above without
# ever repopulating them.
#
# `CMAKE_*` is exempt, and safely so: CMake rewrites `CMAKE_COMMAND`, `CMAKE_ROOT` and the
# `CMAKE_*_COMMAND` tool paths from the running executable on every configure, so a collected
# cmake recovers on its own, while dropping `CMAKE_CTEST_COMMAND` instead aborts the configure in
# `CTestTargets`. `MAKECOMMAND` is not exempt: it holds a cmake path that is never rewritten.
vars=$(sed -n -e 's|^\([A-Za-z_][A-Za-z_0-9]*\):[A-Z]*=.*/nix/store/.*|\1|p' \
              -e 's|^\([A-Za-z_][A-Za-z_0-9]*_FOUND\):.*|\1|p' \
              "$BUILD_DIR/CMakeCache.txt" | { grep -v '^CMAKE_' || true; } | sort -u)

# shellcheck disable=SC2046  # deliberate word splitting: cache variable names are identifiers
cmake $(printf -- '-U %s ' $vars) -S "$SRC_DIR" -B "$BUILD_DIR"
