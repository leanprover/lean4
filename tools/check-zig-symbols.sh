#!/usr/bin/env bash
# Placeholder: symbol coverage check for the in-tree Zig runtime.
# The original zig-backend/tools/check-symbols.sh compared split archives.
# Once CMake builds libleanrt-zig.a and libleanrt_cpp_partial.a, restore the
# nm-based subset check here.
set -euo pipefail
echo "check-zig-symbols: not yet implemented (pending CMake integration)"
exit 1
