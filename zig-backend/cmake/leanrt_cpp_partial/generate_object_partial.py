#!/usr/bin/env python3
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

from pathlib import Path
import sys


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: generate_object_partial.py <src> <dst>")

    src = Path(sys.argv[1])
    dst = Path(sys.argv[2])
    text = src.read_text()

    task_block_start = text.index("class task_manager {")
    task_block_end = text.index("// =======================================\n// Natural numbers")
    text = text[:task_block_start] + text[task_block_end:]

    start = text.index('#ifdef LEAN_USE_GMP\nextern "C" LEAN_EXPORT lean_object * lean_alloc_mpz(mpz_t v) {')
    end = text.index('extern "C" LEAN_EXPORT lean_obj_res lean_float_to_string(double a) {')
    text = text[:start] + text[end:]

    scoped = """struct scoped_current_task_object : flet<lean_task_object *> {\n    scoped_current_task_object(lean_task_object * t):flet(g_current_task_object, t) {}\n};\n"""
    replacement = """extern \"C\" lean_task_object * lean_zig_current_task_swap(lean_task_object *);\n\nstruct scoped_current_task_object : flet<lean_task_object *> {\n    lean_task_object * m_prev_zig;\n    scoped_current_task_object(lean_task_object * t):flet(g_current_task_object, t), m_prev_zig(lean_zig_current_task_swap(t)) {}\n    ~scoped_current_task_object() { lean_zig_current_task_swap(m_prev_zig); }\n};\n"""

    if scoped not in text:
        raise SystemExit("failed to find scoped_current_task_object block in object.cpp")

    dst.write_text(text.replace(scoped, replacement, 1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
