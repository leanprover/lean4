#!/usr/bin/env python3
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

"""Generate EmitZig runtime extern declarations from lean.h and known extras."""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_H = ROOT / "src" / "include" / "lean" / "lean.h"
INLINE_HELPERS = ROOT / "src" / "Lean" / "Compiler" / "LCNF" / "EmitZig" / "InlineHelpers.lean"
OUT = ROOT / "src" / "Lean" / "Compiler" / "LCNF" / "EmitZig" / "RuntimeExterns.lean"
ZIG_RT = ROOT / "src" / "runtime" / "zig"

TYPE_REPLACEMENTS = [
    (r"\bunsigned char\b", "u8"),
    (r"\bunsigned int\b", "c_uint"),
    (r"\bunsigned long\b", "c_ulong"),
    (r"\bunsigned\b", "c_uint"),
    (r"\buint8_t\b", "u8"),
    (r"\buint16_t\b", "u16"),
    (r"\buint32_t\b", "u32"),
    (r"\buint64_t\b", "u64"),
    (r"\bptrdiff_t\b", "isize"),
    (r"\bssize_t\b", "isize"),
    (r"\bint\b", "c_int"),
    (r"\bint8_t\b", "i8"),
    (r"\bint16_t\b", "i16"),
    (r"\bint32_t\b", "i32"),
    (r"\bint64_t\b", "i64"),
    (r"\bsize_t\b", "usize"),
    (r"\bdouble\b", "f64"),
    (r"\bfloat\b", "f32"),
    (r"\bbool\b", "bool"),
    (r"\bvoid\b", "void"),
    (r"\bchar\b", "u8"),
    (r"\blean_obj_arg\b", "LeanObj"),
    (r"\bb_lean_obj_arg\b", "LeanObj"),
    (r"\bu_lean_obj_arg\b", "LeanObj"),
    (r"\bb_lean_obj_res\b", "LeanObj"),
    (r"\blean_obj_res\b", "LeanObj"),
    (r"\blean_object\s*\*", "LeanObj"),
    (r"\bconst\s+lean_object\s*\*", "LeanObj"),
    (r"\blean_string_object\s*\*", "LeanObj"),
    (r"\blean_thunk_object\s*\*", "LeanObj"),
    (r"\blean_task_object\s*\*", "LeanObj"),
    (r"\bchar const\s*\*", "[*:0]const u8"),
    (r"\bconst char\s*\*", "[*:0]const u8"),
    (r"\bconst\s+char\s*\*", "[*c]const u8"),
    (r"\bchar\s*\*", "[*c]u8"),
    (r"\bconst\s+uint8_t\s*\*", "[*c]const u8"),
    (r"\buint8_t\s*\*", "[*c]u8"),
]

MATH_FUNCS = [
    ("sin", "f64", "f64"),
    ("sinf", "f32", "f32"),
    ("cos", "f64", "f64"),
    ("cosf", "f32", "f32"),
    ("tan", "f64", "f64"),
    ("tanf", "f32", "f32"),
    ("asin", "f64", "f64"),
    ("asinf", "f32", "f32"),
    ("acos", "f64", "f64"),
    ("acosf", "f32", "f32"),
    ("atan", "f64", "f64"),
    ("atanf", "f32", "f32"),
    ("atan2", "f64", "f64", "f64"),
    ("atan2f", "f32", "f32", "f32"),
    ("sinh", "f64", "f64"),
    ("sinhf", "f32", "f32"),
    ("cosh", "f64", "f64"),
    ("coshf", "f32", "f32"),
    ("tanh", "f64", "f64"),
    ("tanhf", "f32", "f32"),
    ("asinh", "f64", "f64"),
    ("asinhf", "f32", "f32"),
    ("acosh", "f64", "f64"),
    ("acoshf", "f32", "f32"),
    ("atanh", "f64", "f64"),
    ("atanhf", "f32", "f32"),
    ("exp", "f64", "f64"),
    ("expf", "f32", "f32"),
    ("exp2", "f64", "f64"),
    ("exp2f", "f32", "f32"),
    ("log", "f64", "f64"),
    ("logf", "f32", "f32"),
    ("log2", "f64", "f64"),
    ("log2f", "f32", "f32"),
    ("log10", "f64", "f64"),
    ("log10f", "f32", "f32"),
    ("pow", "f64", "f64", "f64"),
    ("powf", "f32", "f32", "f32"),
    ("sqrt", "f64", "f64"),
    ("sqrtf", "f32", "f32"),
    ("cbrt", "f64", "f64"),
    ("cbrtf", "f32", "f32"),
    ("fabs", "f64", "f64"),
    ("fabsf", "f32", "f32"),
    ("floor", "f64", "f64"),
    ("floorf", "f32", "f32"),
    ("ceil", "f64", "f64"),
    ("ceilf", "f32", "f32"),
    ("round", "f64", "f64"),
    ("roundf", "f32", "f32"),
]

# Symbols referenced by stdlib/runtime but not declared in lean.h.
# Defined locally in `EmitZig.lean` preamble (not as runtime externs).
EMITZIG_LOCAL_FUNCS = {
    "lean_io_result_is_ok",
    "lean_io_result_get_value",
}

EXTRA_FUNCS: list[tuple[str, str, str]] = [
    ("lean_get_githash", "LeanObj", "LeanObj"),
    ("lean_version_get_major", "LeanObj", "LeanObj"),
    ("lean_version_get_minor", "LeanObj", "LeanObj"),
    ("lean_version_get_patch", "LeanObj", "LeanObj"),
    ("lean_version_get_is_release", "u8", "LeanObj"),
    ("lean_version_get_special_desc", "LeanObj", "LeanObj"),
    ("lean_internal_is_stage0", "u8", "LeanObj"),
    ("lean_internal_has_llvm_backend", "u8", "LeanObj"),
    ("lean_internal_get_hardware_concurrency", "u32", ""),
    ("lean_dbg_stack_trace", "LeanObj", "LeanObj"),
    ("lean_byte_array_copy_slice", "LeanObj", "LeanObj, LeanObj, LeanObj, LeanObj"),
    ("lean_chmod", "LeanObj", "LeanObj, LeanObj"),
    ("lean_nat_land", "LeanObj", "LeanObj, LeanObj"),
    ("lean_nat_lor", "LeanObj", "LeanObj, LeanObj"),
    ("lean_nat_lxor", "LeanObj", "LeanObj, LeanObj"),
    ("lean_nat_shiftr", "LeanObj", "LeanObj, LeanObj"),
    ("lean_sorry", "LeanObj", ""),
    ("lean_string_to_utf8", "LeanObj", "LeanObj"),
    ("lean_string_from_utf8_unchecked", "LeanObj", "LeanObj"),
    ("exit", "noreturn", "c_int"),
    ("lean_setup_args", "[*c][*c]u8", "c_int, [*c][*c]u8"),
    ("lean_run_main", "LeanObj", "MainFn, c_int, [*c][*c]u8"),
    ("lean_initialize", "void", ""),
    ("lean_initialize_runtime_module", "void", ""),
    ("lean_initialize_thread", "void", ""),
    ("lean_init_task_manager", "void", ""),
    ("lean_finalize_task_manager", "void", ""),
    ("lean_io_mark_end_initialization", "void", ""),
    ("lean_io_result_show_error", "void", "LeanObj"),
    ("lean_array_get_panic", "LeanObj", "LeanObj"),
    ("lean_mk_string", "LeanObj", "[*c]const u8"),
    ("lean_mk_string_unchecked", "LeanObj", "[*c]const u8, usize, usize"),
    ("lean_string_utf8_get_fast_cold", "u32", "[*:0]const u8, usize, usize, u8"),
]


def load_inline_helper_names() -> set[str]:
    text = INLINE_HELPERS.read_text()
    names = set(re.findall(r'\("([^"]+)"', text))
    # Also pick up names from bignumExternHelperEntries extern lines.
    names.update(re.findall(r'extern fn (lean_\w+)', text))
    return names


def zig_type_to_extern(zig_type: str) -> str:
    t = zig_type.strip()
    mapping = {
        "?*anyopaque": "LeanObj",
        "*anyopaque": "LeanObj",
        "usize": "usize",
        "u8": "u8",
        "u16": "u16",
        "u32": "u32",
        "u64": "u64",
        "i8": "i8",
        "i16": "i16",
        "i32": "i32",
        "i64": "i64",
        "isize": "isize",
        "f32": "f32",
        "f64": "f64",
        "bool": "bool",
        "void": "void",
        "c_int": "c_int",
        "c_uint": "c_uint",
    }
    return mapping.get(t, t)


def zig_rt_export_signatures() -> dict[str, tuple[str, list[str]]]:
    sigs: dict[str, tuple[str, list[str]]] = {}
    export_pat = re.compile(
        r"export fn (lean_\w+)\((.*?)\) callconv\(\.c\) ([^\s{]+)",
        re.DOTALL,
    )
    for path in ZIG_RT.rglob("*.zig"):
        text = path.read_text(errors="replace")
        for m in export_pat.finditer(text):
            name, args_blob, ret = m.group(1), m.group(2), m.group(3)
            arg_types: list[str] = []
            if args_blob.strip():
                for arg in args_blob.split(","):
                    arg = arg.strip()
                    if ":" in arg:
                        arg_types.append(zig_type_to_extern(arg.split(":", 1)[1].strip()))
            sigs[name] = (zig_type_to_extern(ret), arg_types)
    return sigs


def normalize_type(c_type: str) -> str:
    t = re.sub(r"\s+", " ", c_type.strip())
    t = t.replace("const ", "const ")
    if "(*)" in t or "(*" in t:
        return "?*anyopaque"
    for pat, repl in TYPE_REPLACEMENTS:
        t = re.sub(pat, repl, t)
    t = re.sub(r"\s+", " ", t).strip()
    if t == "":
        return "void"
    if t.endswith("*"):
        inner = t[:-1]
        if inner in ("LeanObj", "u8"):
            return "LeanObj" if inner == "LeanObj" else "[*c]u8"
        return "?*anyopaque"
    return t


def split_args(arg_str: str) -> list[str]:
    if not arg_str.strip():
        return []
    args: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in arg_str:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            args.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    tail = "".join(cur).strip()
    if tail:
        args.append(tail)
    return args


def parse_arg(arg: str) -> str:
    arg = arg.strip()
    if not arg or arg == "void":
        return ""
    # Strip parameter names, keep type.
    arg = re.sub(r"\b\w+\s*$", "", arg).strip()
    return normalize_type(arg)


def parse_signature(ret: str, args: str) -> tuple[str, list[str]]:
    noreturn = "LEAN_NORETURN" in ret
    ret = ret.replace("LEAN_NORETURN", "").strip()
    if noreturn and ret == "void":
        zret = "noreturn void"
    else:
        zret = normalize_type(ret)
    zargs = [parse_arg(a) for a in split_args(args)]
    zargs = [a for a in zargs if a]
    return zret, zargs


def parse_lean_h(text: str) -> dict[str, tuple[str, list[str]]]:
    funcs: dict[str, tuple[str, list[str]]] = {}

    export_pat = re.compile(
        r"LEAN_EXPORT\s+(?:LEAN_NORETURN\s+)?((?:const\s+)?[\w\s\*]+?)\s+(lean_\w+)\s*\(([^;]*)\)\s*;",
        re.MULTILINE,
    )
    for m in export_pat.finditer(text):
        args_blob = m.group(3)
        if "(*" in args_blob:
            argc = 0 if not args_blob.strip() else args_blob.count(",") + 1
            funcs[m.group(2)] = simplify_complex_signature(
                m.group(2), parse_signature(m.group(1), "")[0], ["LeanObj"] * argc
            )
        else:
            funcs[m.group(2)] = parse_signature(m.group(1), args_blob)

    inline_pat = re.compile(
        r"static\s+inline\s+((?:const\s+)?[\w\s\*]+?)\s+(lean_\w+)\s*\(([^)]*)\)\s*\{",
        re.MULTILINE,
    )
    for m in inline_pat.finditer(text):
        funcs.setdefault(m.group(2), parse_signature(m.group(1), m.group(3)))

    return funcs


def simplify_complex_signature(name: str, ret: str, args: list[str]) -> tuple[str, list[str]]:
    blob = " ".join([ret, *args])
    if "(*" in blob or "fn (" in blob or "." in ret:
        zret = "LeanObj" if ret not in {"void", "noreturn", "bool", "u8", "u32", "u64", "usize", "f32", "f64"} else ret
        zargs = ["LeanObj" if a.startswith(("?", "*", "fn")) or "fn" in a else a for a in args]
        return zret, zargs
    return ret, args


def format_zig_extern(name: str, ret: str, args: list[str]) -> str:
    ret, args = simplify_complex_signature(name, ret, args)
    if ret in {"noreturn void", "noreturn"}:
        sig_ret = "noreturn"
    elif not ret or "fn" in ret:
        sig_ret = "LeanObj"
    else:
        sig_ret = ret
    if args:
        arg_sig = ", ".join(f"_{i}: {t}" for i, t in enumerate(args))
        return f"extern fn {name}({arg_sig}) callconv(.c) {sig_ret};"
    return f"extern fn {name}() callconv(.c) {sig_ret};"


def main() -> int:
    lean_h = LEAN_H.read_text()
    inline_names = load_inline_helper_names()
    funcs = parse_lean_h(lean_h)

    for name, ret, args in EXTRA_FUNCS:
        arg_list = [a.strip() for a in args.split(",") if a.strip()] if args else []
        funcs[name] = (ret, arg_list)

    for entry in MATH_FUNCS:
        name = entry[0]
        ret = entry[1]
        args = list(entry[2:])
        funcs[name] = (ret, args)

    # Ensure zig-runtime-only exports are declared with signatures from the Zig sources.
    for name, sig in sorted(zig_rt_export_signatures().items()):
        funcs.setdefault(name, sig)

    decls: list[str] = []
    for name in sorted(funcs):
        if name in inline_names or name in EMITZIG_LOCAL_FUNCS:
            continue
        ret, args = funcs[name]
        decls.append(format_zig_extern(name, ret, args))

    year = subprocess.check_output(["date", "+%Y"], text=True).strip()
    lines = [
        "/-",
        f"Copyright (c) {year} Lean FRO, LLC. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: Factory",
        "-/",
        "module",
        "",
        "prelude",
        "public import Init.Data.List.Basic",
        "public import Init.Data.String.Basic",
        "",
        "namespace RuntimeExterns",
        "",
        "/-- Auto-generated from `tools/gen-emitzig-runtime-externs.py`. Do not edit by hand. -/",
        "public def runtimeExternDeclsGenerated : List String := [",
    ]
    for decl in decls:
        escaped = decl.replace("\\", "\\\\").replace("\"", "\\\"")
        lines.append(f"  \"{escaped}\",")
    lines += [
        "]",
        "",
        "end RuntimeExterns",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {len(decls)} extern decls to {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())