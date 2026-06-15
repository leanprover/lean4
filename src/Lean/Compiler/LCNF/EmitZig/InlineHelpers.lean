/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Factory
-/
module

prelude
public import Lean.Data.NameMap.Basic
import Init.Data.String.Legacy
import Lean.CoreM
import Lean.Expr
import Lean.Data.Name

open Lean

namespace InlineHelpers

private def joinLines (lines : List String) : String :=
  String.intercalate "\n" lines

private def addEvalQuota (s : String) : String :=
  if s.startsWith "inline fn " then
    let lines := s.splitOn "\n"
    match lines with
    | first :: rest => String.intercalate "\n" (first :: "  @setEvalBranchQuota(10000000);" :: rest)
    | [] => s
  else
    s

private def supportInlineConsts : List String := [
  joinLines [
    "const LeanMaxCtorTag: c_uint = @as(c_uint, 243);",
    "const LeanMaxCtorFields: c_uint = @as(c_uint, 256);",
    "const LeanMaxCtorScalarsSize: usize = @as(usize, 1024);",
    "const LeanMaxSmallNat: usize = std.math.maxInt(usize) >> 1;"
  ]
]

private def supportInlineHelperEntries : List (String × String) := [
  ("lean_heap_obj", joinLines [
    "inline fn lean_heap_obj(o: LeanObj) *lean_object {",
    "  return @alignCast(o.?);",
    "}"
  ]),
  ("lean_is_scalar", joinLines [
    "inline fn lean_is_scalar(o: LeanObj) bool {",
    "  return (@intFromPtr(o.?) & 1) == 1;",
    "}"
  ]),
  ("lean_unbox", joinLines [
    "inline fn lean_unbox(o: LeanObj) usize {",
    "  return @intFromPtr(o.?) >> 1;",
    "}"
  ]),
  ("lean_ptr_tag", joinLines [
    "inline fn lean_ptr_tag(o: LeanObj) u8 {",
    "  return lean_heap_obj(o).m_tag;",
    "}"
  ]),
  ("lean_ptr_other", joinLines [
    "inline fn lean_ptr_other(o: LeanObj) u8 {",
    "  return lean_heap_obj(o).m_other;",
    "}"
  ]),
  ("lean_is_st", joinLines [
    "inline fn lean_is_st(o: LeanObj) bool {",
    "  return lean_heap_obj(o).m_rc > 0;",
    "}"
  ]),
  ("lean_get_rc_mt_addr", joinLines [
    "inline fn lean_get_rc_mt_addr(o: LeanObj) *i32 {",
    "  return &lean_heap_obj(o).m_rc;",
    "}"
  ]),
  ("lean_is_ctor", joinLines [
    "inline fn lean_is_ctor(o: LeanObj) bool {",
    "  return @as(c_uint, lean_ptr_tag(o)) <= LeanMaxCtorTag;",
    "}"
  ]),
  ("lean_ctor_num_objs", joinLines [
    "inline fn lean_ctor_num_objs(o: LeanObj) c_uint {",
    "  std.debug.assert(lean_is_ctor(o));",
    "  return @as(c_uint, lean_ptr_other(o));",
    "}"
  ]),
  ("lean_ctor_obj_cptr", joinLines [
    "inline fn lean_ctor_obj_cptr(o: LeanObj) [*]LeanObj {",
    "  std.debug.assert(lean_is_ctor(o));",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(o));",
    "  return @ptrCast(@alignCast(bytes + @sizeOf(lean_object)));",
    "}"
  ]),
  ("lean_set_st_header", joinLines [
    "inline fn lean_set_st_header(o: LeanObj, tag: c_uint, other: c_uint) void {",
    "  const obj = lean_heap_obj(o);",
    "  obj.m_rc = 1;",
    "  obj.m_tag = @as(u8, @intCast(tag));",
    "  obj.m_other = @as(u8, @intCast(other));",
    "  obj.m_cs_sz = 0;",
    "}"
  ]),
  ("lean_usize_mul_checked", joinLines [
    "inline fn lean_usize_mul_checked(a: usize, b: usize) usize {",
    "  return std.math.mul(usize, a, b) catch @panic(\"lean_usize_mul_checked overflow\");",
    "}"
  ]),
  ("lean_usize_add_checked", joinLines [
    "inline fn lean_usize_add_checked(a: usize, b: usize) usize {",
    "  return std.math.add(usize, a, b) catch @panic(\"lean_usize_add_checked overflow\");",
    "}"
  ]),
  ("lean_usize_to_nat", joinLines [
    "inline fn lean_usize_to_nat(n: usize) LeanObj {",
    "  if (n <= LeanMaxSmallNat) {",
    "    return lean_box(n);",
    "  } else {",
    "    return lean_big_usize_to_nat(n);",
    "  }",
    "}"
  ]),
  ("lean_array_fields", joinLines [
    "inline fn lean_array_fields(o: LeanObj) [*]usize {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(o));",
    "  return @ptrCast(@alignCast(bytes + @sizeOf(lean_object)));",
    "}"
  ]),
  ("lean_array_size", joinLines [
    "inline fn lean_array_size(o: LeanObj) usize {",
    "  return lean_array_fields(o)[0];",
    "}"
  ]),
  ("lean_array_cptr", joinLines [
    "inline fn lean_array_cptr(o: LeanObj) [*]LeanObj {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(o));",
    "  return @ptrCast(@alignCast(bytes + @sizeOf(lean_object) + 2 * @sizeOf(usize)));",
    "}"
  ]),
  ("lean_array_get_core", joinLines [
    "inline fn lean_array_get_core(o: LeanObj, i: usize) LeanObj {",
    "  std.debug.assert(i < lean_array_size(o));",
    "  return lean_array_cptr(o)[i];",
    "}"
  ]),
  ("lean_alloc_array", joinLines [
    "inline fn lean_alloc_array(size: usize, capacity: usize) LeanObj {",
    "  const total = lean_usize_add_checked(",
    "    @sizeOf(lean_object) + 2 * @sizeOf(usize),",
    "    lean_usize_mul_checked(@sizeOf(usize), capacity)",
    "  );",
    "  const o = lean_alloc_object(total);",
    "  lean_set_st_header(o, @as(c_uint, 246), @as(c_uint, 0));",
    "  const fields = lean_array_fields(o);",
    "  fields[0] = size;",
    "  fields[1] = capacity;",
    "  return o;",
    "}"
  ]),
  ("lean_nat_le", joinLines [
    "inline fn lean_nat_le(a1: LeanObj, a2: LeanObj) bool {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    return @intFromPtr(a1.?) <= @intFromPtr(a2.?);",
    "  } else {",
    "    return lean_nat_big_le(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_lt", joinLines [
    "inline fn lean_nat_lt(a1: LeanObj, a2: LeanObj) bool {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    return @intFromPtr(a1.?) < @intFromPtr(a2.?);",
    "  } else {",
    "    return lean_nat_big_lt(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_inc_ref_n", joinLines [
    "inline fn lean_inc_ref_n(o: LeanObj, n: usize) void {",
    "  const obj = lean_heap_obj(o);",
    "  if (lean_is_st(o)) {",
    "    obj.m_rc += @as(i32, @intCast(n));",
    "  } else if (obj.m_rc != 0) {",
    "    _ = @atomicRmw(i32, lean_get_rc_mt_addr(o), .Sub, @as(i32, @intCast(n)), .monotonic);",
    "  }",
    "}"
  ])
]

private def mvpInlineHelperEntries : List (String × String) := [
  ("lean_box", joinLines [
    "inline fn lean_box(n: usize) LeanObj {",
    "  const ptr: *align(1) lean_object = @ptrFromInt((n << 1) | 1);",
    "  return ptr;",
    "}"
  ]),
  ("lean_unsigned_to_nat", joinLines [
    "inline fn lean_unsigned_to_nat(n: c_uint) LeanObj {",
    "  return lean_usize_to_nat(@as(usize, n));",
    "}"
  ]),
  ("lean_unbox_uint32", joinLines [
    "inline fn lean_unbox_uint32(o: LeanObj) u32 {",
    "  if (@sizeOf(usize) == 4) {",
    "    return lean_ctor_get_uint32(o, @as(c_uint, 0));",
    "  } else {",
    "    return @as(u32, @intCast(lean_unbox(o)));",
    "  }",
    "}"
  ]),
  ("lean_io_result_mk_ok", joinLines [
    "inline fn lean_io_result_mk_ok(a: LeanObj) LeanObj {",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 1), @as(usize, 0));",
    "  lean_ctor_set(r, @as(c_uint, 0), a);",
    "  return r;",
    "}"
  ]),
  ("lean_io_mk_world", joinLines [
    "inline fn lean_io_mk_world() LeanObj {",
    "  return lean_box(@as(usize, 0));",
    "}"
  ]),
  ("lean_obj_tag", joinLines [
    "inline fn lean_obj_tag(o: LeanObj) c_uint {",
    "  if (lean_is_scalar(o)) {",
    "    return @as(c_uint, @intCast(lean_unbox(o)));",
    "  } else {",
    "    return @as(c_uint, lean_ptr_tag(o));",
    "  }",
    "}"
  ]),
  ("lean_ctor_get", joinLines [
    "inline fn lean_ctor_get(o: LeanObj, i: c_uint) LeanObj {",
    "  std.debug.assert(i < lean_ctor_num_objs(o));",
    "  return lean_ctor_obj_cptr(o)[@as(usize, i)];",
    "}"
  ]),
  ("lean_ctor_set_tag", joinLines [
    "inline fn lean_ctor_set_tag(o: LeanObj, new_tag: u8) void {",
    "  std.debug.assert(@as(c_uint, new_tag) <= LeanMaxCtorTag);",
    "  lean_heap_obj(o).m_tag = new_tag;",
    "}"
  ]),
  ("lean_inc_ref", joinLines [
    "inline fn lean_inc_ref(o: LeanObj) void {",
    "  lean_inc_ref_n(o, @as(usize, 1));",
    "}"
  ]),
  ("lean_dec_ref", joinLines [
    "inline fn lean_dec_ref(o: LeanObj) void {",
    "  const obj = lean_heap_obj(o);",
    "  if (obj.m_rc > 1) {",
    "    obj.m_rc -= 1;",
    "  } else if (obj.m_rc != 0) {",
    "    lean_dec_ref_cold(o);",
    "  }",
    "}"
  ]),
  ("lean_inc", joinLines [
    "inline fn lean_inc(o: LeanObj) void {",
    "  if (!lean_is_scalar(o)) lean_inc_ref(o);",
    "}"
  ]),
  ("lean_dec", joinLines [
    "inline fn lean_dec(o: LeanObj) void {",
    "  if (!lean_is_scalar(o)) lean_dec_ref(o);",
    "}"
  ]),
  ("lean_alloc_ctor", joinLines [
    "inline fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: usize) LeanObj {",
    "  std.debug.assert(tag <= LeanMaxCtorTag and num_objs < LeanMaxCtorFields and scalar_sz < LeanMaxCtorScalarsSize);",
    "  const total = lean_usize_add_checked(",
    "    lean_usize_add_checked(@sizeOf(lean_object), lean_usize_mul_checked(@sizeOf(usize), @as(usize, num_objs))),",
    "    scalar_sz",
    "  );",
    "  const o = lean_alloc_object(total);",
    "  lean_set_st_header(o, tag, num_objs);",
    "  return o;",
    "}"
  ]),
  ("lean_array_get_size", joinLines [
    "inline fn lean_array_get_size(a: LeanObj) LeanObj {",
    "  return lean_box(lean_array_size(a));",
    "}"
  ]),
  ("lean_array_uget", joinLines [
    "inline fn lean_array_uget(a: LeanObj, i: usize) LeanObj {",
    "  const r = lean_array_get_core(a, i);",
    "  lean_inc(r);",
    "  return r;",
    "}"
  ]),
  ("lean_array_uget_borrowed", joinLines [
    "inline fn lean_array_uget_borrowed(a: LeanObj, i: usize) LeanObj {",
    "  return lean_array_get_core(a, i);",
    "}"
  ]),
  ("lean_mk_empty_array_with_capacity", joinLines [
    "inline fn lean_mk_empty_array_with_capacity(capacity: LeanObj) LeanObj {",
    "  if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();",
    "  return lean_alloc_array(@as(usize, 0), lean_unbox(capacity));",
    "}"
  ]),
  ("lean_nat_dec_le", joinLines [
    "inline fn lean_nat_dec_le(a1: LeanObj, a2: LeanObj) u8 {",
    "  return @intFromBool(lean_nat_le(a1, a2));",
    "}"
  ]),
  ("lean_nat_dec_lt", joinLines [
    "inline fn lean_nat_dec_lt(a1: LeanObj, a2: LeanObj) u8 {",
    "  return @intFromBool(lean_nat_lt(a1, a2));",
    "}"
  ]),
  ("lean_uint32_to_nat", joinLines [
    "inline fn lean_uint32_to_nat(a: u32) LeanObj {",
    "  return lean_usize_to_nat(@as(usize, a));",
    "}"
  ]),
  ("lean_uint32_add", joinLines [
    "inline fn lean_uint32_add(a1: u32, a2: u32) u32 {",
    "  return a1 +% a2;",
    "}"
  ]),
  ("lean_usize_of_nat", joinLines [
    "inline fn lean_usize_of_nat(a: LeanObj) usize {",
    "  if (lean_is_scalar(a)) {",
    "    return lean_unbox(a);",
    "  } else {",
    "    return lean_usize_of_big_nat(a);",
    "  }",
    "}"
  ]),
  ("lean_usize_add", joinLines [
    "inline fn lean_usize_add(a1: usize, a2: usize) usize {",
    "  return a1 +% a2;",
    "}"
  ]),
  ("lean_usize_dec_eq", joinLines [
    "inline fn lean_usize_dec_eq(a1: usize, a2: usize) u8 {",
    "  return @intFromBool(a1 == a2);",
    "}"
  ]),
  ("lean_string_size", joinLines [
    "inline fn lean_string_size(s: LeanObj) usize {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(s));",
    "  return @as(*usize, @ptrCast(@alignCast(bytes + @sizeOf(lean_object)))).*;",
    "}"
  ]),
  ("lean_string_utf8_get_fast", joinLines [
    "inline fn lean_string_utf8_get_fast(s: LeanObj, i: LeanObj) u32 {",
    "  const str: [*:0]const u8 = @ptrCast(lean_heap_obj(s));",
    "  const idx = lean_unbox(i);",
    "  const c = str[idx];",
    "  if ((c & 0x80) == 0) return @as(u32, c);",
    "  return lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c);",
    "}"
  ]),
  ("lean_string_utf8_next_fast", joinLines [
    "inline fn lean_string_utf8_next_fast(s: LeanObj, i: LeanObj) LeanObj {",
    "  const str: [*:0]const u8 = @ptrCast(lean_heap_obj(s));",
    "  const idx = lean_unbox(i);",
    "  const c = str[idx];",
    "  if ((c & 0x80) == 0) return lean_box(idx + 1);",
    "  return lean_string_utf8_next_fast_cold(idx, c);",
    "}"
  ]),
  ("lean_string_utf8_at_end", joinLines [
    "inline fn lean_string_utf8_at_end(s: LeanObj, i: LeanObj) u8 {",
    "  return @intFromBool(!lean_is_scalar(i) or lean_unbox(i) >= lean_string_size(s) - 1);",
    "}"
  ]),
  ("lean_string_dec_lt", joinLines [
    "inline fn lean_string_dec_lt(s1: LeanObj, s2: LeanObj) u8 {",
    "  return @intFromBool(lean_string_lt(s1, s2));",
    "}"
  ]),
  ("lean_string_utf8_byte_size", joinLines [
    "inline fn lean_string_utf8_byte_size(s: LeanObj) LeanObj {",
    "  return lean_box(lean_string_size(s) - 1);",
    "}"
  ]),
  ("lean_string_length", joinLines [
    "inline fn lean_string_length(s: LeanObj) LeanObj {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(s));",
    "  return lean_box(@as(*usize, @ptrCast(@alignCast(bytes + @sizeOf(lean_object) + 2 * @sizeOf(usize)))).*);",
    "}"
  ]),
  ("lean_string_dec_eq", joinLines [
    "inline fn lean_string_dec_eq(s1: LeanObj, s2: LeanObj) u8 {",
    "  return @intFromBool(s1 == s2 or (lean_string_size(s1) == lean_string_size(s2) and lean_string_eq_cold(s1, s2)));",
    "}"
  ]),
  ("lean_string_is_valid_pos", joinLines [
    "inline fn lean_string_is_valid_pos(s: LeanObj, i: LeanObj) u8 {",
    "  if (!lean_is_scalar(i)) return 0;",
    "  const idx = lean_unbox(i);",
    "  const size = lean_string_size(s) - 1;",
    "  if (idx >= size) return 0;",
    "  const str: [*:0]const u8 = @ptrCast(lean_heap_obj(s));",
    "  return @intFromBool((str[idx] & 0x80) == 0 or (str[idx] & 0xC0) != 0x80);",
    "}"
  ]),
  ("lean_ctor_scalar_base", joinLines [
    "inline fn lean_ctor_scalar_base(o: LeanObj) [*]u8 {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(o));",
    "  return bytes + @sizeOf(lean_object) + @sizeOf(usize) * @as(usize, lean_ctor_num_objs(o));",
    "}"
  ]),
  ("lean_ctor_set", joinLines [
    "inline fn lean_ctor_set(o: LeanObj, i: c_uint, v: LeanObj) void {",
    "  std.debug.assert(i < lean_ctor_num_objs(o));",
    "  lean_ctor_obj_cptr(o)[@as(usize, i)] = v;",
    "}"
  ]),
  ("lean_ctor_release", joinLines [
    "inline fn lean_ctor_release(o: LeanObj, i: c_uint) void {",
    "  std.debug.assert(i < lean_ctor_num_objs(o));",
    "  const slots = lean_ctor_obj_cptr(o);",
    "  lean_dec(slots[@as(usize, i)]);",
    "  slots[@as(usize, i)] = lean_box(0);",
    "}"
  ]),
  ("lean_ctor_get_usize", joinLines [
    "inline fn lean_ctor_get_usize(o: LeanObj, i: c_uint) usize {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*usize, @ptrCast(@alignCast(base + @sizeOf(usize) * @as(usize, i)))).*;",
    "}"
  ]),
  ("lean_ctor_set_usize", joinLines [
    "inline fn lean_ctor_set_usize(o: LeanObj, i: c_uint, v: usize) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*usize, @ptrCast(@alignCast(base + @sizeOf(usize) * @as(usize, i)))).* = v;",
    "}"
  ]),
  ("lean_ctor_get_uint8", joinLines [
    "inline fn lean_ctor_get_uint8(o: LeanObj, offset: c_uint) u8 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*u8, @ptrCast(base + offset)).*;",
    "}"
  ]),
  ("lean_ctor_get_uint16", joinLines [
    "inline fn lean_ctor_get_uint16(o: LeanObj, offset: c_uint) u16 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*u16, @ptrCast(@alignCast(base + offset))).*;",
    "}"
  ]),
  ("lean_ctor_get_uint32", joinLines [
    "inline fn lean_ctor_get_uint32(o: LeanObj, offset: c_uint) u32 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*u32, @ptrCast(@alignCast(base + offset))).*;",
    "}"
  ]),
  ("lean_ctor_get_uint64", joinLines [
    "inline fn lean_ctor_get_uint64(o: LeanObj, offset: c_uint) u64 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*u64, @ptrCast(@alignCast(base + offset))).*;",
    "}"
  ]),
  ("lean_ctor_get_float", joinLines [
    "inline fn lean_ctor_get_float(o: LeanObj, offset: c_uint) f64 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*f64, @ptrCast(@alignCast(base + offset))).*;",
    "}"
  ]),
  ("lean_ctor_get_float32", joinLines [
    "inline fn lean_ctor_get_float32(o: LeanObj, offset: c_uint) f32 {",
    "  const base = lean_ctor_scalar_base(o);",
    "  return @as(*f32, @ptrCast(@alignCast(base + offset))).*;",
    "}"
  ]),
  ("lean_ctor_set_uint8", joinLines [
    "inline fn lean_ctor_set_uint8(o: LeanObj, offset: c_uint, v: u8) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*u8, @ptrCast(base + offset)).* = v;",
    "}"
  ]),
  ("lean_ctor_set_uint16", joinLines [
    "inline fn lean_ctor_set_uint16(o: LeanObj, offset: c_uint, v: u16) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*u16, @ptrCast(@alignCast(base + offset))).* = v;",
    "}"
  ]),
  ("lean_ctor_set_uint32", joinLines [
    "inline fn lean_ctor_set_uint32(o: LeanObj, offset: c_uint, v: u32) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*u32, @ptrCast(@alignCast(base + offset))).* = v;",
    "}"
  ]),
  ("lean_ctor_set_uint64", joinLines [
    "inline fn lean_ctor_set_uint64(o: LeanObj, offset: c_uint, v: u64) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*u64, @ptrCast(@alignCast(base + offset))).* = v;",
    "}"
  ]),
  ("lean_ctor_set_float", joinLines [
    "inline fn lean_ctor_set_float(o: LeanObj, offset: c_uint, v: f64) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*f64, @ptrCast(@alignCast(base + offset))).* = v;",
    "}"
  ]),
  ("lean_ctor_set_float32", joinLines [
    "inline fn lean_ctor_set_float32(o: LeanObj, offset: c_uint, v: f32) void {",
    "  const base = lean_ctor_scalar_base(o);",
    "  @as(*f32, @ptrCast(@alignCast(base + offset))).* = v;",
    "}"
  ]),
  ("lean_closure_obj_cptr", joinLines [
    "inline fn lean_closure_obj_cptr(o: LeanObj) [*]LeanObj {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(o));",
    "  return @ptrCast(@alignCast(bytes + @sizeOf(lean_closure_object)));",
    "}"
  ]),
  ("lean_closure_set", joinLines [
    "inline fn lean_closure_set(o: LeanObj, i: c_uint, v: LeanObj) void {",
    "  lean_closure_obj_cptr(o)[@as(usize, i)] = v;",
    "}"
  ]),
  ("lean_dec_ref_n", joinLines [
    "inline fn lean_dec_ref_n(o: LeanObj, n: usize) void {",
    "  for (0..n) |_| { lean_dec_ref(o); }",
    "}"
  ]),
  ("lean_dec_n", joinLines [
    "inline fn lean_dec_n(o: LeanObj, n: usize) void {",
    "  if (!lean_is_scalar(o)) lean_dec_ref_n(o, n);",
    "}"
  ]),
  ("lean_inc_n", joinLines [
    "inline fn lean_inc_n(o: LeanObj, n: usize) void {",
    "  if (!lean_is_scalar(o)) lean_inc_ref_n(o, n);",
    "}"
  ]),
  ("lean_is_exclusive", joinLines [
    "inline fn lean_is_exclusive(o: LeanObj) bool {",
    "  return !lean_is_scalar(o) and lean_heap_obj(o).m_rc == 1;",
    "}"
  ]),
  ("lean_alloc_closure", joinLines [
    "inline fn lean_alloc_closure(fun: *const anyopaque, arity: c_uint, num_fixed: c_uint) LeanObj {",
    "  std.debug.assert(arity > 0 and num_fixed < arity);",
    "  const total = lean_usize_add_checked(",
    "    @sizeOf(lean_closure_object), lean_usize_mul_checked(@sizeOf(*anyopaque), @as(usize, num_fixed))",
    "  );",
    "  const o: *lean_closure_object = @ptrCast(@alignCast(lean_alloc_object(total)));",
    "  lean_set_st_header(@ptrCast(o), @as(c_uint, 245), @as(c_uint, 0));",
    "  o.m_fun = @constCast(fun);",
    "  o.m_arity = @as(u16, @intCast(arity));",
    "  o.m_num_fixed = @as(u16, @intCast(num_fixed));",
    "  return @ptrCast(o);",
    "}"
  ]),
  ("lean_array_get_borrowed", joinLines [
    "inline fn lean_array_get_borrowed(def_val: LeanObj, a: LeanObj, i: LeanObj) LeanObj {",
    "  if (lean_is_scalar(i)) {",
    "    const idx = lean_unbox(i);",
    "    if (idx < lean_array_size(a)) {",
    "      return lean_array_get_core(a, idx);",
    "    }",
    "  }",
    "  lean_inc(def_val);",
    "  return lean_array_get_panic(def_val);",
    "}"
  ]),
  ("lean_del_object", joinLines [
    "inline fn lean_del_object(o: LeanObj) void {",
    "  if (!lean_is_scalar(o)) lean_free_object(o);",
    "}"
  ]),
  ("lean_box_uint32", joinLines [
    "inline fn lean_box_uint32(value: u32) LeanObj {",
    "  if (value <= LeanMaxSmallNat) { return lean_box(@as(usize, value)); }",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 0), @as(usize, 4));",
    "  lean_ctor_set_uint32(r, @as(c_uint, 0), value);",
    "  return r;",
    "}"
  ]),
  ("lean_box_uint64", joinLines [
    "inline fn lean_box_uint64(value: u64) LeanObj {",
    "  if (value <= LeanMaxSmallNat) { return lean_box(@as(usize, @intCast(value))); }",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 0), @as(usize, 8));",
    "  lean_ctor_set_uint64(r, @as(c_uint, 0), value);",
    "  return r;",
    "}"
  ]),
  ("lean_box_usize", joinLines [
    "inline fn lean_box_usize(value: usize) LeanObj {",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 0), @sizeOf(usize));",
    "  lean_ctor_set_usize(r, @as(c_uint, 0), value);",
    "  return r;",
    "}"
  ]),
  ("lean_box_float", joinLines [
    "inline fn lean_box_float(value: f64) LeanObj {",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 0), @as(usize, 8));",
    "  lean_ctor_set_float(r, @as(c_uint, 0), value);",
    "  return r;",
    "}"
  ]),
  ("lean_box_float32", joinLines [
    "inline fn lean_box_float32(value: f32) LeanObj {",
    "  const r = lean_alloc_ctor(@as(c_uint, 0), @as(c_uint, 0), @as(usize, 4));",
    "  lean_ctor_set_float32(r, @as(c_uint, 0), value);",
    "  return r;",
    "}"
  ]),
  ("lean_unbox_usize", joinLines [
    "inline fn lean_unbox_usize(o: LeanObj) usize {",
    "  return lean_ctor_get_usize(o, @as(c_uint, 0));",
    "}"
  ]),
  ("lean_unbox_uint64", joinLines [
    "inline fn lean_unbox_uint64(o: LeanObj) u64 {",
    "  return lean_ctor_get_uint64(o, @as(c_uint, 0));",
    "}"
  ]),
  ("lean_unbox_float", joinLines [
    "inline fn lean_unbox_float(o: LeanObj) f64 {",
    "  return lean_ctor_get_float(o, @as(c_uint, 0));",
    "}"
  ]),
  ("lean_unbox_float32", joinLines [
    "inline fn lean_unbox_float32(o: LeanObj) f32 {",
    "  return lean_ctor_get_float32(o, @as(c_uint, 0));",
    "}"
  ]),
  ("lean_byte_array_size", joinLines [
    "inline fn lean_byte_array_size(a: LeanObj) LeanObj {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(a));",
    "  return lean_box(@as(*usize, @ptrCast(@alignCast(bytes + @sizeOf(lean_object)))).*);",
    "}"
  ]),
  ("lean_byte_array_fget", joinLines [
    "inline fn lean_byte_array_fget(a: LeanObj, i: LeanObj) u8 {",
    "  const bytes: [*]u8 = @ptrCast(lean_heap_obj(a));",
    "  const data = bytes + @sizeOf(lean_object) + 2 * @sizeOf(usize);",
    "  return data[lean_unbox(i)];",
    "}"
  ]),
  ("lean_string_get_byte_fast", joinLines [
    "inline fn lean_string_get_byte_fast(s: LeanObj, i: LeanObj) u8 {",
    "  const str: [*:0]const u8 = @ptrCast(lean_heap_obj(s));",
    "  return str[lean_unbox(i)];",
    "}"
  ]),
  ("lean_uint8_land", joinLines [
    "inline fn lean_uint8_land(a1: u8, a2: u8) u8 {",
    "  return a1 & a2;",
    "}"
  ]),
  ("lean_uint8_dec_eq", joinLines [
    "inline fn lean_uint8_dec_eq(a1: u8, a2: u8) u8 {",
    "  return @intFromBool(a1 == a2);",
    "}"
  ]),
  ("lean_uint8_to_uint32", joinLines [
    "inline fn lean_uint8_to_uint32(a: u8) u32 {",
    "  return @as(u32, a);",
    "}"
  ]),
  ("lean_uint32_dec_eq", joinLines [
    "inline fn lean_uint32_dec_eq(a1: u32, a2: u32) u8 {",
    "  return @intFromBool(a1 == a2);",
    "}"
  ]),
  ("lean_uint32_dec_le", joinLines [
    "inline fn lean_uint32_dec_le(a1: u32, a2: u32) u8 {",
    "  return @intFromBool(a1 <= a2);",
    "}"
  ]),
  ("lean_uint32_dec_lt", joinLines [
    "inline fn lean_uint32_dec_lt(a1: u32, a2: u32) u8 {",
    "  return @intFromBool(a1 < a2);",
    "}"
  ]),
  ("lean_uint32_lor", joinLines [
    "inline fn lean_uint32_lor(a1: u32, a2: u32) u32 {",
    "  return a1 | a2;",
    "}"
  ]),
  ("lean_uint32_shift_left", joinLines [
    "inline fn lean_uint32_shift_left(a1: u32, a2: u32) u32 {",
    "  return a1 << @as(u5, @truncate(a2));",
    "}"
  ]),
]

private def bignumExternHelperEntries : List (String × String) := [
  ("lean_nat_big_succ", "extern fn lean_nat_big_succ(a: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_big_add", "extern fn lean_nat_big_add(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_big_sub", "extern fn lean_nat_big_sub(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_overflow_mul", "extern fn lean_nat_overflow_mul(a1: usize, a2: usize) callconv(.c) LeanObj;"),
  ("lean_nat_big_mul", "extern fn lean_nat_big_mul(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_big_div", "extern fn lean_nat_big_div(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_big_mod", "extern fn lean_nat_big_mod(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_nat_big_eq", "extern fn lean_nat_big_eq(a1: LeanObj, a2: LeanObj) callconv(.c) bool;"),
  ("lean_nat_big_le", "extern fn lean_nat_big_le(a1: LeanObj, a2: LeanObj) callconv(.c) bool;"),
  ("lean_nat_big_lt", "extern fn lean_nat_big_lt(a1: LeanObj, a2: LeanObj) callconv(.c) bool;"),
  ("lean_nat_pow", "extern fn lean_nat_pow(a1: LeanObj, a2: LeanObj) callconv(.c) LeanObj;"),
  ("lean_cstr_to_nat", "extern fn lean_cstr_to_nat(s: [*c]const u8) callconv(.c) LeanObj;"),
  ("lean_big_uint64_to_nat", "extern fn lean_big_uint64_to_nat(n: u64) callconv(.c) LeanObj;"),
  ("lean_uint32_of_big_nat", "extern fn lean_uint32_of_big_nat(a: LeanObj) callconv(.c) u32;"),
  ("lean_uint64_of_big_nat", "extern fn lean_uint64_of_big_nat(a: LeanObj) callconv(.c) u64;")
]

private def bignumInlineHelperEntries : List (String × String) := [
  ("lean_uint64_to_nat", joinLines [
    "inline fn lean_uint64_to_nat(n: u64) LeanObj {",
    "  if (n <= LeanMaxSmallNat) {",
    "    return lean_box(@as(usize, @intCast(n)));",
    "  } else {",
    "    return lean_big_uint64_to_nat(n);",
    "  }",
    "}"
  ]),
  ("lean_nat_succ", joinLines [
    "inline fn lean_nat_succ(a: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a)) {",
    "    return lean_usize_to_nat(lean_unbox(a) +% @as(usize, 1));",
    "  } else {",
    "    return lean_nat_big_succ(a);",
    "  }",
    "}"
  ]),
  ("lean_nat_add", joinLines [
    "inline fn lean_nat_add(a1: LeanObj, a2: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    return lean_usize_to_nat(lean_unbox(a1) +% lean_unbox(a2));",
    "  } else {",
    "    return lean_nat_big_add(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_sub", joinLines [
    "inline fn lean_nat_sub(a1: LeanObj, a2: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    const n1 = lean_unbox(a1);",
    "    const n2 = lean_unbox(a2);",
    "    if (n1 < n2) {",
    "      return lean_box(@as(usize, 0));",
    "    } else {",
    "      return lean_box(n1 - n2);",
    "    }",
    "  } else {",
    "    return lean_nat_big_sub(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_mul", joinLines [
    "inline fn lean_nat_mul(a1: LeanObj, a2: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    const n1 = lean_unbox(a1);",
    "    if (n1 == 0) {",
    "      return a1;",
    "    }",
    "    const n2 = lean_unbox(a2);",
    "    const r = n1 *% n2;",
    "    if (r <= LeanMaxSmallNat and r / n1 == n2) {",
    "      return lean_box(r);",
    "    } else {",
    "      return lean_nat_overflow_mul(n1, n2);",
    "    }",
    "  } else {",
    "    return lean_nat_big_mul(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_div", joinLines [
    "inline fn lean_nat_div(a1: LeanObj, a2: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    const n1 = lean_unbox(a1);",
    "    const n2 = lean_unbox(a2);",
    "    if (n2 == 0) {",
    "      return lean_box(@as(usize, 0));",
    "    } else {",
    "      return lean_box(n1 / n2);",
    "    }",
    "  } else {",
    "    return lean_nat_big_div(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_mod", joinLines [
    "inline fn lean_nat_mod(a1: LeanObj, a2: LeanObj) LeanObj {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    const n1 = lean_unbox(a1);",
    "    const n2 = lean_unbox(a2);",
    "    if (n2 == 0) {",
    "      return lean_box(n1);",
    "    } else {",
    "      return lean_box(n1 % n2);",
    "    }",
    "  } else {",
    "    return lean_nat_big_mod(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_eq", joinLines [
    "inline fn lean_nat_eq(a1: LeanObj, a2: LeanObj) bool {",
    "  if (lean_is_scalar(a1) and lean_is_scalar(a2)) {",
    "    return a1 == a2;",
    "  } else {",
    "    return lean_nat_big_eq(a1, a2);",
    "  }",
    "}"
  ]),
  ("lean_nat_dec_eq", joinLines [
    "inline fn lean_nat_dec_eq(a1: LeanObj, a2: LeanObj) u8 {",
    "  return @intFromBool(lean_nat_eq(a1, a2));",
    "}"
  ]),
  ("lean_uint32_of_nat", joinLines [
    "inline fn lean_uint32_of_nat(a: LeanObj) u32 {",
    "  if (lean_is_scalar(a)) {",
    "    return @as(u32, @intCast(lean_unbox(a)));",
    "  } else {",
    "    return lean_uint32_of_big_nat(a);",
    "  }",
    "}"
  ]),
  ("lean_uint64_of_nat", joinLines [
    "inline fn lean_uint64_of_nat(a: LeanObj) u64 {",
    "  if (lean_is_scalar(a)) {",
    "    return @as(u64, @intCast(lean_unbox(a)));",
    "  } else {",
    "    return lean_uint64_of_big_nat(a);",
    "  }",
    "}"
  ])
]

public def inlineHelpers : NameMap String :=
  (mvpInlineHelperEntries ++ bignumExternHelperEntries ++ bignumInlineHelperEntries).foldl (init := {}) fun acc (name, decl) =>
    acc.insert (.str .anonymous name) decl

public def emittedInlineNames : List String :=
  (supportInlineHelperEntries ++ mvpInlineHelperEntries ++ bignumExternHelperEntries ++ bignumInlineHelperEntries).map Prod.fst

public def isInlineHelperName (name : String) : Bool :=
  emittedInlineNames.contains name

public def inlineHelperDecls : List String :=
  supportInlineConsts.map addEvalQuota ++
    (supportInlineHelperEntries ++ mvpInlineHelperEntries ++ bignumExternHelperEntries ++ bignumInlineHelperEntries).map (addEvalQuota ∘ Prod.snd)

end InlineHelpers
