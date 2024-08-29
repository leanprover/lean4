// Lean compiler output
// Module: Std.Tactic.BVDecide.Normalize
// Imports: Std.Tactic.BVDecide.Normalize.BitVec Std.Tactic.BVDecide.Normalize.Bool Std.Tactic.BVDecide.Normalize.Canonicalize Std.Tactic.BVDecide.Normalize.Equal Std.Tactic.BVDecide.Normalize.Prop
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Canonicalize(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Equal(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Prop(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Normalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Canonicalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Equal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
