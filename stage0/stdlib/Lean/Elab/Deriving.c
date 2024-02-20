// Lean compiler output
// Module: Lean.Elab.Deriving
// Imports: Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util Lean.Elab.Deriving.Inhabited Lean.Elab.Deriving.Nonempty Lean.Elab.Deriving.TypeName Lean.Elab.Deriving.BEq Lean.Elab.Deriving.DecEq Lean.Elab.Deriving.Repr Lean.Elab.Deriving.FromToJson Lean.Elab.Deriving.SizeOf Lean.Elab.Deriving.Hashable Lean.Elab.Deriving.Ord
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
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_BEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Inhabited(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Nonempty(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_TypeName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_BEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_DecEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_FromToJson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_SizeOf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
