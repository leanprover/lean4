// Lean compiler output
// Module: Lean.Elab.BuiltinDo
// Imports: public import Lean.Elab.BuiltinDo.Basic public import Lean.Elab.BuiltinDo.Let public import Lean.Elab.BuiltinDo.Match public import Lean.Elab.BuiltinDo.MatchExpr public import Lean.Elab.BuiltinDo.If public import Lean.Elab.BuiltinDo.Jump public import Lean.Elab.BuiltinDo.Misc public import Lean.Elab.BuiltinDo.For public import Lean.Elab.BuiltinDo.TryCatch
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
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Match(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_MatchExpr(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Jump(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Misc(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_TryCatch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Jump(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Misc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
