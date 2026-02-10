// Lean compiler output
// Module: Lean.Elab.Tactic.Conv
// Imports: public import Lean.Elab.Tactic.Conv.Basic public import Lean.Elab.Tactic.Conv.Congr public import Lean.Elab.Tactic.Conv.Rewrite public import Lean.Elab.Tactic.Conv.Change public import Lean.Elab.Tactic.Conv.Lets public import Lean.Elab.Tactic.Conv.Simp public import Lean.Elab.Tactic.Conv.Pattern public import Lean.Elab.Tactic.Conv.Delta public import Lean.Elab.Tactic.Conv.Unfold public import Lean.Elab.Tactic.Conv.Cbv
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
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Delta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Cbv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
