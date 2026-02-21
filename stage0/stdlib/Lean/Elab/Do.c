// Lean compiler output
// Module: Lean.Elab.Do
// Imports: public import Lean.Elab.Do.Basic public import Lean.Elab.Do.InferControlInfo public import Lean.Elab.Do.PatternVar public import Lean.Elab.Do.Control public import Lean.Elab.Do.Switch public import Lean.Elab.Do.Legacy
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
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Control(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Switch(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Legacy(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Switch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
