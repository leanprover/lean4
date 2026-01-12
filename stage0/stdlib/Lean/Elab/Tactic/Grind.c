// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: public import Lean.Elab.Tactic.Grind.Main public import Lean.Elab.Tactic.Grind.Basic public import Lean.Elab.Tactic.Grind.BuiltinTactic public import Lean.Elab.Tactic.Grind.ShowState public import Lean.Elab.Tactic.Grind.Have public import Lean.Elab.Tactic.Grind.Trace public import Lean.Elab.Tactic.Grind.Config public import Lean.Elab.Tactic.Grind.Lint public import Lean.Elab.Tactic.Grind.LintExceptions public import Lean.Elab.Tactic.Grind.Annotated
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
lean_object* initialize_Lean_Elab_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_BuiltinTactic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_ShowState(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Have(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Trace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Lint(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_LintExceptions(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Annotated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_BuiltinTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_LintExceptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
