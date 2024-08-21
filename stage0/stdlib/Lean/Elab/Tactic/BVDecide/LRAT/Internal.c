// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.LRAT.Internal
// Imports: Lean.Elab.Tactic.BVDecide.LRAT.Internal.Actions Lean.Elab.Tactic.BVDecide.LRAT.Internal.Assignment Lean.Elab.Tactic.BVDecide.LRAT.Internal.CNF Lean.Elab.Tactic.BVDecide.LRAT.Internal.Formula Lean.Elab.Tactic.BVDecide.LRAT.Internal.Entails Lean.Elab.Tactic.BVDecide.LRAT.Internal.Assignment Lean.Elab.Tactic.BVDecide.LRAT.Internal.Clause Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATChecker Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound Lean.Elab.Tactic.BVDecide.LRAT.Internal.PosFin Lean.Elab.Tactic.BVDecide.LRAT.Internal.Convert
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
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_CNF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Formula(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Assignment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_CNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Formula(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Entails(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Assignment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Clause(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_PosFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Internal_Convert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
