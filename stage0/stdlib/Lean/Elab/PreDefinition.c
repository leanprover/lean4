// Lean compiler output
// Module: Lean.Elab.PreDefinition
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural Lean.Elab.PreDefinition.Main Lean.Elab.PreDefinition.MkInhabitant Lean.Elab.PreDefinition.WF Lean.Elab.PreDefinition.Eqns Lean.Elab.PreDefinition.Nonrec.Eqns Lean.Elab.PreDefinition.EqUnfold
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
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Nonrec_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_EqUnfold(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Nonrec_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_EqUnfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
