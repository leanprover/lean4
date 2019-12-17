// Lean compiler output
// Module: Init.Lean.Elab
// Imports: Init.Lean.Elab.Import Init.Lean.Elab.Exception Init.Lean.Elab.ElabStrategyAttrs Init.Lean.Elab.Command Init.Lean.Elab.Term Init.Lean.Elab.Quotation Init.Lean.Elab.Frontend Init.Lean.Elab.BuiltinNotation
#include "runtime/lean.h"
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
lean_object* initialize_Init_Lean_Elab_Import(lean_object*);
lean_object* initialize_Init_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Init_Lean_Elab_ElabStrategyAttrs(lean_object*);
lean_object* initialize_Init_Lean_Elab_Command(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object*);
lean_object* initialize_Init_Lean_Elab_Frontend(lean_object*);
lean_object* initialize_Init_Lean_Elab_BuiltinNotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_ElabStrategyAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Frontend(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_BuiltinNotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
