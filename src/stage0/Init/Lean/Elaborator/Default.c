// Lean compiler output
// Module: Init.Lean.Elaborator.Default
// Imports: Init.Lean.Elaborator.Basic Init.Lean.Elaborator.ElabStrategyAttrs Init.Lean.Elaborator.Command Init.Lean.Elaborator.PreTerm Init.Lean.Elaborator.Term
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
lean_object* initialize_Init_Lean_Elaborator_Basic(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_ElabStrategyAttrs(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Command(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_PreTerm(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elaborator_Default(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elaborator_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_ElabStrategyAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_PreTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
