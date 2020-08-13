// Lean compiler output
// Module: Lean.Meta.EqnCompiler
// Imports: Init Lean.Meta.EqnCompiler.MatchPattern Lean.Meta.EqnCompiler.DepElim Lean.Meta.EqnCompiler.CaseValues Lean.Meta.EqnCompiler.CaseArraySizes
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
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_9__withAltsAux___main___rarg___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_1__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_9__withAltsAux___main___rarg___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_MatchPattern(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_DepElim(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_CaseValues(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_CaseArraySizes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_EqnCompiler(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_MatchPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_DepElim(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_CaseValues(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_CaseArraySizes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_EqnCompiler_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
