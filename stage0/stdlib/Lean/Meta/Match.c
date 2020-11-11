// Lean compiler output
// Module: Lean.Meta.Match
// Imports: Init Lean.Meta.Match.MatchPatternAttr Lean.Meta.Match.Match Lean.Meta.Match.CaseValues Lean.Meta.Match.CaseArraySizes
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
extern lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Meta_Match___hyg_3_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseArraySizes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchPatternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseArraySizes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn____x40_Lean_Meta_Match___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
