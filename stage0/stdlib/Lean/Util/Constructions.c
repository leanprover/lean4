// Lean compiler output
// Module: Lean.Util.Constructions
// Imports: Init Lean.Environment
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
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l_Lean_mkRecOn___boxed(lean_object*, lean_object*);
lean_object* lean_mk_ibelow(lean_object*, lean_object*);
lean_object* lean_mk_below(lean_object*, lean_object*);
lean_object* lean_mk_brec_on(lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusion___boxed(lean_object*, lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_mkIBelow___boxed(lean_object*, lean_object*);
lean_object* lean_mk_binduction_on(lean_object*, lean_object*);
lean_object* l_Lean_mkBelow___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkBInductionOn___boxed(lean_object*, lean_object*);
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Lean_mkBRecOn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_cases_on(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkRecOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_rec_on(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkNoConfusion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_no_confusion(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkBelow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_below(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkIBelow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_ibelow(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkBRecOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_brec_on(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkBInductionOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_binduction_on(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Constructions(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
