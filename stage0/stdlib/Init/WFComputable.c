// Lean compiler output
// Module: Init.WFComputable
// Imports: public import Init.WF import Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Acc_recC___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_3(x_1, x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Acc_recC___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Acc_recC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Acc_recC___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Acc_recC___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Acc_recC___redArg(x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Acc_recC___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Acc_recC___redArg(x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Acc_recC___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Acc_recC___redArg(x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_WellFounded_fixC___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_fixC___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_fixC___redArg(x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_WFComputable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
