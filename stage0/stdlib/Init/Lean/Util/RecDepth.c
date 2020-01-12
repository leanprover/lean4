// Lean compiler output
// Module: Init.Lean.Util.RecDepth
// Imports: Init.Lean.Data.Options
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
lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_getMaxRecDepth___boxed(lean_object*);
lean_object* l_Lean_getMaxRecDepth___closed__2;
lean_object* l_Lean_getMaxRecDepth___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_maxRecDepthErrorMessage___closed__1;
lean_object* l_Lean_maxRecDepth(lean_object*);
lean_object* l_Lean_maxRecDepth___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_maxRecDepth___closed__2;
lean_object* l_Lean_maxRecDepth___closed__1;
lean_object* l_Lean_defaultMaxRecDepth;
lean_object* _init_l_Lean_defaultMaxRecDepth() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(512u);
return x_1;
}
}
lean_object* _init_l_Lean_getMaxRecDepth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxRecDepth");
return x_1;
}
}
lean_object* _init_l_Lean_getMaxRecDepth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getMaxRecDepth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_getMaxRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getMaxRecDepth___closed__2;
x_3 = l_Lean_defaultMaxRecDepth;
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getMaxRecDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getMaxRecDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_maxRecDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_defaultMaxRecDepth;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_maxRecDepth___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum recursion depth for many Lean procedures");
return x_1;
}
}
lean_object* _init_l_Lean_maxRecDepth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_maxRecDepth___closed__1;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_maxRecDepth___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_maxRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getMaxRecDepth___closed__2;
x_3 = l_Lean_maxRecDepth___closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_maxRecDepthErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)");
return x_1;
}
}
lean_object* _init_l_Lean_maxRecDepthErrorMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepthErrorMessage___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Lean_Data_Options(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_RecDepth(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_Options(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_defaultMaxRecDepth = _init_l_Lean_defaultMaxRecDepth();
lean_mark_persistent(l_Lean_defaultMaxRecDepth);
l_Lean_getMaxRecDepth___closed__1 = _init_l_Lean_getMaxRecDepth___closed__1();
lean_mark_persistent(l_Lean_getMaxRecDepth___closed__1);
l_Lean_getMaxRecDepth___closed__2 = _init_l_Lean_getMaxRecDepth___closed__2();
lean_mark_persistent(l_Lean_getMaxRecDepth___closed__2);
l_Lean_maxRecDepth___closed__1 = _init_l_Lean_maxRecDepth___closed__1();
lean_mark_persistent(l_Lean_maxRecDepth___closed__1);
l_Lean_maxRecDepth___closed__2 = _init_l_Lean_maxRecDepth___closed__2();
lean_mark_persistent(l_Lean_maxRecDepth___closed__2);
l_Lean_maxRecDepth___closed__3 = _init_l_Lean_maxRecDepth___closed__3();
lean_mark_persistent(l_Lean_maxRecDepth___closed__3);
res = l_Lean_maxRecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_maxRecDepthErrorMessage___closed__1 = _init_l_Lean_maxRecDepthErrorMessage___closed__1();
lean_mark_persistent(l_Lean_maxRecDepthErrorMessage___closed__1);
l_Lean_maxRecDepthErrorMessage = _init_l_Lean_maxRecDepthErrorMessage();
lean_mark_persistent(l_Lean_maxRecDepthErrorMessage);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
