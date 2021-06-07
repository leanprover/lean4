// Lean compiler output
// Module: Lean.Runtime
// Imports: Init
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
lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object*);
lean_object* l_Lean_closureMaxArgs;
lean_object* l_Lean_maxSmallNat___closed__1;
lean_object* l_Lean_maxSmallNatFn___boxed(lean_object*);
lean_object* l_Lean_maxSmallNat;
lean_object* lean_max_small_nat(lean_object*);
lean_object* l_Lean_closureMaxArgs___closed__1;
lean_object* lean_closure_max_args(lean_object*);
lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_closure_max_args(x_1);
return x_2;
}
}
lean_object* l_Lean_maxSmallNatFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_max_small_nat(x_1);
return x_2;
}
}
#define _init_l_Lean_closureMaxArgs___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_box(0);\
x_2 = lean_closure_max_args(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_closureMaxArgs___closed__1_end;\
}\
l_Lean_closureMaxArgs___closed__1_end: ((void) 0);}
#define _init_l_Lean_closureMaxArgs(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_closureMaxArgs___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_closureMaxArgs_end;\
}\
l_Lean_closureMaxArgs_end: ((void) 0);}
#define _init_l_Lean_maxSmallNat___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_box(0);\
x_2 = lean_max_small_nat(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_maxSmallNat___closed__1_end;\
}\
l_Lean_maxSmallNat___closed__1_end: ((void) 0);}
#define _init_l_Lean_maxSmallNat(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_maxSmallNat___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_maxSmallNat_end;\
}\
l_Lean_maxSmallNat_end: ((void) 0);}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Runtime(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_closureMaxArgs___closed__1(l_Lean_closureMaxArgs___closed__1);
lean_mark_persistent(l_Lean_closureMaxArgs___closed__1);
_init_l_Lean_closureMaxArgs(l_Lean_closureMaxArgs);
lean_mark_persistent(l_Lean_closureMaxArgs);
_init_l_Lean_maxSmallNat___closed__1(l_Lean_maxSmallNat___closed__1);
lean_mark_persistent(l_Lean_maxSmallNat___closed__1);
_init_l_Lean_maxSmallNat(l_Lean_maxSmallNat);
lean_mark_persistent(l_Lean_maxSmallNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
