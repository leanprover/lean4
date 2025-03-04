// Lean compiler output
// Module: Lake.DSL.Extensions
// Imports: Lean.Environment
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
LEAN_EXPORT lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Lake_optsExt;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_35_(lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1;
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4_(lean_object*);
static lean_object* _init_l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1;
x_4 = 2;
x_5 = l_Lean_registerEnvExtension___rarg(x_3, x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_35_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1;
x_4 = 2;
x_5 = l_Lean_registerEnvExtension___rarg(x_3, x_2, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1 = _init_l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1();
lean_mark_persistent(l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4____closed__1);
if (builtin) {res = l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_dirExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_dirExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lake_initFn____x40_Lake_DSL_Extensions___hyg_35_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_optsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_optsExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
