// Lean compiler output
// Module: Lean.Runtime
// Imports: public import Init.Prelude
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
lean_object* lean_closure_max_args(lean_object*);
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object*);
lean_object* lean_max_small_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object*);
lean_object* lean_libuv_version(lean_object*);
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object*);
static lean_once_cell_t l_Lean_closureMaxArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_closureMaxArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgs;
static lean_once_cell_t l_Lean_maxSmallNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxSmallNat___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxSmallNat;
static lean_once_cell_t l_Lean_libUVVersion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_libUVVersion___closed__0;
LEAN_EXPORT lean_object* l_Lean_libUVVersion;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_closure_max_args(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_max_small_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_libuv_version(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_closureMaxArgs___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_closure_max_args(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_closureMaxArgs(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_closureMaxArgs___closed__0, &l_Lean_closureMaxArgs___closed__0_once, _init_l_Lean_closureMaxArgs___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_maxSmallNat___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_max_small_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_maxSmallNat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_maxSmallNat___closed__0, &l_Lean_maxSmallNat___closed__0_once, _init_l_Lean_maxSmallNat___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_libUVVersion___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_libuv_version(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_libUVVersion(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_libUVVersion___closed__0, &l_Lean_libUVVersion___closed__0_once, _init_l_Lean_libUVVersion___closed__0);
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Runtime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
lean_mark_persistent(l_Lean_closureMaxArgs);
l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
lean_mark_persistent(l_Lean_maxSmallNat);
l_Lean_libUVVersion = _init_l_Lean_libUVVersion();
lean_mark_persistent(l_Lean_libUVVersion);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
