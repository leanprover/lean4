// Lean compiler output
// Module: Lean.Runtime
// Imports: Init.Prelude
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
static lean_object* l_Lean_closureMaxArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgs;
lean_object* lean_libuv_version(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxSmallNat;
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object*);
lean_object* lean_closure_max_args(lean_object*);
LEAN_EXPORT lean_object* l_Lean_libUVVersion;
lean_object* lean_max_small_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object*);
static lean_object* l_Lean_libUVVersion___closed__1;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object*);
static lean_object* l_Lean_maxSmallNat___closed__1;
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
static lean_object* _init_l_Lean_closureMaxArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_closure_max_args(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_closureMaxArgs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_closureMaxArgs___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_maxSmallNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_max_small_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_maxSmallNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxSmallNat___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_libUVVersion___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_libuv_version(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_libUVVersion() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_libUVVersion___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_closureMaxArgs___closed__1 = _init_l_Lean_closureMaxArgs___closed__1();
lean_mark_persistent(l_Lean_closureMaxArgs___closed__1);
l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
lean_mark_persistent(l_Lean_closureMaxArgs);
l_Lean_maxSmallNat___closed__1 = _init_l_Lean_maxSmallNat___closed__1();
lean_mark_persistent(l_Lean_maxSmallNat___closed__1);
l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
lean_mark_persistent(l_Lean_maxSmallNat);
l_Lean_libUVVersion___closed__1 = _init_l_Lean_libUVVersion___closed__1();
lean_mark_persistent(l_Lean_libUVVersion___closed__1);
l_Lean_libUVVersion = _init_l_Lean_libUVVersion();
lean_mark_persistent(l_Lean_libUVVersion);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
