// Lean compiler output
// Module: Init.Data.Option.Coe
// Imports: public import Init.Coe
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
static lean_object* l_optionCoe___closed__0;
LEAN_EXPORT lean_object* l_optionCoe(lean_object*);
LEAN_EXPORT lean_object* l_optionCoe___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_optionCoe___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_optionCoe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_optionCoe___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_optionCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_optionCoe___closed__0;
return x_2;
}
}
lean_object* initialize_Init_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_optionCoe___closed__0 = _init_l_optionCoe___closed__0();
lean_mark_persistent(l_optionCoe___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
