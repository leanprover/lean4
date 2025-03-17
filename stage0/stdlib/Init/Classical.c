// Lean compiler output
// Module: Init.Classical
// Imports: Init.PropLemmas
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
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not(lean_object*);
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not___rarg(uint8_t);
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not___rarg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Classical_decidable__of__decidable__not___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Classical_decidable__of__decidable__not___rarg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_PropLemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Classical(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_PropLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
