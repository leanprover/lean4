// Lean compiler output
// Module: Init.Classical
// Imports: Init.Core
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
lean_object* l_Classical_typeDecidable_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Classical_typeDecidable_match__1(lean_object*, lean_object*);
lean_object* l_Classical_typeDecidable_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Classical_typeDecidable_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
}
}
lean_object* l_Classical_typeDecidable_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Classical_typeDecidable_match__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Classical_typeDecidable_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Classical_typeDecidable_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init_Core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Classical(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
