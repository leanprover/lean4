// Lean compiler output
// Module: Init.Data.Vector.FinRange
// Imports: Init.Data.Array.FinRange Init.Data.Vector.OfFn
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
LEAN_EXPORT lean_object* l_Vector_finRange(lean_object*);
static lean_object* l_Vector_finRange___closed__1;
lean_object* l_Array_ofFn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finRange___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_finRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_finRange___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Vector_finRange___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Vector_finRange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Vector_finRange___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Vector_finRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Vector_finRange___closed__1;
x_3 = l_Array_ofFn___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Vector_finRange___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Vector_finRange___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Vector_finRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Vector_finRange(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_FinRange(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_OfFn(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_FinRange(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_FinRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Vector_finRange___closed__1 = _init_l_Vector_finRange___closed__1();
lean_mark_persistent(l_Vector_finRange___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
