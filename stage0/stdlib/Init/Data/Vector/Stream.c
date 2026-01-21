// Lean compiler output
// Module: Init.Data.Vector.Stream
// Imports: public import Init.Data.Stream public import Init.Data.Vector.Basic
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
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray___boxed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray(lean_object*, lean_object*);
static lean_object* l_Vector_instToStreamSubarray___closed__0;
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Vector_instToStreamSubarray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Vector_instToStreamSubarray___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Vector_instToStreamSubarray___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Vector_instToStreamSubarray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Vector_instToStreamSubarray(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Vector_instToStreamSubarray___closed__0 = _init_l_Vector_instToStreamSubarray___closed__0();
lean_mark_persistent(l_Vector_instToStreamSubarray___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
