// Lean compiler output
// Module: Init.Data.ByteArray.Lemmas
// Imports: public import Init.Data.ByteArray.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_byte_array_data(x_1);
x_6 = lean_box(x_3);
x_7 = lean_apply_4(x_4, x_5, x_2, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
