// Lean compiler output
// Module: Init.Data.Char.Lemmas
// Imports: Init.Data.Char.Basic Init.Data.UInt.Lemmas
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
LEAN_EXPORT lean_object* l_String_csize(uint32_t);
LEAN_EXPORT lean_object* l_String_csize___boxed(lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_String_csize(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_csize___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_csize(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
