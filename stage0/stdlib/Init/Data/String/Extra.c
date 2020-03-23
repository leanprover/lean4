// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: Init.Util
#include "runtime/lean.h"
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
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_foldlAux___main___at_String_toNat_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_toNat_x21___boxed(lean_object*);
lean_object* l_String_toNat_x21___closed__1;
lean_object* l_String_toNat_x21___closed__2;
lean_object* l_String_toNat_x21(lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_String_toNat_x21___closed__3;
lean_object* _init_l_String_toNat_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.String.Extra");
return x_1;
}
}
lean_object* _init_l_String_toNat_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat expected");
return x_1;
}
}
lean_object* _init_l_String_toNat_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_String_toNat_x21___closed__1;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_String_toNat_x21___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_String_toNat_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_isNat(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Nat_Inhabited;
x_4 = l_String_toNat_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_foldlAux___main___at_String_toNat_x3f___spec__1(x_1, x_6, x_7, x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l_String_toNat_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toNat_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_String_Extra(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_toNat_x21___closed__1 = _init_l_String_toNat_x21___closed__1();
lean_mark_persistent(l_String_toNat_x21___closed__1);
l_String_toNat_x21___closed__2 = _init_l_String_toNat_x21___closed__2();
lean_mark_persistent(l_String_toNat_x21___closed__2);
l_String_toNat_x21___closed__3 = _init_l_String_toNat_x21___closed__3();
lean_mark_persistent(l_String_toNat_x21___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
