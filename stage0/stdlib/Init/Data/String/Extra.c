// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: Init.Control.Except Init.Data.ByteArray Init.Util
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
extern lean_object* l_instInhabitedNat;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_foldlAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toUTF8___boxed(lean_object*);
lean_object* l_String_toNat_x21___closed__4;
extern lean_object* l_String_toNat_x3f___closed__1;
lean_object* l_String_fromUTF8Unchecked___boxed(lean_object*);
lean_object* l_String_toNat_x21___boxed(lean_object*);
lean_object* l_String_toNat_x21___closed__1;
lean_object* l_String_toNat_x21___closed__2;
lean_object* l_String_toNat_x21(lean_object*);
lean_object* l_String_toNat_x21___closed__3;
#define _init_l_String_toNat_x21___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Init.Data.String.Extra");\
__INIT_VAR__ = x_1; goto l_String_toNat_x21___closed__1_end;\
}\
l_String_toNat_x21___closed__1_end: ((void) 0);}
#define _init_l_String_toNat_x21___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("String.toNat!");\
__INIT_VAR__ = x_1; goto l_String_toNat_x21___closed__2_end;\
}\
l_String_toNat_x21___closed__2_end: ((void) 0);}
#define _init_l_String_toNat_x21___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Nat expected");\
__INIT_VAR__ = x_1; goto l_String_toNat_x21___closed__3_end;\
}\
l_String_toNat_x21___closed__3_end: ((void) 0);}
#define _init_l_String_toNat_x21___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; \
x_1 = l_String_toNat_x21___closed__1;\
x_2 = l_String_toNat_x21___closed__2;\
x_3 = lean_unsigned_to_nat(17u);\
x_4 = lean_unsigned_to_nat(4u);\
x_5 = l_String_toNat_x21___closed__3;\
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);\
__INIT_VAR__ = x_6; goto l_String_toNat_x21___closed__4_end;\
}\
l_String_toNat_x21___closed__4_end: ((void) 0);}
lean_object* l_String_toNat_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_isNat(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_instInhabitedNat;
x_4 = l_String_toNat_x21___closed__4;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = l_String_toNat_x3f___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_foldlAux_loop___rarg(x_7, x_1, x_6, x_8, x_8);
lean_dec(x_6);
return x_9;
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
lean_object* l_String_fromUTF8Unchecked___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_from_utf8_unchecked(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_toUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_to_utf8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Control_Except(lean_object*);
lean_object* initialize_Init_Data_ByteArray(lean_object*);
lean_object* initialize_Init_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_String_Extra(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_String_toNat_x21___closed__1(l_String_toNat_x21___closed__1);
lean_mark_persistent(l_String_toNat_x21___closed__1);
_init_l_String_toNat_x21___closed__2(l_String_toNat_x21___closed__2);
lean_mark_persistent(l_String_toNat_x21___closed__2);
_init_l_String_toNat_x21___closed__3(l_String_toNat_x21___closed__3);
lean_mark_persistent(l_String_toNat_x21___closed__3);
_init_l_String_toNat_x21___closed__4(l_String_toNat_x21___closed__4);
lean_mark_persistent(l_String_toNat_x21___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
