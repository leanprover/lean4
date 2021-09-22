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
LEAN_EXPORT lean_object* l_String_toNat_x21___lambda__1(lean_object*, uint32_t);
extern lean_object* l_instInhabitedNat;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_String_foldlAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_String_toNat_x21___closed__4;
LEAN_EXPORT lean_object* l_String_fromUTF8Unchecked___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21___boxed(lean_object*);
static lean_object* l_String_toNat_x21___closed__1;
static lean_object* l_String_toNat_x21___closed__2;
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object*);
static lean_object* l_String_toNat_x21___closed__3;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_String_toNat_x21___closed__5;
LEAN_EXPORT lean_object* l_String_toNat_x21___lambda__1(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_uint32_to_nat(x_2);
x_6 = lean_unsigned_to_nat(48u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_String_toNat_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.String.Extra");
return x_1;
}
}
static lean_object* _init_l_String_toNat_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String.toNat!");
return x_1;
}
}
static lean_object* _init_l_String_toNat_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat expected");
return x_1;
}
}
static lean_object* _init_l_String_toNat_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_toNat_x21___closed__1;
x_2 = l_String_toNat_x21___closed__2;
x_3 = lean_unsigned_to_nat(17u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_String_toNat_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_String_toNat_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toNat_x21___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object* x_1) {
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
x_7 = l_String_toNat_x21___closed__5;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_foldlAux_loop___rarg(x_7, x_1, x_6, x_8, x_8);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_toNat_x21___lambda__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toNat_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8Unchecked___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_from_utf8_unchecked(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* initialize_Init_Data_String_Extra(lean_object* w) {
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
l_String_toNat_x21___closed__1 = _init_l_String_toNat_x21___closed__1();
lean_mark_persistent(l_String_toNat_x21___closed__1);
l_String_toNat_x21___closed__2 = _init_l_String_toNat_x21___closed__2();
lean_mark_persistent(l_String_toNat_x21___closed__2);
l_String_toNat_x21___closed__3 = _init_l_String_toNat_x21___closed__3();
lean_mark_persistent(l_String_toNat_x21___closed__3);
l_String_toNat_x21___closed__4 = _init_l_String_toNat_x21___closed__4();
lean_mark_persistent(l_String_toNat_x21___closed__4);
l_String_toNat_x21___closed__5 = _init_l_String_toNat_x21___closed__5();
lean_mark_persistent(l_String_toNat_x21___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
