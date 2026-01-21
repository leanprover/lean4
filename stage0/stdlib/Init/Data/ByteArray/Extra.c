// Lean compiler output
// Module: Init.Data.ByteArray.Extra
// Imports: public import Init.Data.ByteArray.Basic import Init.Data.String.Basic
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
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_ByteArray_toUInt64BE_x21___closed__1;
LEAN_EXPORT lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__1;
uint64_t lean_uint8_to_uint64(uint8_t);
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object*);
LEAN_EXPORT uint64_t l_ByteArray_toUInt64BE_x21(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__0;
static lean_object* l_ByteArray_toUInt64BE_x21___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__3;
static lean_object* l_ByteArray_toUInt64LE_x21___closed__2;
LEAN_EXPORT lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1;
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT uint64_t l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(lean_object*);
static lean_object* _init_l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; 
x_2 = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.ByteArray.Extra", 25, 25);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ByteArray.toUInt64LE!", 21, 21);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: bs.size == 8\n  ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(20u);
x_4 = l_ByteArray_toUInt64LE_x21___closed__1;
x_5 = l_ByteArray_toUInt64LE_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint64_t l_ByteArray_toUInt64LE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint64_t x_6; 
x_5 = l_ByteArray_toUInt64LE_x21___closed__3;
x_6 = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; 
x_7 = lean_unsigned_to_nat(7u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = lean_uint8_to_uint64(x_8);
x_10 = 56;
x_11 = lean_uint64_shift_left(x_9, x_10);
x_12 = lean_unsigned_to_nat(6u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = lean_uint8_to_uint64(x_13);
x_15 = 48;
x_16 = lean_uint64_shift_left(x_14, x_15);
x_17 = lean_uint64_lor(x_11, x_16);
x_18 = lean_unsigned_to_nat(5u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = lean_uint8_to_uint64(x_19);
x_21 = 40;
x_22 = lean_uint64_shift_left(x_20, x_21);
x_23 = lean_uint64_lor(x_17, x_22);
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = lean_uint8_to_uint64(x_25);
x_27 = 32;
x_28 = lean_uint64_shift_left(x_26, x_27);
x_29 = lean_uint64_lor(x_23, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = lean_uint8_to_uint64(x_31);
x_33 = 24;
x_34 = lean_uint64_shift_left(x_32, x_33);
x_35 = lean_uint64_lor(x_29, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = lean_uint8_to_uint64(x_37);
x_39 = 16;
x_40 = lean_uint64_shift_left(x_38, x_39);
x_41 = lean_uint64_lor(x_35, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = lean_uint8_to_uint64(x_43);
x_45 = 8;
x_46 = lean_uint64_shift_left(x_44, x_45);
x_47 = lean_uint64_lor(x_41, x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_byte_array_get(x_1, x_48);
x_50 = lean_uint8_to_uint64(x_49);
x_51 = lean_uint64_lor(x_47, x_50);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_toUInt64LE_x21(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ByteArray.toUInt64BE!", 21, 21);
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(36u);
x_4 = l_ByteArray_toUInt64BE_x21___closed__0;
x_5 = l_ByteArray_toUInt64LE_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint64_t l_ByteArray_toUInt64BE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint64_t x_6; 
x_5 = l_ByteArray_toUInt64BE_x21___closed__1;
x_6 = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = lean_uint8_to_uint64(x_8);
x_10 = 56;
x_11 = lean_uint64_shift_left(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = lean_uint8_to_uint64(x_13);
x_15 = 48;
x_16 = lean_uint64_shift_left(x_14, x_15);
x_17 = lean_uint64_lor(x_11, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = lean_uint8_to_uint64(x_19);
x_21 = 40;
x_22 = lean_uint64_shift_left(x_20, x_21);
x_23 = lean_uint64_lor(x_17, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = lean_uint8_to_uint64(x_25);
x_27 = 32;
x_28 = lean_uint64_shift_left(x_26, x_27);
x_29 = lean_uint64_lor(x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = lean_uint8_to_uint64(x_31);
x_33 = 24;
x_34 = lean_uint64_shift_left(x_32, x_33);
x_35 = lean_uint64_lor(x_29, x_34);
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = lean_uint8_to_uint64(x_37);
x_39 = 16;
x_40 = lean_uint64_shift_left(x_38, x_39);
x_41 = lean_uint64_lor(x_35, x_40);
x_42 = lean_unsigned_to_nat(6u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = lean_uint8_to_uint64(x_43);
x_45 = 8;
x_46 = lean_uint64_shift_left(x_44, x_45);
x_47 = lean_uint64_lor(x_41, x_46);
x_48 = lean_unsigned_to_nat(7u);
x_49 = lean_byte_array_get(x_1, x_48);
x_50 = lean_uint8_to_uint64(x_49);
x_51 = lean_uint64_lor(x_47, x_50);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_toUInt64BE_x21(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1 = _init_l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1);
l_ByteArray_toUInt64LE_x21___closed__0 = _init_l_ByteArray_toUInt64LE_x21___closed__0();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__0);
l_ByteArray_toUInt64LE_x21___closed__1 = _init_l_ByteArray_toUInt64LE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__1);
l_ByteArray_toUInt64LE_x21___closed__2 = _init_l_ByteArray_toUInt64LE_x21___closed__2();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__2);
l_ByteArray_toUInt64LE_x21___closed__3 = _init_l_ByteArray_toUInt64LE_x21___closed__3();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__3);
l_ByteArray_toUInt64BE_x21___closed__0 = _init_l_ByteArray_toUInt64BE_x21___closed__0();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__0);
l_ByteArray_toUInt64BE_x21___closed__1 = _init_l_ByteArray_toUInt64BE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
