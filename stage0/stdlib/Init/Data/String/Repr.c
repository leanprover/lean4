// Lean compiler output
// Module: Init.Data.String.Repr
// Imports: public import Init.Data.String.Basic public import Init.Data.ToString.Basic
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
static lean_object* l_instReprIterator___lam__0___closed__3;
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_toInt_x21_spec__0(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_Substring_toNat_x3f(lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__6;
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_String_toInt_x21___closed__0;
static lean_object* l_instReprIterator___lam__0___closed__5;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__2;
static lean_object* l_instReprIterator___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__7;
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__0;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instReprIterator;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object*);
LEAN_EXPORT uint8_t l_String_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringIterator;
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_instReprIterator___lam__0___closed__4;
static lean_object* _init_l_instReprIterator___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Iterator.mk ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ byteIdx := ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_instReprIterator___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprIterator___lam__0___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_instReprIterator___lam__0___closed__1;
x_7 = l_String_quote(x_4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
x_9 = l_instReprIterator___lam__0___closed__3;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_instReprIterator___lam__0___closed__5;
x_12 = l_Nat_reprFast(x_5);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_instReprIterator___lam__0___closed__7;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_instReprIterator___lam__0___closed__1;
x_22 = l_String_quote(x_19);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_instReprIterator___lam__0___closed__3;
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_instReprIterator___lam__0___closed__5;
x_28 = l_Nat_reprFast(x_20);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_instReprIterator___lam__0___closed__7;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Repr_addAppParen(x_33, x_2);
return x_34;
}
}
}
static lean_object* _init_l_instReprIterator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprIterator___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprIterator___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_instToStringIterator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_String_toNat_x3f(x_1);
lean_dec_ref(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_nat_to_int(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_string_utf8_byte_size(x_1);
lean_inc(x_14);
lean_inc_ref(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_nextn(x_15, x_16, x_2);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
x_19 = l_Substring_toNat_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_neg(x_23);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_neg(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___String_isInt_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
x_6 = x_12;
goto block_9;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_10, x_13);
x_6 = x_14;
goto block_9;
}
}
block_9:
{
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_nat_dec_eq(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_String_anyAux___at___String_isInt_spec__0(x_7, x_1, x_6, x_2);
lean_dec(x_6);
lean_dec_ref(x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
return x_7;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_1);
return x_5;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_string_utf8_byte_size(x_1);
lean_inc(x_10);
lean_inc_ref(x_1);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Substring_nextn(x_11, x_12, x_2);
lean_dec_ref(x_11);
x_14 = lean_nat_sub(x_10, x_13);
x_15 = lean_nat_dec_eq(x_14, x_2);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_String_anyAux___at___String_isInt_spec__0(x_15, x_1, x_10, x_13);
lean_dec(x_10);
lean_dec_ref(x_1);
if (x_16 == 0)
{
return x_5;
}
else
{
return x_15;
}
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_1);
x_17 = 0;
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_isInt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___String_isInt_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___String_toInt_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Int_instInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_toInt_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int expected", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toInt_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_toInt_x21___closed__0;
x_4 = l_panic___at___String_toInt_x21_spec__0(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
return x_5;
}
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Repr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instReprIterator___lam__0___closed__0 = _init_l_instReprIterator___lam__0___closed__0();
lean_mark_persistent(l_instReprIterator___lam__0___closed__0);
l_instReprIterator___lam__0___closed__1 = _init_l_instReprIterator___lam__0___closed__1();
lean_mark_persistent(l_instReprIterator___lam__0___closed__1);
l_instReprIterator___lam__0___closed__2 = _init_l_instReprIterator___lam__0___closed__2();
lean_mark_persistent(l_instReprIterator___lam__0___closed__2);
l_instReprIterator___lam__0___closed__3 = _init_l_instReprIterator___lam__0___closed__3();
lean_mark_persistent(l_instReprIterator___lam__0___closed__3);
l_instReprIterator___lam__0___closed__4 = _init_l_instReprIterator___lam__0___closed__4();
lean_mark_persistent(l_instReprIterator___lam__0___closed__4);
l_instReprIterator___lam__0___closed__5 = _init_l_instReprIterator___lam__0___closed__5();
lean_mark_persistent(l_instReprIterator___lam__0___closed__5);
l_instReprIterator___lam__0___closed__6 = _init_l_instReprIterator___lam__0___closed__6();
lean_mark_persistent(l_instReprIterator___lam__0___closed__6);
l_instReprIterator___lam__0___closed__7 = _init_l_instReprIterator___lam__0___closed__7();
lean_mark_persistent(l_instReprIterator___lam__0___closed__7);
l_instReprIterator = _init_l_instReprIterator();
lean_mark_persistent(l_instReprIterator);
l_instToStringIterator = _init_l_instToStringIterator();
lean_mark_persistent(l_instToStringIterator);
l_String_toInt_x21___closed__0 = _init_l_String_toInt_x21___closed__0();
lean_mark_persistent(l_String_toInt_x21___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
