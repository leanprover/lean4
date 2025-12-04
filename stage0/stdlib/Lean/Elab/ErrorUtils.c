// Lean compiler output
// Module: Lean.Elab.ErrorUtils
// Imports: import Init.Notation import Init.Data.String
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
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0;
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford(lean_object*);
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("th", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rd", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nd", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tenth", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ninth", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eighth", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seventh", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sixth", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fifth", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fourth", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("third", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("second", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("first", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zeroth", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_40; 
x_22 = lean_unsigned_to_nat(10u);
x_40 = lean_nat_dec_eq(x_1, x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(100u);
x_42 = lean_nat_mod(x_1, x_41);
x_43 = lean_nat_dec_lt(x_22, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
x_23 = x_43;
goto block_39;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(20u);
x_45 = lean_nat_dec_lt(x_42, x_44);
lean_dec(x_42);
x_23 = x_45;
goto block_39;
}
}
else
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3;
return x_46;
}
block_39:
{
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_nat_mod(x_1, x_22);
x_25 = lean_nat_dec_eq(x_24, x_6);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_24, x_8);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Nat_reprFast(x_1);
x_28 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
x_29 = lean_string_append(x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Nat_reprFast(x_1);
x_31 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1;
x_32 = lean_string_append(x_30, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_33 = l_Nat_reprFast(x_1);
x_34 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2;
x_35 = lean_string_append(x_33, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Nat_reprFast(x_1);
x_37 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
x_38 = lean_string_append(x_36, x_37);
return x_38;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_1);
x_47 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4;
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5;
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6;
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7;
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8;
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9;
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_1);
x_53 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10;
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11;
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12;
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13;
return x_56;
}
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", and ", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__List_toOxford(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_inc_ref(x_3);
x_5 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec_ref(x_5);
x_15 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2;
x_16 = lean_string_append(x_12, x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_14);
lean_dec(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l___private_Lean_Elab_ErrorUtils_0__List_toOxford(x_3);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorUtils_0__Nat_plural___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_ErrorUtils_0__Nat_plural(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ErrorUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12);
l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13 = _init_l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13);
l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0 = _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__0);
l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1 = _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__1);
l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2 = _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__2);
l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3 = _init_l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3();
lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__List_toOxford___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
