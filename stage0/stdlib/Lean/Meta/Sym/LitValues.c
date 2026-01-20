// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: public import Lean.Expr public import Init.Data.Rat
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
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
static lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2;
uint16_t lean_int16_of_int(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
static lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__2;
static lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__0;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object*);
static lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1;
static lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__0;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__0;
static lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__1;
uint64_t lean_int64_of_int(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__2;
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
static lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__1;
static lean_object* _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_getNatValue_x3f___closed__1;
x_2 = l_Lean_Meta_Sym_getNatValue_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_13 = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec_ref(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_8);
x_15 = lean_box(0);
return x_15;
}
else
{
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec_ref(x_16);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec_ref(x_8);
x_21 = lean_box(0);
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_getIntValue_x3f___closed__1;
x_2 = l_Lean_Meta_Sym_getIntValue_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Meta_Sym_getIntValue_x3f___closed__2;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_21; 
lean_dec_ref(x_1);
x_21 = l_Lean_Meta_Sym_getNatValue_x3f(x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_int_neg(x_25);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_neg(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
block_10:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_to_int(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Rat_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_getRatValue_x3f___closed__1;
x_2 = l_Lean_Meta_Sym_getRatValue_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Meta_Sym_getRatValue_x3f___closed__2;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
lean_dec_ref(x_25);
if (x_27 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_28; 
lean_dec_ref(x_1);
x_28 = l_Lean_Meta_Sym_getIntValue_x3f(x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_13);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Meta_Sym_getNatValue_x3f(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_30);
x_32 = lean_box(0);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = l_Rat_ofInt(x_30);
x_36 = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(x_34);
x_37 = l_Rat_div(x_35, x_36);
lean_dec_ref(x_35);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
x_39 = l_Rat_ofInt(x_30);
x_40 = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(x_38);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
}
}
}
}
block_10:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Rat_ofInt(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Rat_ofInt(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_getNatValue_x3f___closed__1;
x_2 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNatLT", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2;
x_2 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_cleanupAnnotations(x_1);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_27 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec_ref(x_21);
x_29 = l_Lean_Expr_isApp(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_33 = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3;
x_36 = l_Lean_Expr_isConstOf(x_32, x_35);
lean_dec_ref(x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_31);
lean_dec_ref(x_25);
x_37 = lean_box(0);
return x_37;
}
else
{
x_2 = x_31;
x_3 = x_25;
goto block_17;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_dec_ref(x_32);
x_38 = l_Lean_Expr_cleanupAnnotations(x_31);
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_38);
lean_dec_ref(x_25);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_41);
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_38);
x_43 = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4;
x_44 = l_Lean_Expr_isConstOf(x_42, x_43);
lean_dec_ref(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec_ref(x_41);
lean_dec_ref(x_25);
x_45 = lean_box(0);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Sym_getNatValue_x3f(x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_25);
x_47 = lean_box(0);
return x_47;
}
else
{
if (lean_obj_tag(x_25) == 9)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_48);
lean_dec_ref(x_25);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec_ref(x_48);
x_52 = l_BitVec_ofNat(x_50, x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_46, 0, x_53);
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec_ref(x_48);
x_56 = l_BitVec_ofNat(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec_ref(x_48);
lean_dec_ref(x_46);
x_59 = lean_box(0);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec_ref(x_46);
lean_dec_ref(x_25);
x_60 = lean_box(0);
return x_60;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_26);
x_2 = x_25;
x_3 = x_21;
goto block_17;
}
}
}
block_17:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Sym_getNatValue_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Sym_getNatValue_x3f(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_BitVec_ofNat(x_6, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_BitVec_ofNat(x_6, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_uint8_of_nat(x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_uint8_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint16_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_uint16_of_nat(x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint16_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_uint16_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_uint32_of_nat(x_5);
lean_dec(x_5);
x_7 = lean_box_uint32(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_uint32_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_box_uint32(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_uint64_of_nat(x_5);
lean_dec(x_5);
x_7 = lean_box_uint64(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_uint64_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_box_uint64(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_int8_of_int(x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_int8_of_int(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint16_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_int16_of_int(x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint16_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_int16_of_int(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_int32_of_int(x_5);
lean_dec(x_5);
x_7 = lean_box_uint32(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_int32_of_int(x_8);
lean_dec(x_8);
x_10 = lean_box_uint32(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_int64_of_int(x_5);
lean_dec(x_5);
x_7 = lean_box_uint64(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_int64_of_int(x_8);
lean_dec(x_8);
x_10 = lean_box_uint64(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_getFinValue_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getFinValue_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_getFinValue_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_14 = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec_ref(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_12);
lean_dec_ref(x_8);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_cleanupAnnotations(x_12);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_17);
lean_dec_ref(x_8);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_22 = l_Lean_Meta_Sym_getFinValue_x3f___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_20);
lean_dec_ref(x_8);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Sym_getNatValue_x3f(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_8);
x_26 = lean_box(0);
return x_26;
}
else
{
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_8);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_nat_mod(x_30, x_29);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; 
lean_dec(x_30);
lean_free_object(x_25);
lean_dec(x_29);
x_35 = lean_box(0);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec_ref(x_27);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_nat_mod(x_37, x_36);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_36);
x_43 = lean_box(0);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_27);
lean_dec_ref(x_25);
x_44 = lean_box(0);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec_ref(x_25);
lean_dec_ref(x_8);
x_45 = lean_box(0);
return x_45;
}
}
}
}
}
}
}
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_getNatValue_x3f___closed__0 = _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_getNatValue_x3f___closed__0);
l_Lean_Meta_Sym_getNatValue_x3f___closed__1 = _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_getNatValue_x3f___closed__1);
l_Lean_Meta_Sym_getNatValue_x3f___closed__2 = _init_l_Lean_Meta_Sym_getNatValue_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_getNatValue_x3f___closed__2);
l_Lean_Meta_Sym_getIntValue_x3f___closed__0 = _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_getIntValue_x3f___closed__0);
l_Lean_Meta_Sym_getIntValue_x3f___closed__1 = _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_getIntValue_x3f___closed__1);
l_Lean_Meta_Sym_getIntValue_x3f___closed__2 = _init_l_Lean_Meta_Sym_getIntValue_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_getIntValue_x3f___closed__2);
l_Lean_Meta_Sym_getRatValue_x3f___closed__0 = _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_getRatValue_x3f___closed__0);
l_Lean_Meta_Sym_getRatValue_x3f___closed__1 = _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_getRatValue_x3f___closed__1);
l_Lean_Meta_Sym_getRatValue_x3f___closed__2 = _init_l_Lean_Meta_Sym_getRatValue_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_getRatValue_x3f___closed__2);
l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0 = _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0);
l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1 = _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1);
l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2 = _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2);
l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3 = _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3);
l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4 = _init_l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4);
l_Lean_Meta_Sym_getFinValue_x3f___closed__0 = _init_l_Lean_Meta_Sym_getFinValue_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_getFinValue_x3f___closed__0);
l_Lean_Meta_Sym_getFinValue_x3f___closed__1 = _init_l_Lean_Meta_Sym_getFinValue_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_getFinValue_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
