// Lean compiler output
// Module: Lake.Util.Date
// Imports: public import Init.Data.Ord.Basic import Lake.Util.String import Init.Data.String.Search
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
lean_object* l_Lake_zpad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Date_instToString___closed__0;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate_decEq(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_Date_instLE;
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__16;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__12;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__6;
LEAN_EXPORT uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instToString;
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedDate;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object*);
static lean_object* l_Lake_instOrdDate___closed__0;
LEAN_EXPORT lean_object* l_Lake_Date_instLT;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_instInhabitedDate_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instReprDate;
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__17;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__15;
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lake_instOrdDate_ord___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__11;
static lean_object* l_Lake_Date_instMin___closed__0;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__8;
static lean_object* l_Lake_instReprDate___closed__0;
LEAN_EXPORT lean_object* l_Lake_Date_instMax;
static lean_object* l_Lake_Date_ofString_x3f___closed__0;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__1;
static lean_object* l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0;
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__5;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate_decEq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Date_instMin;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__10;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__14;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__19;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedDate_default;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_instOrdDate;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_instReprDate_repr___redArg___closed__9;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Date_toString___closed__0;
static lean_object* l_Lake_Date_instMax___closed__0;
static lean_object* _init_l_Lake_instInhabitedDate_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedDate_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedDate_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedDate() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedDate_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqDate_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_instDecidableEqDate_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqDate(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdDate_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_lt(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_3, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_7);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_4, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 2;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_5, x_8);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_5, x_8);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 2;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdDate_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instOrdDate_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instOrdDate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instOrdDate_ord___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdDate() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdDate___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("year", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__5;
x_2 = l_Lake_instReprDate_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("month", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("day", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__17;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprDate_repr___redArg___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_instReprDate_repr___redArg___closed__5;
x_6 = l_Lake_instReprDate_repr___redArg___closed__6;
x_7 = l_Lake_instReprDate_repr___redArg___closed__7;
x_8 = l_Nat_reprFast(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_instReprDate_repr___redArg___closed__9;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lake_instReprDate_repr___redArg___closed__11;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Lake_instReprDate_repr___redArg___closed__12;
x_22 = l_Nat_reprFast(x_3);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_11);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = l_Lake_instReprDate_repr___redArg___closed__14;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = l_Lake_instReprDate_repr___redArg___closed__15;
x_33 = l_Nat_reprFast(x_4);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_11);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lake_instReprDate_repr___redArg___closed__18;
x_39 = l_Lake_instReprDate_repr___redArg___closed__19;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = l_Lake_instReprDate_repr___redArg___closed__20;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_11);
return x_44;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprDate_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprDate_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprDate_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprDate() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprDate___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_instOrdDate_ord(x_1, x_2);
if (x_3 == 2)
{
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_inc_ref(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Date_instMin___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Date_instMin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Date_instMin___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instMin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Date_instMin___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_instOrdDate_ord(x_1, x_2);
if (x_3 == 2)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Date_instMax___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Date_instMax___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Date_instMax___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instMax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Date_instMax___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(7u);
x_6 = lean_nat_dec_le(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(31u);
x_8 = lean_nat_mod(x_2, x_3);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(30u);
x_11 = lean_nat_mod(x_2, x_3);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_22; 
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_nat_mod(x_1, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(28u);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(100u);
x_25 = lean_nat_mod(x_1, x_24);
x_26 = lean_nat_dec_eq(x_25, x_15);
lean_dec(x_25);
if (x_26 == 0)
{
if (x_22 == 0)
{
goto block_21;
}
else
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(29u);
return x_27;
}
}
else
{
goto block_21;
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(400u);
x_17 = lean_nat_mod(x_1, x_16);
x_18 = lean_nat_dec_eq(x_17, x_15);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(28u);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(29u);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Date_maxDay(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(12u);
x_8 = lean_nat_dec_le(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_Date_maxDay(x_1, x_2);
x_13 = lean_nat_dec_le(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_nat_sub(x_16, x_15);
x_18 = lean_nat_dec_eq(x_14, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_string_utf8_next_fast(x_3, x_14);
x_20 = lean_string_utf8_get_fast(x_3, x_14);
x_21 = lean_uint32_dec_eq(x_20, x_1);
if (x_21 == 0)
{
lean_dec(x_14);
lean_ctor_set(x_5, 1, x_19);
goto _start;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_2);
x_23 = l_String_Slice_slice_x21(x_2, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_19);
x_7 = x_5;
x_8 = x_23;
goto block_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_5);
lean_dec(x_14);
lean_inc(x_4);
lean_inc_ref(x_3);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_4);
x_25 = lean_box(1);
x_7 = x_25;
x_8 = x_24;
goto block_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_nat_sub(x_29, x_28);
x_31 = lean_nat_dec_eq(x_27, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_string_utf8_next_fast(x_3, x_27);
x_33 = lean_string_utf8_get_fast(x_3, x_27);
x_34 = lean_uint32_dec_eq(x_33, x_1);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_2);
x_37 = l_String_Slice_slice_x21(x_2, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_32);
x_7 = x_38;
x_8 = x_37;
goto block_11;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
lean_inc(x_4);
lean_inc_ref(x_3);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_4);
x_40 = lean_box(1);
x_7 = x_40;
x_8 = x_39;
goto block_11;
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
block_11:
{
lean_object* x_9; 
x_9 = lean_array_push(x_6, x_8);
x_5 = x_7;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_Date_ofString_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = 45;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0(x_5);
x_7 = l_Lake_Date_ofString_x3f___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(x_2, x_5, x_1, x_4, x_6, x_7);
x_9 = lean_array_to_list(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = l_String_Slice_toNat_x3f(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_String_Slice_toNat_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_15);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_String_Slice_toNat_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_18);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lake_Date_ofValid_x3f(x_18, x_21, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_26 = lean_box(0);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_27 = lean_box(0);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec_ref(x_9);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_9);
x_29 = lean_box(0);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(x_1, x_2, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_11 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_Lake_Date_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Lake_zpad(x_2, x_5);
x_7 = l_Lake_Date_toString___closed__0;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lake_zpad(x_3, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = lean_string_append(x_11, x_7);
x_13 = l_Lake_zpad(x_4, x_9);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
static lean_object* _init_l_Lake_Date_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Date_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Date_instToString___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Date(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedDate_default___closed__0 = _init_l_Lake_instInhabitedDate_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedDate_default___closed__0);
l_Lake_instInhabitedDate_default = _init_l_Lake_instInhabitedDate_default();
lean_mark_persistent(l_Lake_instInhabitedDate_default);
l_Lake_instInhabitedDate = _init_l_Lake_instInhabitedDate();
lean_mark_persistent(l_Lake_instInhabitedDate);
l_Lake_instOrdDate___closed__0 = _init_l_Lake_instOrdDate___closed__0();
lean_mark_persistent(l_Lake_instOrdDate___closed__0);
l_Lake_instOrdDate = _init_l_Lake_instOrdDate();
lean_mark_persistent(l_Lake_instOrdDate);
l_Lake_instReprDate_repr___redArg___closed__0 = _init_l_Lake_instReprDate_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__0);
l_Lake_instReprDate_repr___redArg___closed__1 = _init_l_Lake_instReprDate_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__1);
l_Lake_instReprDate_repr___redArg___closed__2 = _init_l_Lake_instReprDate_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__2);
l_Lake_instReprDate_repr___redArg___closed__3 = _init_l_Lake_instReprDate_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__3);
l_Lake_instReprDate_repr___redArg___closed__4 = _init_l_Lake_instReprDate_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__4);
l_Lake_instReprDate_repr___redArg___closed__5 = _init_l_Lake_instReprDate_repr___redArg___closed__5();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__5);
l_Lake_instReprDate_repr___redArg___closed__6 = _init_l_Lake_instReprDate_repr___redArg___closed__6();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__6);
l_Lake_instReprDate_repr___redArg___closed__7 = _init_l_Lake_instReprDate_repr___redArg___closed__7();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__7);
l_Lake_instReprDate_repr___redArg___closed__8 = _init_l_Lake_instReprDate_repr___redArg___closed__8();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__8);
l_Lake_instReprDate_repr___redArg___closed__9 = _init_l_Lake_instReprDate_repr___redArg___closed__9();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__9);
l_Lake_instReprDate_repr___redArg___closed__10 = _init_l_Lake_instReprDate_repr___redArg___closed__10();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__10);
l_Lake_instReprDate_repr___redArg___closed__11 = _init_l_Lake_instReprDate_repr___redArg___closed__11();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__11);
l_Lake_instReprDate_repr___redArg___closed__12 = _init_l_Lake_instReprDate_repr___redArg___closed__12();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__12);
l_Lake_instReprDate_repr___redArg___closed__13 = _init_l_Lake_instReprDate_repr___redArg___closed__13();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__13);
l_Lake_instReprDate_repr___redArg___closed__14 = _init_l_Lake_instReprDate_repr___redArg___closed__14();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__14);
l_Lake_instReprDate_repr___redArg___closed__15 = _init_l_Lake_instReprDate_repr___redArg___closed__15();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__15);
l_Lake_instReprDate_repr___redArg___closed__16 = _init_l_Lake_instReprDate_repr___redArg___closed__16();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__16);
l_Lake_instReprDate_repr___redArg___closed__17 = _init_l_Lake_instReprDate_repr___redArg___closed__17();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__17);
l_Lake_instReprDate_repr___redArg___closed__18 = _init_l_Lake_instReprDate_repr___redArg___closed__18();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__18);
l_Lake_instReprDate_repr___redArg___closed__19 = _init_l_Lake_instReprDate_repr___redArg___closed__19();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__19);
l_Lake_instReprDate_repr___redArg___closed__20 = _init_l_Lake_instReprDate_repr___redArg___closed__20();
lean_mark_persistent(l_Lake_instReprDate_repr___redArg___closed__20);
l_Lake_instReprDate___closed__0 = _init_l_Lake_instReprDate___closed__0();
lean_mark_persistent(l_Lake_instReprDate___closed__0);
l_Lake_instReprDate = _init_l_Lake_instReprDate();
lean_mark_persistent(l_Lake_instReprDate);
l_Lake_Date_instLT = _init_l_Lake_Date_instLT();
lean_mark_persistent(l_Lake_Date_instLT);
l_Lake_Date_instLE = _init_l_Lake_Date_instLE();
lean_mark_persistent(l_Lake_Date_instLE);
l_Lake_Date_instMin___closed__0 = _init_l_Lake_Date_instMin___closed__0();
lean_mark_persistent(l_Lake_Date_instMin___closed__0);
l_Lake_Date_instMin = _init_l_Lake_Date_instMin();
lean_mark_persistent(l_Lake_Date_instMin);
l_Lake_Date_instMax___closed__0 = _init_l_Lake_Date_instMax___closed__0();
lean_mark_persistent(l_Lake_Date_instMax___closed__0);
l_Lake_Date_instMax = _init_l_Lake_Date_instMax();
lean_mark_persistent(l_Lake_Date_instMax);
l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0 = _init_l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00Lake_Date_ofString_x3f_spec__0___closed__0);
l_Lake_Date_ofString_x3f___closed__0 = _init_l_Lake_Date_ofString_x3f___closed__0();
lean_mark_persistent(l_Lake_Date_ofString_x3f___closed__0);
l_Lake_Date_toString___closed__0 = _init_l_Lake_Date_toString___closed__0();
lean_mark_persistent(l_Lake_Date_toString___closed__0);
l_Lake_Date_instToString___closed__0 = _init_l_Lake_Date_instToString___closed__0();
lean_mark_persistent(l_Lake_Date_instToString___closed__0);
l_Lake_Date_instToString = _init_l_Lake_Date_instToString();
lean_mark_persistent(l_Lake_Date_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
