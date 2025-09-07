// Lean compiler output
// Module: Init.Data.Format.Instances
// Imports: Init.Data.Format.Basic Init.Data.Array.Basic Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_instToFormatArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatPos;
LEAN_EXPORT lean_object* l_instToFormatProd___redArg(lean_object*, lean_object*);
static lean_object* l_instToFormatProd___redArg___lam__0___closed__3;
static lean_object* l_Option_format___redArg___closed__0;
static lean_object* l_List_format___redArg___closed__9;
LEAN_EXPORT lean_object* l_instToFormatPos___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_toFormat(lean_object*);
static lean_object* l_Option_format___redArg___closed__2;
static lean_object* l_List_format___redArg___closed__0;
LEAN_EXPORT lean_object* l_instToFormatList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatArray___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
static lean_object* l_List_format___redArg___closed__1;
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOfToString(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Option_format(lean_object*, lean_object*, lean_object*);
static lean_object* l_instToFormatProd___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_List_format___redArg(lean_object*, lean_object*);
static lean_object* l_instToFormatArray___redArg___lam__0___closed__0;
static uint8_t l_String_toFormat___closed__2;
static lean_object* l_String_toFormat___closed__0;
static lean_object* l_List_format___redArg___closed__7;
static lean_object* l_List_format___redArg___closed__8;
static lean_object* l_instToFormatArray___redArg___lam__0___closed__1;
static lean_object* l_List_format___redArg___closed__4;
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg(lean_object*);
static lean_object* l_List_format___redArg___closed__5;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___String_toFormat_spec__0(lean_object*, lean_object*);
static lean_object* l_Option_format___redArg___closed__1;
static lean_object* l_List_format___redArg___closed__3;
static lean_object* l_String_toFormat___closed__1;
static lean_object* l_instToFormatProd___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_instToFormatArray(lean_object*, lean_object*);
static lean_object* l_List_format___redArg___closed__2;
LEAN_EXPORT lean_object* l_Option_format___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___String_toFormat_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToFormatOption___redArg(lean_object*);
static lean_object* l_Option_format___redArg___closed__3;
LEAN_EXPORT lean_object* l_instToFormatProd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instToFormatProd___redArg___lam__0___closed__0;
static lean_object* l_List_format___redArg___closed__6;
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatOfToString___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_instToFormatOfToString___redArg___lam__0), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_2);
lean_closure_set(x_3, 4, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToFormatOfToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToFormatOfToString___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_List_format___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_format___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_format___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_List_format___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_format___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_format___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_format___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_instNatCastInt___lam__0(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___redArg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_format___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_List_format___redArg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_4 = l_List_format___redArg___closed__4;
x_5 = l_Std_Format_joinSep___redArg(x_1, x_2, x_4);
x_6 = l_List_format___redArg___closed__7;
x_7 = l_List_format___redArg___closed__8;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_List_format___redArg___closed__9;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_format___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToFormatList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_format), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_format), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instToFormatArray___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_instToFormatArray___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instToFormatArray___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_instToFormatArray___redArg___lam__0___closed__1;
x_4 = lean_array_to_list(x_2);
x_5 = l_List_format___redArg(x_1, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instToFormatArray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToFormatArray___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Option_format___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Option_format___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_format___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Option_format___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("some ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Option_format___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_format___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_format___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_Option_format___redArg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Option_format___redArg___closed__3;
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Option_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_format___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToFormatOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_format), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_format), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instToFormatProd___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToFormatProd___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instToFormatProd___redArg___lam__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToFormatProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_List_format___redArg___closed__3;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_1(x_2, x_6);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_format___redArg___closed__7;
x_14 = l_instToFormatProd___redArg___lam__0___closed__2;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = l_instToFormatProd___redArg___lam__0___closed__3;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = 0;
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_apply_1(x_1, x_21);
x_24 = l_List_format___redArg___closed__3;
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_apply_1(x_2, x_22);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_format___redArg___closed__7;
x_31 = l_instToFormatProd___redArg___lam__0___closed__2;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = l_instToFormatProd___redArg___lam__0___closed__3;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = 0;
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_instToFormatProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToFormatProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToFormatProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instToFormatProd___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___String_toFormat_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___String_toFormat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_List_foldl___at___Std_Format_joinSep___at___String_toFormat_spec__0_spec__0(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_String_toFormat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_String_toFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l_String_toFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_String_toFormat___closed__1;
x_2 = l_String_toFormat___closed__0;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; uint8_t x_7; 
x_6 = l_String_toFormat___closed__0;
x_7 = l_String_toFormat___closed__2;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_box(0);
x_10 = l_String_splitOnAux(x_1, x_6, x_8, x_8, x_8, x_9);
lean_dec_ref(x_1);
x_2 = x_10;
goto block_5;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_2 = x_12;
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = l_Std_Format_joinSep___at___String_toFormat_spec__0(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_instToFormatPos___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_reprFast(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_instToFormatPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToFormatPos___lam__0), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Data_Format_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Instances(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_format___redArg___closed__0 = _init_l_List_format___redArg___closed__0();
lean_mark_persistent(l_List_format___redArg___closed__0);
l_List_format___redArg___closed__1 = _init_l_List_format___redArg___closed__1();
lean_mark_persistent(l_List_format___redArg___closed__1);
l_List_format___redArg___closed__2 = _init_l_List_format___redArg___closed__2();
lean_mark_persistent(l_List_format___redArg___closed__2);
l_List_format___redArg___closed__3 = _init_l_List_format___redArg___closed__3();
lean_mark_persistent(l_List_format___redArg___closed__3);
l_List_format___redArg___closed__4 = _init_l_List_format___redArg___closed__4();
lean_mark_persistent(l_List_format___redArg___closed__4);
l_List_format___redArg___closed__5 = _init_l_List_format___redArg___closed__5();
lean_mark_persistent(l_List_format___redArg___closed__5);
l_List_format___redArg___closed__6 = _init_l_List_format___redArg___closed__6();
lean_mark_persistent(l_List_format___redArg___closed__6);
l_List_format___redArg___closed__7 = _init_l_List_format___redArg___closed__7();
lean_mark_persistent(l_List_format___redArg___closed__7);
l_List_format___redArg___closed__8 = _init_l_List_format___redArg___closed__8();
lean_mark_persistent(l_List_format___redArg___closed__8);
l_List_format___redArg___closed__9 = _init_l_List_format___redArg___closed__9();
lean_mark_persistent(l_List_format___redArg___closed__9);
l_instToFormatArray___redArg___lam__0___closed__0 = _init_l_instToFormatArray___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToFormatArray___redArg___lam__0___closed__0);
l_instToFormatArray___redArg___lam__0___closed__1 = _init_l_instToFormatArray___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToFormatArray___redArg___lam__0___closed__1);
l_Option_format___redArg___closed__0 = _init_l_Option_format___redArg___closed__0();
lean_mark_persistent(l_Option_format___redArg___closed__0);
l_Option_format___redArg___closed__1 = _init_l_Option_format___redArg___closed__1();
lean_mark_persistent(l_Option_format___redArg___closed__1);
l_Option_format___redArg___closed__2 = _init_l_Option_format___redArg___closed__2();
lean_mark_persistent(l_Option_format___redArg___closed__2);
l_Option_format___redArg___closed__3 = _init_l_Option_format___redArg___closed__3();
lean_mark_persistent(l_Option_format___redArg___closed__3);
l_instToFormatProd___redArg___lam__0___closed__0 = _init_l_instToFormatProd___redArg___lam__0___closed__0();
lean_mark_persistent(l_instToFormatProd___redArg___lam__0___closed__0);
l_instToFormatProd___redArg___lam__0___closed__1 = _init_l_instToFormatProd___redArg___lam__0___closed__1();
lean_mark_persistent(l_instToFormatProd___redArg___lam__0___closed__1);
l_instToFormatProd___redArg___lam__0___closed__2 = _init_l_instToFormatProd___redArg___lam__0___closed__2();
lean_mark_persistent(l_instToFormatProd___redArg___lam__0___closed__2);
l_instToFormatProd___redArg___lam__0___closed__3 = _init_l_instToFormatProd___redArg___lam__0___closed__3();
lean_mark_persistent(l_instToFormatProd___redArg___lam__0___closed__3);
l_String_toFormat___closed__0 = _init_l_String_toFormat___closed__0();
lean_mark_persistent(l_String_toFormat___closed__0);
l_String_toFormat___closed__1 = _init_l_String_toFormat___closed__1();
lean_mark_persistent(l_String_toFormat___closed__1);
l_String_toFormat___closed__2 = _init_l_String_toFormat___closed__2();
l_instToFormatPos = _init_l_instToFormatPos();
lean_mark_persistent(l_instToFormatPos);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
