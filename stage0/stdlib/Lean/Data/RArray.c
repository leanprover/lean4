// Lean compiler output
// Module: Lean.Data.RArray
// Imports: public import Lean.Meta.DecLevel
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
static lean_object* l_Lean_RArray_toExpr___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
static lean_object* l_Lean_RArray_toExpr___redArg___closed__3;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___redArg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_nat_dec_eq(x_5, x_3);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_nat_add(x_2, x_3);
x_8 = lean_nat_shiftr(x_7, x_4);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(x_1, x_2, x_8);
lean_inc(x_8);
x_10 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(x_1, x_8, x_3);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_1(x_1, x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_ofFn___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RArray_ofFn___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RArray_ofFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_ofArray___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_RArray_ofArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_array_get_size(x_1);
lean_dec_ref(x_1);
x_4 = l_Lean_RArray_ofFn___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RArray_ofArray___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_apply_1(x_2, x_8);
x_10 = l_Lean_mkAppB(x_3, x_1, x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_apply_1(x_2, x_11);
x_13 = l_Lean_mkAppB(x_3, x_1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(x_1, x_2, x_3, x_4, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_20 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(x_1, x_2, x_3, x_4, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkRawNatLit(x_15);
x_24 = l_Lean_mkApp4(x_4, x_1, x_23, x_19, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_mkRawNatLit(x_15);
x_27 = l_Lean_mkApp4(x_4, x_1, x_26, x_19, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RArray", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leaf", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RArray_toExpr___redArg___closed__2;
x_2 = l_Lean_RArray_toExpr___redArg___closed__1;
x_3 = l_Lean_RArray_toExpr___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("branch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RArray_toExpr___redArg___closed__4;
x_2 = l_Lean_RArray_toExpr___redArg___closed__1;
x_3 = l_Lean_RArray_toExpr___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_getDecLevel(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_RArray_toExpr___redArg___closed__3;
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_inc_ref(x_13);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = l_Lean_RArray_toExpr___redArg___closed__5;
x_16 = l_Lean_mkConst(x_15, x_13);
x_17 = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(x_1, x_2, x_14, x_16, x_3);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RArray_toExpr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RArray_toExpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RArray_toExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RArray_toExpr___redArg___closed__0 = _init_l_Lean_RArray_toExpr___redArg___closed__0();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__0);
l_Lean_RArray_toExpr___redArg___closed__1 = _init_l_Lean_RArray_toExpr___redArg___closed__1();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__1);
l_Lean_RArray_toExpr___redArg___closed__2 = _init_l_Lean_RArray_toExpr___redArg___closed__2();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__2);
l_Lean_RArray_toExpr___redArg___closed__3 = _init_l_Lean_RArray_toExpr___redArg___closed__3();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__3);
l_Lean_RArray_toExpr___redArg___closed__4 = _init_l_Lean_RArray_toExpr___redArg___closed__4();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__4);
l_Lean_RArray_toExpr___redArg___closed__5 = _init_l_Lean_RArray_toExpr___redArg___closed__5();
lean_mark_persistent(l_Lean_RArray_toExpr___redArg___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
