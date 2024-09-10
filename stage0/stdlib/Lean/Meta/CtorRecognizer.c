// Lean compiler output
// Module: Lean.Meta.CtorRecognizer
// Imports: Lean.Meta.LitValues Lean.Meta.Offset
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
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_constructorApp_x27_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorAppCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_constructorApp_x27_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_constructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_constructorApp_x27_x3f___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_constructorApp_x3f___closed__1;
extern lean_object* l___private_Lean_Expr_0__Lean_natAddFn;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_constructorApp_x27_x3f___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorAppCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_litToCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorAppCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_20);
x_22 = lean_nat_dec_eq(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_13);
lean_dec(x_16);
x_23 = lean_box(0);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 4);
lean_inc(x_26);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_28);
x_30 = lean_nat_dec_eq(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_24);
x_31 = lean_box(0);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_35, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_39, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 4);
lean_inc(x_42);
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_44);
x_46 = lean_nat_dec_eq(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_39);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_40)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_40;
}
lean_ctor_set(x_49, 0, x_39);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_7);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorAppCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isConstructorAppCore_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_litToCtor(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_isConstructorAppCore_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_isConstructorApp_x3f(x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isConstructorApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(1, 1, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isConstructorApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_isConstructorApp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isConstructorApp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_isConstructorApp_x27___lambda__1(x_1, x_11, x_2, x_3, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isConstructorApp_x27___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_constructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Meta_litToCtor(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_10);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_16, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 4);
lean_inc(x_22);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_24);
x_26 = lean_nat_dec_eq(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_20);
lean_dec(x_9);
x_27 = lean_box(0);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_Meta_constructorApp_x3f___closed__1;
lean_inc(x_25);
x_29 = lean_mk_array(x_25, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_9, x_29, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_17, 0, x_33);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 4);
lean_inc(x_36);
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_38);
x_40 = lean_nat_dec_eq(x_37, x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_9);
x_41 = lean_box(0);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = l_Lean_Meta_constructorApp_x3f___closed__1;
lean_inc(x_39);
x_43 = lean_mk_array(x_39, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_39, x_44);
lean_dec(x_39);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_9, x_43, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_13, 0, x_48);
return x_13;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_51, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_9);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_55, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 4);
lean_inc(x_58);
x_59 = lean_nat_add(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_60);
x_62 = lean_nat_dec_eq(x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_9);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = l_Lean_Meta_constructorApp_x3f___closed__1;
lean_inc(x_61);
x_66 = lean_mk_array(x_61, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_61, x_67);
lean_dec(x_61);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_9, x_66, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_56)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_56;
}
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
x_73 = lean_box(0);
lean_ctor_set(x_7, 0, x_73);
return x_7;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_7, 0);
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_7);
x_76 = l_Lean_Expr_getAppFn(x_74);
if (lean_obj_tag(x_76) == 4)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_5, x_75);
lean_dec(x_5);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_82, x_77);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_74);
x_84 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_86, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 4);
lean_inc(x_89);
x_90 = lean_nat_add(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_74, x_91);
x_93 = lean_nat_dec_eq(x_90, x_92);
lean_dec(x_90);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_74);
x_94 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_81;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_80);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = l_Lean_Meta_constructorApp_x3f___closed__1;
lean_inc(x_92);
x_97 = lean_mk_array(x_92, x_96);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_92, x_98);
lean_dec(x_92);
x_100 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_74, x_97, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_86);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_87)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_87;
}
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_81)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_81;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_80);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_5);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_75);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_7);
if (x_106 == 0)
{
return x_7;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_7, 0);
x_108 = lean_ctor_get(x_7, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_7);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x27_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x27_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x27_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_constructorApp_x27_x3f___closed__1;
x_2 = l_Lean_Meta_constructorApp_x27_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x27_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_constructorApp_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_constructorApp_x3f(x_14, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = l_Lean_Exception_isInterrupt(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_box(0);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
return x_16;
}
}
else
{
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = l_Lean_Exception_isInterrupt(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
x_38 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
else
{
return x_13;
}
}
else
{
return x_13;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = l_Lean_Exception_isInterrupt(x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_10, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_11, 0);
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_10, 0, x_51);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_54 = x_11;
} else {
 lean_dec_ref(x_11);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_7);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_7, 1);
x_65 = lean_ctor_get(x_7, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_7);
x_71 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_72 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_71, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 6)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_dec_eq(x_68, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_nat_sub(x_68, x_77);
lean_dec(x_68);
x_80 = l_Lean_mkNatLit(x_79);
x_81 = l___private_Lean_Expr_0__Lean_natAddFn;
x_82 = l_Lean_mkAppB(x_81, x_67, x_80);
x_83 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_84 = lean_array_push(x_83, x_82);
lean_ctor_set(x_63, 1, x_84);
lean_ctor_set(x_63, 0, x_76);
lean_ctor_set(x_72, 0, x_8);
return x_72;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_68);
x_85 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_86 = lean_array_push(x_85, x_67);
lean_ctor_set(x_63, 1, x_86);
lean_ctor_set(x_63, 0, x_76);
lean_ctor_set(x_72, 0, x_8);
return x_72;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_dec_eq(x_68, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_nat_sub(x_68, x_89);
lean_dec(x_68);
x_92 = l_Lean_mkNatLit(x_91);
x_93 = l___private_Lean_Expr_0__Lean_natAddFn;
x_94 = l_Lean_mkAppB(x_93, x_67, x_92);
x_95 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_96 = lean_array_push(x_95, x_94);
lean_ctor_set(x_63, 1, x_96);
lean_ctor_set(x_63, 0, x_88);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_87);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_68);
x_98 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_99 = lean_array_push(x_98, x_67);
lean_ctor_set(x_63, 1, x_99);
lean_ctor_set(x_63, 0, x_88);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_87);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_73);
lean_free_object(x_63);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_8);
x_101 = !lean_is_exclusive(x_72);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_72, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_72, 0, x_103);
return x_72;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_72, 1);
lean_inc(x_104);
lean_dec(x_72);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_free_object(x_63);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_8);
x_107 = !lean_is_exclusive(x_72);
if (x_107 == 0)
{
return x_72;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_72, 0);
x_109 = lean_ctor_get(x_72, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_72);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_free_object(x_63);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_box(0);
lean_ctor_set(x_7, 0, x_111);
return x_7;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_63, 0);
x_113 = lean_ctor_get(x_63, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_63);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_free_object(x_7);
x_116 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_117 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_116, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 6)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_dec_eq(x_113, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_nat_sub(x_113, x_122);
lean_dec(x_113);
x_125 = l_Lean_mkNatLit(x_124);
x_126 = l___private_Lean_Expr_0__Lean_natAddFn;
x_127 = l_Lean_mkAppB(x_126, x_112, x_125);
x_128 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_129 = lean_array_push(x_128, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_8, 0, x_130);
if (lean_is_scalar(x_120)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_120;
}
lean_ctor_set(x_131, 0, x_8);
lean_ctor_set(x_131, 1, x_119);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_113);
x_132 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_133 = lean_array_push(x_132, x_112);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_8, 0, x_134);
if (lean_is_scalar(x_120)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_120;
}
lean_ctor_set(x_135, 0, x_8);
lean_ctor_set(x_135, 1, x_119);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_112);
lean_free_object(x_8);
x_136 = lean_ctor_get(x_117, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_137 = x_117;
} else {
 lean_dec_ref(x_117);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_113);
lean_dec(x_112);
lean_free_object(x_8);
x_140 = lean_ctor_get(x_117, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_117, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_142 = x_117;
} else {
 lean_dec_ref(x_117);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; 
lean_dec(x_113);
lean_dec(x_112);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = lean_box(0);
lean_ctor_set(x_7, 0, x_144);
return x_7;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_145 = lean_ctor_get(x_8, 0);
x_146 = lean_ctor_get(x_7, 1);
lean_inc(x_146);
lean_dec(x_7);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_nat_dec_eq(x_148, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_153 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_152, x_2, x_3, x_4, x_5, x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 6)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_dec_eq(x_148, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_nat_sub(x_148, x_158);
lean_dec(x_148);
x_161 = l_Lean_mkNatLit(x_160);
x_162 = l___private_Lean_Expr_0__Lean_natAddFn;
x_163 = l_Lean_mkAppB(x_162, x_147, x_161);
x_164 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_165 = lean_array_push(x_164, x_163);
if (lean_is_scalar(x_149)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_149;
}
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_8, 0, x_166);
if (lean_is_scalar(x_156)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_156;
}
lean_ctor_set(x_167, 0, x_8);
lean_ctor_set(x_167, 1, x_155);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_148);
x_168 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_169 = lean_array_push(x_168, x_147);
if (lean_is_scalar(x_149)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_149;
}
lean_ctor_set(x_170, 0, x_157);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_8, 0, x_170);
if (lean_is_scalar(x_156)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_156;
}
lean_ctor_set(x_171, 0, x_8);
lean_ctor_set(x_171, 1, x_155);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_free_object(x_8);
x_172 = lean_ctor_get(x_153, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_173 = x_153;
} else {
 lean_dec_ref(x_153);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_free_object(x_8);
x_176 = lean_ctor_get(x_153, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_153, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_178 = x_153;
} else {
 lean_dec_ref(x_153);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_146);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_182 = lean_ctor_get(x_8, 0);
lean_inc(x_182);
lean_dec(x_8);
x_183 = lean_ctor_get(x_7, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_184 = x_7;
} else {
 lean_dec_ref(x_7);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_186, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_184);
x_190 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_191 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_190, x_2, x_3, x_4, x_5, x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 6)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_nat_dec_eq(x_186, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_nat_sub(x_186, x_196);
lean_dec(x_186);
x_199 = l_Lean_mkNatLit(x_198);
x_200 = l___private_Lean_Expr_0__Lean_natAddFn;
x_201 = l_Lean_mkAppB(x_200, x_185, x_199);
x_202 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_203 = lean_array_push(x_202, x_201);
if (lean_is_scalar(x_187)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_187;
}
lean_ctor_set(x_204, 0, x_195);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_194)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_194;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_193);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_186);
x_207 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_208 = lean_array_push(x_207, x_185);
if (lean_is_scalar(x_187)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_187;
}
lean_ctor_set(x_209, 0, x_195);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
if (lean_is_scalar(x_194)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_194;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_193);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_192);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
x_212 = lean_ctor_get(x_191, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_213 = x_191;
} else {
 lean_dec_ref(x_191);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
x_216 = lean_ctor_get(x_191, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_191, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_218 = x_191;
} else {
 lean_dec_ref(x_191);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = lean_box(0);
if (lean_is_scalar(x_184)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_184;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_183);
return x_221;
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_7);
if (x_222 == 0)
{
return x_7;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_7, 0);
x_224 = lean_ctor_get(x_7, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_7);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_constructorApp_x3f___closed__1 = _init_l_Lean_Meta_constructorApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_constructorApp_x3f___closed__1);
l_Lean_Meta_constructorApp_x27_x3f___closed__1 = _init_l_Lean_Meta_constructorApp_x27_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_constructorApp_x27_x3f___closed__1);
l_Lean_Meta_constructorApp_x27_x3f___closed__2 = _init_l_Lean_Meta_constructorApp_x27_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_constructorApp_x27_x3f___closed__2);
l_Lean_Meta_constructorApp_x27_x3f___closed__3 = _init_l_Lean_Meta_constructorApp_x27_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_constructorApp_x27_x3f___closed__3);
l_Lean_Meta_constructorApp_x27_x3f___closed__4 = _init_l_Lean_Meta_constructorApp_x27_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_constructorApp_x27_x3f___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
