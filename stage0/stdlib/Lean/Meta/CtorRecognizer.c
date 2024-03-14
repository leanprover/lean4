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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_litToCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x27_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_9);
x_26 = lean_nat_dec_eq(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_17);
lean_dec(x_20);
x_27 = lean_box(0);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 4);
lean_inc(x_30);
x_31 = lean_nat_add(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_32);
lean_dec(x_9);
x_34 = lean_nat_dec_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
x_35 = lean_box(0);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_39, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 4);
lean_inc(x_46);
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_48);
lean_dec(x_9);
x_50 = lean_nat_dec_eq(x_47, x_49);
lean_dec(x_49);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_43);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_44)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_44;
}
lean_ctor_set(x_53, 0, x_43);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_38);
return x_54;
}
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
x_55 = lean_box(0);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_7);
x_58 = l_Lean_Expr_getAppFn(x_56);
if (lean_obj_tag(x_58) == 4)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_5, x_57);
lean_dec(x_5);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(x_64, x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
x_66 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 4);
lean_inc(x_71);
x_72 = lean_nat_add(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_56, x_73);
lean_dec(x_56);
x_75 = lean_nat_dec_eq(x_72, x_74);
lean_dec(x_74);
lean_dec(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_69);
lean_dec(x_68);
x_76 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_63;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_62);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
if (lean_is_scalar(x_69)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_69;
}
lean_ctor_set(x_78, 0, x_68);
if (lean_is_scalar(x_63)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_63;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_62);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_5);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_57);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_5);
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
return x_7;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_7, 0);
x_84 = lean_ctor_get(x_7, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_7);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
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
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_constructorApp_x27_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
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
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
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
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_7, 1);
x_39 = lean_ctor_get(x_7, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_7);
x_45 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_46 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_45, x_2, x_3, x_4, x_5, x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 6)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_dec_eq(x_42, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_nat_sub(x_42, x_51);
lean_dec(x_42);
x_54 = l_Lean_mkNatLit(x_53);
x_55 = l___private_Lean_Expr_0__Lean_natAddFn;
x_56 = l_Lean_mkAppB(x_55, x_41, x_54);
x_57 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_58 = lean_array_push(x_57, x_56);
lean_ctor_set(x_37, 1, x_58);
lean_ctor_set(x_37, 0, x_50);
lean_ctor_set(x_46, 0, x_8);
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
x_59 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_60 = lean_array_push(x_59, x_41);
lean_ctor_set(x_37, 1, x_60);
lean_ctor_set(x_37, 0, x_50);
lean_ctor_set(x_46, 0, x_8);
return x_46;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_dec_eq(x_42, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_nat_sub(x_42, x_63);
lean_dec(x_42);
x_66 = l_Lean_mkNatLit(x_65);
x_67 = l___private_Lean_Expr_0__Lean_natAddFn;
x_68 = l_Lean_mkAppB(x_67, x_41, x_66);
x_69 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_70 = lean_array_push(x_69, x_68);
lean_ctor_set(x_37, 1, x_70);
lean_ctor_set(x_37, 0, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_8);
lean_ctor_set(x_71, 1, x_61);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_42);
x_72 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_73 = lean_array_push(x_72, x_41);
lean_ctor_set(x_37, 1, x_73);
lean_ctor_set(x_37, 0, x_62);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_61);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_47);
lean_free_object(x_37);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_8);
x_75 = !lean_is_exclusive(x_46);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_46, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_46, 0, x_77);
return x_46;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_46, 1);
lean_inc(x_78);
lean_dec(x_46);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_37);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_8);
x_81 = !lean_is_exclusive(x_46);
if (x_81 == 0)
{
return x_46;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_46, 0);
x_83 = lean_ctor_get(x_46, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_46);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_free_object(x_37);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_box(0);
lean_ctor_set(x_7, 0, x_85);
return x_7;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_37, 0);
x_87 = lean_ctor_get(x_37, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_37);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_free_object(x_7);
x_90 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_91 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_90, x_2, x_3, x_4, x_5, x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 6)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_dec_eq(x_87, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_nat_sub(x_87, x_96);
lean_dec(x_87);
x_99 = l_Lean_mkNatLit(x_98);
x_100 = l___private_Lean_Expr_0__Lean_natAddFn;
x_101 = l_Lean_mkAppB(x_100, x_86, x_99);
x_102 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_103 = lean_array_push(x_102, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_8, 0, x_104);
if (lean_is_scalar(x_94)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_94;
}
lean_ctor_set(x_105, 0, x_8);
lean_ctor_set(x_105, 1, x_93);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_87);
x_106 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_107 = lean_array_push(x_106, x_86);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_8, 0, x_108);
if (lean_is_scalar(x_94)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_94;
}
lean_ctor_set(x_109, 0, x_8);
lean_ctor_set(x_109, 1, x_93);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_92);
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_8);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_111 = x_91;
} else {
 lean_dec_ref(x_91);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_8);
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_91, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_116 = x_91;
} else {
 lean_dec_ref(x_91);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_box(0);
lean_ctor_set(x_7, 0, x_118);
return x_7;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_8, 0);
x_120 = lean_ctor_get(x_7, 1);
lean_inc(x_120);
lean_dec(x_7);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
 x_123 = lean_box(0);
}
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_eq(x_122, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_127 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_126, x_2, x_3, x_4, x_5, x_120);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 6)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_dec_eq(x_122, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_nat_sub(x_122, x_132);
lean_dec(x_122);
x_135 = l_Lean_mkNatLit(x_134);
x_136 = l___private_Lean_Expr_0__Lean_natAddFn;
x_137 = l_Lean_mkAppB(x_136, x_121, x_135);
x_138 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_139 = lean_array_push(x_138, x_137);
if (lean_is_scalar(x_123)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_123;
}
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_8, 0, x_140);
if (lean_is_scalar(x_130)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_130;
}
lean_ctor_set(x_141, 0, x_8);
lean_ctor_set(x_141, 1, x_129);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_122);
x_142 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_143 = lean_array_push(x_142, x_121);
if (lean_is_scalar(x_123)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_123;
}
lean_ctor_set(x_144, 0, x_131);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_8, 0, x_144);
if (lean_is_scalar(x_130)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_130;
}
lean_ctor_set(x_145, 0, x_8);
lean_ctor_set(x_145, 1, x_129);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_128);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_8);
x_146 = lean_ctor_get(x_127, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_147 = x_127;
} else {
 lean_dec_ref(x_127);
 x_147 = lean_box(0);
}
x_148 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_8);
x_150 = lean_ctor_get(x_127, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_127, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_152 = x_127;
} else {
 lean_dec_ref(x_127);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_120);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_156 = lean_ctor_get(x_8, 0);
lean_inc(x_156);
lean_dec(x_8);
x_157 = lean_ctor_get(x_7, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_158 = x_7;
} else {
 lean_dec_ref(x_7);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_161 = x_156;
} else {
 lean_dec_ref(x_156);
 x_161 = lean_box(0);
}
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_eq(x_160, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
x_164 = l_Lean_Meta_constructorApp_x27_x3f___closed__3;
x_165 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_164, x_2, x_3, x_4, x_5, x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 6)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_dec_eq(x_160, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_172 = lean_nat_sub(x_160, x_170);
lean_dec(x_160);
x_173 = l_Lean_mkNatLit(x_172);
x_174 = l___private_Lean_Expr_0__Lean_natAddFn;
x_175 = l_Lean_mkAppB(x_174, x_159, x_173);
x_176 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_177 = lean_array_push(x_176, x_175);
if (lean_is_scalar(x_161)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_161;
}
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
if (lean_is_scalar(x_168)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_168;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_167);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_160);
x_181 = l_Lean_Meta_constructorApp_x27_x3f___closed__4;
x_182 = lean_array_push(x_181, x_159);
if (lean_is_scalar(x_161)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_161;
}
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
if (lean_is_scalar(x_168)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_168;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_167);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
x_186 = lean_ctor_get(x_165, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_187 = x_165;
} else {
 lean_dec_ref(x_165);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
x_190 = lean_ctor_get(x_165, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_165, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_192 = x_165;
} else {
 lean_dec_ref(x_165);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_194 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_158;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_157);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_7);
if (x_196 == 0)
{
return x_7;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_7, 0);
x_198 = lean_ctor_get(x_7, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_7);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
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
