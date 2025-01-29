// Lean compiler output
// Module: Lean.Meta.GetUnfoldableConst
// Imports: Lean.Meta.GlobalInstances
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_instance(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t, uint8_t);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTheoremInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_get_reducibility_status(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_get_reducibility_status(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 2)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = 1;
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = 1;
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_ctor_get_uint8(x_1, 9);
x_7 = lean_box(x_6);
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_ConstantInfo_name(x_2);
x_12 = l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1(x_11, x_3, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_7);
x_31 = l_Lean_ConstantInfo_name(x_2);
lean_inc(x_31);
x_32 = l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(x_31, x_3, x_4, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_st_ref_get(x_4, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = 3;
x_41 = l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_6, x_40);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_31);
x_42 = 0;
x_43 = lean_box(x_42);
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
else
{
uint8_t x_44; 
x_44 = lean_is_instance(x_39, x_31);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
x_46 = lean_box(x_45);
lean_ctor_set(x_36, 0, x_46);
return x_36;
}
else
{
uint8_t x_47; lean_object* x_48; 
x_47 = 1;
x_48 = lean_box(x_47);
lean_ctor_set(x_36, 0, x_48);
return x_36;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 3;
x_53 = l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_6, x_52);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_31);
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_is_instance(x_51, x_31);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
else
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_31);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
lean_dec(x_65);
x_66 = 1;
x_67 = lean_box(x_66);
lean_ctor_set(x_32, 0, x_67);
return x_32;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_32, 1);
lean_inc(x_68);
lean_dec(x_32);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isIrreducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_2, 6);
lean_inc(x_8);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault(x_9, x_1, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_apply_5(x_14, x_12, x_1, x_4, x_5, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_canUnfold(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Environment_find_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_15)) {
case 1:
{
lean_object* x_16; 
lean_free_object(x_7);
lean_inc(x_15);
x_16 = l_Lean_Meta_canUnfold(x_15, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_free_object(x_12);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_12);
lean_dec(x_15);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 2:
{
lean_object* x_33; 
lean_free_object(x_12);
lean_free_object(x_7);
x_33 = l_Lean_Meta_getTheoremInfo(x_15, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_33;
}
default: 
{
lean_object* x_34; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_box(0);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
switch (lean_obj_tag(x_35)) {
case 1:
{
lean_object* x_36; 
lean_free_object(x_7);
lean_inc(x_35);
x_36 = l_Lean_Meta_canUnfold(x_35, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_35);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
case 2:
{
lean_object* x_51; 
lean_free_object(x_7);
x_51 = l_Lean_Meta_getTheoremInfo(x_35, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_51;
}
default: 
{
lean_object* x_52; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = lean_box(0);
lean_ctor_set(x_7, 0, x_52);
return x_7;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_1);
x_56 = l_Lean_Environment_find_x3f(x_55, x_1);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
switch (lean_obj_tag(x_58)) {
case 1:
{
lean_object* x_60; 
lean_inc(x_58);
x_60 = l_Lean_Meta_canUnfold(x_58, x_2, x_3, x_4, x_5, x_54);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_58);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_59;
}
lean_ctor_set(x_69, 0, x_58);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_59);
lean_dec(x_58);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
case 2:
{
lean_object* x_75; 
lean_dec(x_59);
x_75 = l_Lean_Meta_getTheoremInfo(x_58, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_75;
}
default: 
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_54);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUnfoldableConst_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_find_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_box(0);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_15)) {
case 1:
{
lean_object* x_16; 
lean_free_object(x_7);
lean_inc(x_15);
x_16 = l_Lean_Meta_canUnfold(x_15, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_free_object(x_12);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_12);
lean_dec(x_15);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 2:
{
lean_object* x_33; 
lean_free_object(x_12);
lean_free_object(x_7);
x_33 = l_Lean_Meta_getTheoremInfo(x_15, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_33;
}
default: 
{
lean_object* x_34; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_box(0);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
switch (lean_obj_tag(x_35)) {
case 1:
{
lean_object* x_36; 
lean_free_object(x_7);
lean_inc(x_35);
x_36 = l_Lean_Meta_canUnfold(x_35, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_35);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
case 2:
{
lean_object* x_51; 
lean_free_object(x_7);
x_51 = l_Lean_Meta_getTheoremInfo(x_35, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_51;
}
default: 
{
lean_object* x_52; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = lean_box(0);
lean_ctor_set(x_7, 0, x_52);
return x_7;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Environment_find_x3f(x_55, x_1);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
switch (lean_obj_tag(x_59)) {
case 1:
{
lean_object* x_61; 
lean_inc(x_59);
x_61 = l_Lean_Meta_canUnfold(x_59, x_2, x_3, x_4, x_5, x_54);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_59);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_59);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_60);
lean_dec(x_59);
x_72 = lean_ctor_get(x_61, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
case 2:
{
lean_object* x_76; 
lean_dec(x_60);
x_76 = l_Lean_Meta_getTheoremInfo(x_59, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_54);
return x_78;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUnfoldableConstNoEx_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Lean_Meta_GlobalInstances(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_GlobalInstances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
