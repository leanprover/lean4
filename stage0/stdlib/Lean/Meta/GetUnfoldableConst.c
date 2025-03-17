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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_shouldReduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Environment_findAsync_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
x_14 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_18 = lean_box(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_7);
x_19 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_free_object(x_13);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 2);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_task_get_own(x_30);
lean_ctor_set(x_13, 0, x_31);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_task_get_own(x_33);
lean_ctor_set(x_13, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_18);
x_36 = l_Lean_AsyncConstantInfo_toConstantInfo(x_16);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; 
lean_free_object(x_7);
lean_inc(x_36);
x_37 = l_Lean_Meta_canUnfold(x_36, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_36);
lean_free_object(x_13);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_37, 0);
lean_dec(x_47);
lean_ctor_set(x_13, 0, x_36);
lean_ctor_set(x_37, 0, x_13);
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
lean_ctor_set(x_13, 0, x_36);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_36);
lean_free_object(x_13);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_36);
lean_free_object(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_54 = lean_box(0);
lean_ctor_set(x_7, 0, x_54);
return x_7;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
lean_dec(x_13);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*3);
x_57 = lean_box(x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_free_object(x_7);
x_58 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_55, 2);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_task_get_own(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_57);
x_71 = l_Lean_AsyncConstantInfo_toConstantInfo(x_55);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; 
lean_free_object(x_7);
lean_inc(x_71);
x_72 = l_Lean_Meta_canUnfold(x_71, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_71);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_71);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_71);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = lean_box(0);
lean_ctor_set(x_7, 0, x_87);
return x_7;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_7, 0);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_7);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = 0;
lean_inc(x_1);
x_92 = l_Lean_Environment_findAsync_x3f(x_90, x_1, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = l_Lean_throwUnknownConstant___at___private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get_uint8(x_94, sizeof(void*)*3);
x_97 = lean_box(x_96);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Meta_shouldReduceAll(x_2, x_3, x_4, x_5, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_95);
lean_dec(x_94);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_106 = x_98;
} else {
 lean_dec_ref(x_98);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_94, 2);
lean_inc(x_107);
lean_dec(x_94);
x_108 = lean_task_get_own(x_107);
if (lean_is_scalar(x_95)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_95;
}
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_106)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_106;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_97);
x_111 = l_Lean_AsyncConstantInfo_toConstantInfo(x_94);
if (lean_obj_tag(x_111) == 1)
{
lean_object* x_112; 
lean_inc(x_111);
x_112 = l_Lean_Meta_canUnfold(x_111, x_2, x_3, x_4, x_5, x_89);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_111);
lean_dec(x_95);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_95;
}
lean_ctor_set(x_121, 0, x_111);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_111);
lean_dec(x_95);
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_125 = x_112;
} else {
 lean_dec_ref(x_112);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_111);
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_89);
return x_128;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Environment_find_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
switch (lean_obj_tag(x_16)) {
case 1:
{
lean_object* x_17; 
lean_free_object(x_7);
lean_inc(x_16);
x_17 = l_Lean_Meta_canUnfold(x_16, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_free_object(x_13);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_13);
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 2:
{
lean_object* x_34; 
lean_free_object(x_13);
lean_free_object(x_7);
x_34 = l_Lean_Meta_getTheoremInfo(x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_34;
}
default: 
{
lean_object* x_35; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
switch (lean_obj_tag(x_36)) {
case 1:
{
lean_object* x_37; 
lean_free_object(x_7);
lean_inc(x_36);
x_37 = l_Lean_Meta_canUnfold(x_36, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_36);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
case 2:
{
lean_object* x_52; 
lean_free_object(x_7);
x_52 = l_Lean_Meta_getTheoremInfo(x_36, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_52;
}
default: 
{
lean_object* x_53; 
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_53 = lean_box(0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = 0;
x_58 = l_Lean_Environment_find_x3f(x_56, x_1, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
switch (lean_obj_tag(x_61)) {
case 1:
{
lean_object* x_63; 
lean_inc(x_61);
x_63 = l_Lean_Meta_canUnfold(x_61, x_2, x_3, x_4, x_5, x_55);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_61);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_62;
}
lean_ctor_set(x_72, 0, x_61);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
lean_dec(x_61);
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_76 = x_63;
} else {
 lean_dec_ref(x_63);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
case 2:
{
lean_object* x_78; 
lean_dec(x_62);
x_78 = l_Lean_Meta_getTheoremInfo(x_61, x_2, x_3, x_4, x_5, x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_55);
return x_80;
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
