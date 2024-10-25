// Lean compiler output
// Module: Lean.Meta.Constructions.RecOn
// Imports: Lean.Meta.InferType Lean.AuxRecursor Lean.AddDecl Lean.Meta.CompletionName
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_mkRecOn___spec__1(lean_object*, lean_object*);
static lean_object* l_mkRecOn___closed__2;
extern lean_object* l_Lean_auxRecExt;
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_mkRecOn___closed__3;
static lean_object* l_mkRecOn___closed__7;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_mkRecOn___closed__1;
LEAN_EXPORT lean_object* l_mkRecOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_mkRecOn___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkRecOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5;
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_recOnSuffix;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
static lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_mkRecOn___closed__6;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_mkRecOn___closed__5;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_mkRecOn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_param___override(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_param___override(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = l_Lean_Environment_hasUnsafe(x_14, x_3);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
if (x_15 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Environment_hasUnsafe(x_14, x_4);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_5);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_14);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_28);
x_29 = l_Lean_Environment_hasUnsafe(x_28, x_3);
lean_inc(x_1);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
if (x_29 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Environment_hasUnsafe(x_28, x_4);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 1;
x_35 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_4);
lean_ctor_set(x_35, 2, x_5);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_5);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 2, x_5);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
x_2 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2;
x_3 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5;
x_4 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_3);
lean_ctor_set(x_4, 6, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_12, x_1, x_2, x_14, x_15);
x_17 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
lean_ctor_set(x_9, 4, x_17);
lean_ctor_set(x_9, 0, x_16);
x_18 = lean_st_ref_set(x_6, x_9, x_10);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_4, x_38, x_22);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
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
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 5);
x_49 = lean_ctor_get(x_9, 6);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_50 = 0;
x_51 = lean_box(0);
x_52 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_44, x_1, x_2, x_50, x_51);
x_53 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_47);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_48);
lean_ctor_set(x_54, 6, x_49);
x_55 = lean_st_ref_set(x_6, x_54, x_10);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_take(x_4, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
x_65 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
x_67 = lean_st_ref_set(x_4, x_66, x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_mkRecOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_List_mapTR_loop___at_mkRecOn___spec__1(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_11, x_14);
x_16 = l_Lean_mkAppN(x_15, x_4);
x_17 = lean_array_get_size(x_4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
lean_inc(x_4);
x_25 = l_Array_toSubarray___rarg(x_4, x_24, x_23);
x_26 = lean_nat_add(x_23, x_18);
x_27 = lean_nat_add(x_26, x_22);
x_28 = lean_nat_add(x_27, x_20);
lean_dec(x_27);
lean_inc(x_26);
lean_inc(x_4);
x_29 = l_Array_toSubarray___rarg(x_4, x_26, x_28);
x_30 = l_Array_ofSubarray___rarg(x_25);
lean_dec(x_25);
x_31 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_32 = l_Array_append___rarg(x_30, x_31);
lean_dec(x_31);
x_33 = lean_array_get_size(x_32);
x_34 = l_Array_toSubarray___rarg(x_32, x_24, x_33);
x_35 = l_Array_toSubarray___rarg(x_4, x_23, x_26);
x_36 = l_Array_ofSubarray___rarg(x_34);
lean_dec(x_34);
x_37 = l_Array_ofSubarray___rarg(x_35);
lean_dec(x_35);
x_38 = l_Array_append___rarg(x_36, x_37);
lean_dec(x_37);
x_39 = lean_array_get_size(x_38);
x_40 = l_Array_toSubarray___rarg(x_38, x_24, x_39);
x_41 = l_Array_ofSubarray___rarg(x_40);
lean_dec(x_40);
x_42 = 0;
x_43 = 1;
x_44 = 1;
lean_inc(x_41);
x_45 = l_Lean_Meta_mkForallFVars(x_41, x_5, x_42, x_43, x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_mkLambdaFVars(x_41, x_16, x_42, x_43, x_42, x_44, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_recOnSuffix;
x_52 = l_Lean_Name_str___override(x_3, x_51);
x_53 = lean_box(1);
x_54 = l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2(x_52, x_12, x_46, x_49, x_53, x_6, x_7, x_8, x_9, x_50);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_46);
lean_dec(x_12);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
return x_45;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_45, 0);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_45);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l_mkRecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_mkRecOn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_mkRecOn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_mkRecOn___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_mkRecOn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" not a recinfo", 14, 14);
return x_1;
}
}
static lean_object* _init_l_mkRecOn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_mkRecOn___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_mkRecOn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_auxRecExt;
return x_1;
}
}
static lean_object* _init_l_mkRecOn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_protectedExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_mkRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_mkRecOn___closed__1;
lean_inc(x_1);
x_8 = l_Lean_Name_str___override(x_1, x_7);
lean_inc(x_8);
x_9 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_mkRecOn___lambda__1___boxed), 10, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_1);
x_17 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_19);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_addDecl(x_10, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 0;
lean_inc(x_24);
x_26 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(x_24, x_25, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 4);
lean_dec(x_33);
x_34 = l_mkRecOn___closed__6;
lean_inc(x_24);
x_35 = l_Lean_TagDeclarationExtension_tag(x_34, x_32, x_24);
x_36 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
lean_ctor_set(x_29, 4, x_36);
lean_ctor_set(x_29, 0, x_35);
x_37 = lean_st_ref_set(x_5, x_29, x_30);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_3, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
x_44 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
lean_ctor_set(x_40, 1, x_44);
x_45 = lean_st_ref_set(x_3, x_40, x_41);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_5, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 4);
lean_dec(x_52);
x_53 = l_mkRecOn___closed__7;
x_54 = l_Lean_TagDeclarationExtension_tag(x_53, x_51, x_24);
lean_ctor_set(x_48, 4, x_36);
lean_ctor_set(x_48, 0, x_54);
x_55 = lean_st_ref_set(x_5, x_48, x_49);
lean_dec(x_5);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_take(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_44);
x_62 = lean_st_ref_set(x_3, x_58, x_59);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 2);
x_71 = lean_ctor_get(x_58, 3);
x_72 = lean_ctor_get(x_58, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_44);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_72);
x_74 = lean_st_ref_set(x_3, x_73, x_59);
lean_dec(x_3);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
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
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_79 = lean_ctor_get(x_48, 0);
x_80 = lean_ctor_get(x_48, 1);
x_81 = lean_ctor_get(x_48, 2);
x_82 = lean_ctor_get(x_48, 3);
x_83 = lean_ctor_get(x_48, 5);
x_84 = lean_ctor_get(x_48, 6);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_48);
x_85 = l_mkRecOn___closed__7;
x_86 = l_Lean_TagDeclarationExtension_tag(x_85, x_79, x_24);
x_87 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_80);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_82);
lean_ctor_set(x_87, 4, x_36);
lean_ctor_set(x_87, 5, x_83);
lean_ctor_set(x_87, 6, x_84);
x_88 = lean_st_ref_set(x_5, x_87, x_49);
lean_dec(x_5);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_take(x_3, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 4);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_44);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_95);
lean_ctor_set(x_98, 4, x_96);
x_99 = lean_st_ref_set(x_3, x_98, x_92);
lean_dec(x_3);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_104 = lean_ctor_get(x_40, 0);
x_105 = lean_ctor_get(x_40, 2);
x_106 = lean_ctor_get(x_40, 3);
x_107 = lean_ctor_get(x_40, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_40);
x_108 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_105);
lean_ctor_set(x_109, 3, x_106);
lean_ctor_set(x_109, 4, x_107);
x_110 = lean_st_ref_set(x_3, x_109, x_41);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_st_ref_take(x_5, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 6);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 lean_ctor_release(x_113, 6);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
x_122 = l_mkRecOn___closed__7;
x_123 = l_Lean_TagDeclarationExtension_tag(x_122, x_115, x_24);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 7, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_116);
lean_ctor_set(x_124, 2, x_117);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set(x_124, 4, x_36);
lean_ctor_set(x_124, 5, x_119);
lean_ctor_set(x_124, 6, x_120);
x_125 = lean_st_ref_set(x_5, x_124, x_114);
lean_dec(x_5);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_take(x_3, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 4);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_108);
lean_ctor_set(x_135, 2, x_131);
lean_ctor_set(x_135, 3, x_132);
lean_ctor_set(x_135, 4, x_133);
x_136 = lean_st_ref_set(x_3, x_135, x_129);
lean_dec(x_3);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_141 = lean_ctor_get(x_29, 0);
x_142 = lean_ctor_get(x_29, 1);
x_143 = lean_ctor_get(x_29, 2);
x_144 = lean_ctor_get(x_29, 3);
x_145 = lean_ctor_get(x_29, 5);
x_146 = lean_ctor_get(x_29, 6);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_29);
x_147 = l_mkRecOn___closed__6;
lean_inc(x_24);
x_148 = l_Lean_TagDeclarationExtension_tag(x_147, x_141, x_24);
x_149 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
x_150 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_142);
lean_ctor_set(x_150, 2, x_143);
lean_ctor_set(x_150, 3, x_144);
lean_ctor_set(x_150, 4, x_149);
lean_ctor_set(x_150, 5, x_145);
lean_ctor_set(x_150, 6, x_146);
x_151 = lean_st_ref_set(x_5, x_150, x_30);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_st_ref_take(x_3, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 4);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
x_161 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_157);
lean_ctor_set(x_162, 3, x_158);
lean_ctor_set(x_162, 4, x_159);
x_163 = lean_st_ref_set(x_3, x_162, x_155);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_take(x_5, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 5);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 6);
lean_inc(x_173);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 lean_ctor_release(x_166, 6);
 x_174 = x_166;
} else {
 lean_dec_ref(x_166);
 x_174 = lean_box(0);
}
x_175 = l_mkRecOn___closed__7;
x_176 = l_Lean_TagDeclarationExtension_tag(x_175, x_168, x_24);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 7, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_169);
lean_ctor_set(x_177, 2, x_170);
lean_ctor_set(x_177, 3, x_171);
lean_ctor_set(x_177, 4, x_149);
lean_ctor_set(x_177, 5, x_172);
lean_ctor_set(x_177, 6, x_173);
x_178 = lean_st_ref_set(x_5, x_177, x_167);
lean_dec(x_5);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_st_ref_take(x_3, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 4);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 5, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_161);
lean_ctor_set(x_188, 2, x_184);
lean_ctor_set(x_188, 3, x_185);
lean_ctor_set(x_188, 4, x_186);
x_189 = lean_st_ref_set(x_3, x_188, x_182);
lean_dec(x_3);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = lean_box(0);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_21);
if (x_194 == 0)
{
return x_21;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_21, 0);
x_196 = lean_ctor_get(x_21, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_21);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_free_object(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_18);
if (x_198 == 0)
{
return x_18;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_18, 0);
x_200 = lean_ctor_get(x_18, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_18);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_10, 0);
lean_inc(x_202);
lean_dec(x_10);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 2);
lean_inc(x_204);
x_205 = lean_alloc_closure((void*)(l_mkRecOn___lambda__1___boxed), 10, 3);
lean_closure_set(x_205, 0, x_203);
lean_closure_set(x_205, 1, x_202);
lean_closure_set(x_205, 2, x_1);
x_206 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_207 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_204, x_205, x_206, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_208);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_208);
lean_inc(x_5);
lean_inc(x_4);
x_211 = l_Lean_addDecl(x_210, x_4, x_5, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
lean_dec(x_208);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec(x_213);
x_215 = 0;
lean_inc(x_214);
x_216 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(x_214, x_215, x_2, x_3, x_4, x_5, x_212);
lean_dec(x_4);
lean_dec(x_2);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_st_ref_take(x_5, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_219, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 5);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 6);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 lean_ctor_release(x_219, 6);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
x_228 = l_mkRecOn___closed__6;
lean_inc(x_214);
x_229 = l_Lean_TagDeclarationExtension_tag(x_228, x_221, x_214);
x_230 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 7, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_222);
lean_ctor_set(x_231, 2, x_223);
lean_ctor_set(x_231, 3, x_224);
lean_ctor_set(x_231, 4, x_230);
lean_ctor_set(x_231, 5, x_225);
lean_ctor_set(x_231, 6, x_226);
x_232 = lean_st_ref_set(x_5, x_231, x_220);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_st_ref_take(x_3, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6;
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 5, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_239);
lean_ctor_set(x_243, 4, x_240);
x_244 = lean_st_ref_set(x_3, x_243, x_236);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = lean_st_ref_take(x_5, x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_247, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_247, 5);
lean_inc(x_253);
x_254 = lean_ctor_get(x_247, 6);
lean_inc(x_254);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 lean_ctor_release(x_247, 4);
 lean_ctor_release(x_247, 5);
 lean_ctor_release(x_247, 6);
 x_255 = x_247;
} else {
 lean_dec_ref(x_247);
 x_255 = lean_box(0);
}
x_256 = l_mkRecOn___closed__7;
x_257 = l_Lean_TagDeclarationExtension_tag(x_256, x_249, x_214);
if (lean_is_scalar(x_255)) {
 x_258 = lean_alloc_ctor(0, 7, 0);
} else {
 x_258 = x_255;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_250);
lean_ctor_set(x_258, 2, x_251);
lean_ctor_set(x_258, 3, x_252);
lean_ctor_set(x_258, 4, x_230);
lean_ctor_set(x_258, 5, x_253);
lean_ctor_set(x_258, 6, x_254);
x_259 = lean_st_ref_set(x_5, x_258, x_248);
lean_dec(x_5);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_st_ref_take(x_3, x_260);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_262, 4);
lean_inc(x_267);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 x_268 = x_262;
} else {
 lean_dec_ref(x_262);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_242);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set(x_269, 4, x_267);
x_270 = lean_st_ref_set(x_3, x_269, x_263);
lean_dec(x_3);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_box(0);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_271);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_208);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_275 = lean_ctor_get(x_211, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_211, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_277 = x_211;
} else {
 lean_dec_ref(x_211);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_281 = x_207;
} else {
 lean_dec_ref(x_207);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_10);
lean_dec(x_1);
x_283 = lean_ctor_get(x_9, 1);
lean_inc(x_283);
lean_dec(x_9);
x_284 = l_Lean_MessageData_ofName(x_8);
x_285 = l_mkRecOn___closed__3;
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
x_287 = l_mkRecOn___closed__5;
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_288, x_2, x_3, x_4, x_5, x_283);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_289;
}
}
else
{
uint8_t x_290; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_9);
if (x_290 == 0)
{
return x_9;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_9, 0);
x_292 = lean_ctor_get(x_9, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_9);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_mkRecOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_mkRecOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_RecOn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__1);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__2);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__5);
l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6 = _init_l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__6);
l_mkRecOn___closed__1 = _init_l_mkRecOn___closed__1();
lean_mark_persistent(l_mkRecOn___closed__1);
l_mkRecOn___closed__2 = _init_l_mkRecOn___closed__2();
lean_mark_persistent(l_mkRecOn___closed__2);
l_mkRecOn___closed__3 = _init_l_mkRecOn___closed__3();
lean_mark_persistent(l_mkRecOn___closed__3);
l_mkRecOn___closed__4 = _init_l_mkRecOn___closed__4();
lean_mark_persistent(l_mkRecOn___closed__4);
l_mkRecOn___closed__5 = _init_l_mkRecOn___closed__5();
lean_mark_persistent(l_mkRecOn___closed__5);
l_mkRecOn___closed__6 = _init_l_mkRecOn___closed__6();
lean_mark_persistent(l_mkRecOn___closed__6);
l_mkRecOn___closed__7 = _init_l_mkRecOn___closed__7();
lean_mark_persistent(l_mkRecOn___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
