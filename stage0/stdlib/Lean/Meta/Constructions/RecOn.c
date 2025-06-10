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
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_recOnSuffix;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at_mkRecOn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
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
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_12, x_1, x_2, x_14, x_15);
x_17 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
lean_ctor_set(x_9, 5, x_17);
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
x_25 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
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
x_37 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 6);
x_50 = lean_ctor_get(x_9, 7);
x_51 = lean_ctor_get(x_9, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_52 = 0;
x_53 = lean_box(0);
x_54 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_44, x_1, x_2, x_52, x_53);
x_55 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_49);
lean_ctor_set(x_56, 7, x_50);
lean_ctor_set(x_56, 8, x_51);
x_57 = lean_st_ref_set(x_6, x_56, x_10);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_4, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 4);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
x_69 = lean_st_ref_set(x_4, x_68, x_61);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
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
lean_dec(x_41);
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
x_33 = lean_ctor_get(x_29, 5);
lean_dec(x_33);
x_34 = l_mkRecOn___closed__6;
lean_inc(x_24);
x_35 = l_Lean_TagDeclarationExtension_tag(x_34, x_32, x_24);
x_36 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
lean_ctor_set(x_29, 5, x_36);
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
x_44 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
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
x_52 = lean_ctor_get(x_48, 5);
lean_dec(x_52);
x_53 = l_mkRecOn___closed__7;
x_54 = l_Lean_TagDeclarationExtension_tag(x_53, x_51, x_24);
lean_ctor_set(x_48, 5, x_36);
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
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_79 = lean_ctor_get(x_48, 0);
x_80 = lean_ctor_get(x_48, 1);
x_81 = lean_ctor_get(x_48, 2);
x_82 = lean_ctor_get(x_48, 3);
x_83 = lean_ctor_get(x_48, 4);
x_84 = lean_ctor_get(x_48, 6);
x_85 = lean_ctor_get(x_48, 7);
x_86 = lean_ctor_get(x_48, 8);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_48);
x_87 = l_mkRecOn___closed__7;
x_88 = l_Lean_TagDeclarationExtension_tag(x_87, x_79, x_24);
x_89 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set(x_89, 4, x_83);
lean_ctor_set(x_89, 5, x_36);
lean_ctor_set(x_89, 6, x_84);
lean_ctor_set(x_89, 7, x_85);
lean_ctor_set(x_89, 8, x_86);
x_90 = lean_st_ref_set(x_5, x_89, x_49);
lean_dec(x_5);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_take(x_3, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 4);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_44);
lean_ctor_set(x_100, 2, x_96);
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set(x_100, 4, x_98);
x_101 = lean_st_ref_set(x_3, x_100, x_94);
lean_dec(x_3);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_106 = lean_ctor_get(x_40, 0);
x_107 = lean_ctor_get(x_40, 2);
x_108 = lean_ctor_get(x_40, 3);
x_109 = lean_ctor_get(x_40, 4);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_40);
x_110 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_109);
x_112 = lean_st_ref_set(x_3, x_111, x_41);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_st_ref_take(x_5, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 6);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 7);
lean_inc(x_123);
x_124 = lean_ctor_get(x_115, 8);
lean_inc(x_124);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 lean_ctor_release(x_115, 6);
 lean_ctor_release(x_115, 7);
 lean_ctor_release(x_115, 8);
 x_125 = x_115;
} else {
 lean_dec_ref(x_115);
 x_125 = lean_box(0);
}
x_126 = l_mkRecOn___closed__7;
x_127 = l_Lean_TagDeclarationExtension_tag(x_126, x_117, x_24);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 9, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_118);
lean_ctor_set(x_128, 2, x_119);
lean_ctor_set(x_128, 3, x_120);
lean_ctor_set(x_128, 4, x_121);
lean_ctor_set(x_128, 5, x_36);
lean_ctor_set(x_128, 6, x_122);
lean_ctor_set(x_128, 7, x_123);
lean_ctor_set(x_128, 8, x_124);
x_129 = lean_st_ref_set(x_5, x_128, x_116);
lean_dec(x_5);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_take(x_3, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 4);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_110);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
lean_ctor_set(x_139, 4, x_137);
x_140 = lean_st_ref_set(x_3, x_139, x_133);
lean_dec(x_3);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = lean_box(0);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_145 = lean_ctor_get(x_29, 0);
x_146 = lean_ctor_get(x_29, 1);
x_147 = lean_ctor_get(x_29, 2);
x_148 = lean_ctor_get(x_29, 3);
x_149 = lean_ctor_get(x_29, 4);
x_150 = lean_ctor_get(x_29, 6);
x_151 = lean_ctor_get(x_29, 7);
x_152 = lean_ctor_get(x_29, 8);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_29);
x_153 = l_mkRecOn___closed__6;
lean_inc(x_24);
x_154 = l_Lean_TagDeclarationExtension_tag(x_153, x_145, x_24);
x_155 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
x_156 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_146);
lean_ctor_set(x_156, 2, x_147);
lean_ctor_set(x_156, 3, x_148);
lean_ctor_set(x_156, 4, x_149);
lean_ctor_set(x_156, 5, x_155);
lean_ctor_set(x_156, 6, x_150);
lean_ctor_set(x_156, 7, x_151);
lean_ctor_set(x_156, 8, x_152);
x_157 = lean_st_ref_set(x_5, x_156, x_30);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_st_ref_take(x_3, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 5, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set(x_168, 4, x_165);
x_169 = lean_st_ref_set(x_3, x_168, x_161);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_5, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 6);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 7);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 8);
lean_inc(x_181);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 lean_ctor_release(x_172, 5);
 lean_ctor_release(x_172, 6);
 lean_ctor_release(x_172, 7);
 lean_ctor_release(x_172, 8);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
x_183 = l_mkRecOn___closed__7;
x_184 = l_Lean_TagDeclarationExtension_tag(x_183, x_174, x_24);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(0, 9, 0);
} else {
 x_185 = x_182;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_175);
lean_ctor_set(x_185, 2, x_176);
lean_ctor_set(x_185, 3, x_177);
lean_ctor_set(x_185, 4, x_178);
lean_ctor_set(x_185, 5, x_155);
lean_ctor_set(x_185, 6, x_179);
lean_ctor_set(x_185, 7, x_180);
lean_ctor_set(x_185, 8, x_181);
x_186 = lean_st_ref_set(x_5, x_185, x_173);
lean_dec(x_5);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_st_ref_take(x_3, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 4);
lean_inc(x_194);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 x_195 = x_189;
} else {
 lean_dec_ref(x_189);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_167);
lean_ctor_set(x_196, 2, x_192);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 4, x_194);
x_197 = lean_st_ref_set(x_3, x_196, x_190);
lean_dec(x_3);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
}
else
{
uint8_t x_202; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_21);
if (x_202 == 0)
{
return x_21;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_21, 0);
x_204 = lean_ctor_get(x_21, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_21);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_free_object(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_18);
if (x_206 == 0)
{
return x_18;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_18, 0);
x_208 = lean_ctor_get(x_18, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_18);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_10, 0);
lean_inc(x_210);
lean_dec(x_10);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 2);
lean_inc(x_212);
x_213 = lean_alloc_closure((void*)(l_mkRecOn___lambda__1___boxed), 10, 3);
lean_closure_set(x_213, 0, x_211);
lean_closure_set(x_213, 1, x_210);
lean_closure_set(x_213, 2, x_1);
x_214 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_215 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_212, x_213, x_214, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_216);
lean_inc(x_5);
lean_inc(x_4);
x_219 = l_Lean_addDecl(x_218, x_4, x_5, x_217);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_ctor_get(x_216, 0);
lean_inc(x_221);
lean_dec(x_216);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec(x_221);
x_223 = 0;
lean_inc(x_222);
x_224 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3(x_222, x_223, x_2, x_3, x_4, x_5, x_220);
lean_dec(x_4);
lean_dec(x_2);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_take(x_5, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_227, 4);
lean_inc(x_233);
x_234 = lean_ctor_get(x_227, 6);
lean_inc(x_234);
x_235 = lean_ctor_get(x_227, 7);
lean_inc(x_235);
x_236 = lean_ctor_get(x_227, 8);
lean_inc(x_236);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 lean_ctor_release(x_227, 4);
 lean_ctor_release(x_227, 5);
 lean_ctor_release(x_227, 6);
 lean_ctor_release(x_227, 7);
 lean_ctor_release(x_227, 8);
 x_237 = x_227;
} else {
 lean_dec_ref(x_227);
 x_237 = lean_box(0);
}
x_238 = l_mkRecOn___closed__6;
lean_inc(x_222);
x_239 = l_Lean_TagDeclarationExtension_tag(x_238, x_229, x_222);
x_240 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__3;
if (lean_is_scalar(x_237)) {
 x_241 = lean_alloc_ctor(0, 9, 0);
} else {
 x_241 = x_237;
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_230);
lean_ctor_set(x_241, 2, x_231);
lean_ctor_set(x_241, 3, x_232);
lean_ctor_set(x_241, 4, x_233);
lean_ctor_set(x_241, 5, x_240);
lean_ctor_set(x_241, 6, x_234);
lean_ctor_set(x_241, 7, x_235);
lean_ctor_set(x_241, 8, x_236);
x_242 = lean_st_ref_set(x_5, x_241, x_228);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_st_ref_take(x_3, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_245, 4);
lean_inc(x_250);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 lean_ctor_release(x_245, 3);
 lean_ctor_release(x_245, 4);
 x_251 = x_245;
} else {
 lean_dec_ref(x_245);
 x_251 = lean_box(0);
}
x_252 = l_Lean_setReducibilityStatus___at_mkRecOn___spec__3___closed__4;
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 5, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_247);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_249);
lean_ctor_set(x_253, 4, x_250);
x_254 = lean_st_ref_set(x_3, x_253, x_246);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_st_ref_take(x_5, x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 3);
lean_inc(x_262);
x_263 = lean_ctor_get(x_257, 4);
lean_inc(x_263);
x_264 = lean_ctor_get(x_257, 6);
lean_inc(x_264);
x_265 = lean_ctor_get(x_257, 7);
lean_inc(x_265);
x_266 = lean_ctor_get(x_257, 8);
lean_inc(x_266);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 lean_ctor_release(x_257, 5);
 lean_ctor_release(x_257, 6);
 lean_ctor_release(x_257, 7);
 lean_ctor_release(x_257, 8);
 x_267 = x_257;
} else {
 lean_dec_ref(x_257);
 x_267 = lean_box(0);
}
x_268 = l_mkRecOn___closed__7;
x_269 = l_Lean_TagDeclarationExtension_tag(x_268, x_259, x_222);
if (lean_is_scalar(x_267)) {
 x_270 = lean_alloc_ctor(0, 9, 0);
} else {
 x_270 = x_267;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_260);
lean_ctor_set(x_270, 2, x_261);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set(x_270, 4, x_263);
lean_ctor_set(x_270, 5, x_240);
lean_ctor_set(x_270, 6, x_264);
lean_ctor_set(x_270, 7, x_265);
lean_ctor_set(x_270, 8, x_266);
x_271 = lean_st_ref_set(x_5, x_270, x_258);
lean_dec(x_5);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_st_ref_take(x_3, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 lean_ctor_release(x_274, 4);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_252);
lean_ctor_set(x_281, 2, x_277);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_279);
x_282 = lean_st_ref_set(x_3, x_281, x_275);
lean_dec(x_3);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_284 = x_282;
} else {
 lean_dec_ref(x_282);
 x_284 = lean_box(0);
}
x_285 = lean_box(0);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_216);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_287 = lean_ctor_get(x_219, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_219, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_289 = x_219;
} else {
 lean_dec_ref(x_219);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_ctor_get(x_215, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_215, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_293 = x_215;
} else {
 lean_dec_ref(x_215);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_10);
lean_dec(x_1);
x_295 = lean_ctor_get(x_9, 1);
lean_inc(x_295);
lean_dec(x_9);
x_296 = l_Lean_MessageData_ofName(x_8);
x_297 = l_mkRecOn___closed__3;
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_299 = l_mkRecOn___closed__5;
x_300 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_300, x_2, x_3, x_4, x_5, x_295);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_301;
}
}
else
{
uint8_t x_302; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_9);
if (x_302 == 0)
{
return x_9;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_9, 0);
x_304 = lean_ctor_get(x_9, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_9);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
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
