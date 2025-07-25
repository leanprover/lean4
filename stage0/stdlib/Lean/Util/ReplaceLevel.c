// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: Lean.Expr
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
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr;
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(uint8_t, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
static size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
static lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Level_replace(x_1, x_4);
x_6 = l_Lean_mkLevelSucc(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = l_Lean_Level_replace(x_1, x_8);
x_11 = l_Lean_mkLevelMax_x27(x_9, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Level_replace(x_1, x_12);
x_15 = l_Lean_Level_replace(x_1, x_13);
x_16 = l_Lean_mkLevelIMax_x27(x_14, x_15);
return x_16;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec_ref(x_3);
return x_17;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 8192;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_uset(x_6, x_1, x_2);
lean_inc_ref(x_3);
x_9 = lean_array_uset(x_7, x_1, x_3);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_array_uset(x_11, x_1, x_2);
lean_inc_ref(x_3);
x_14 = lean_array_uset(x_12, x_1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceLevelImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_8 = l_Lean_Level_replace(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_Level_replace(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_mod(x_7, x_2);
x_9 = lean_array_uget(x_5, x_8);
lean_dec_ref(x_5);
x_10 = lean_ptr_addr(x_9);
lean_dec_ref(x_9);
x_11 = lean_usize_dec_eq(x_10, x_7);
if (x_11 == 0)
{
lean_dec_ref(x_6);
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace(x_1, x_12);
x_14 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_3, x_13);
x_15 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_14, x_4);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_16, x_17);
lean_inc_ref(x_3);
x_19 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(x_3, x_18);
x_20 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_19, x_4);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_22);
lean_inc_ref(x_1);
x_23 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_21, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_22, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_3, x_24, x_27);
x_30 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_29, x_28);
return x_30;
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; size_t x_49; size_t x_50; uint8_t x_51; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_33);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_32);
lean_inc_ref(x_1);
x_35 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_32, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc_ref(x_33);
x_38 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_33, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_49 = lean_ptr_addr(x_32);
lean_dec_ref(x_32);
x_50 = lean_ptr_addr(x_36);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_dec_ref(x_33);
x_41 = x_51;
goto block_48;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = lean_ptr_addr(x_33);
lean_dec_ref(x_33);
x_53 = lean_ptr_addr(x_39);
x_54 = lean_usize_dec_eq(x_52, x_53);
x_41 = x_54;
goto block_48;
}
block_48:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Expr_lam___override(x_31, x_36, x_39, x_34);
x_43 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_42, x_40);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_34, x_34);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Expr_lam___override(x_31, x_36, x_39, x_34);
x_46 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_45, x_40);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_31);
lean_inc_ref(x_3);
x_47 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_40);
return x_47;
}
}
}
}
case 7:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; size_t x_73; size_t x_74; uint8_t x_75; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_56);
lean_inc_ref(x_1);
x_59 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
lean_inc_ref(x_57);
x_62 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_57, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_73 = lean_ptr_addr(x_56);
lean_dec_ref(x_56);
x_74 = lean_ptr_addr(x_60);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_dec_ref(x_57);
x_65 = x_75;
goto block_72;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_57);
lean_dec_ref(x_57);
x_77 = lean_ptr_addr(x_63);
x_78 = lean_usize_dec_eq(x_76, x_77);
x_65 = x_78;
goto block_72;
}
block_72:
{
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Expr_forallE___override(x_55, x_60, x_63, x_58);
x_67 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_66, x_64);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_58, x_58);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_forallE___override(x_55, x_60, x_63, x_58);
x_70 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_69, x_64);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_55);
lean_inc_ref(x_3);
x_71 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_64);
return x_71;
}
}
}
}
case 8:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; size_t x_103; size_t x_104; uint8_t x_105; 
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_82);
x_83 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc_ref(x_80);
lean_inc_ref(x_1);
x_84 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_80, x_4);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
lean_inc_ref(x_81);
lean_inc_ref(x_1);
x_87 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_81, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
lean_inc_ref(x_82);
x_90 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_82, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_103 = lean_ptr_addr(x_80);
lean_dec_ref(x_80);
x_104 = lean_ptr_addr(x_85);
x_105 = lean_usize_dec_eq(x_103, x_104);
if (x_105 == 0)
{
lean_dec_ref(x_81);
x_93 = x_105;
goto block_102;
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_81);
lean_dec_ref(x_81);
x_107 = lean_ptr_addr(x_88);
x_108 = lean_usize_dec_eq(x_106, x_107);
x_93 = x_108;
goto block_102;
}
block_102:
{
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_82);
x_94 = l_Lean_Expr_letE___override(x_79, x_85, x_88, x_91, x_83);
x_95 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_94, x_92);
return x_95;
}
else
{
size_t x_96; size_t x_97; uint8_t x_98; 
x_96 = lean_ptr_addr(x_82);
lean_dec_ref(x_82);
x_97 = lean_ptr_addr(x_91);
x_98 = lean_usize_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Expr_letE___override(x_79, x_85, x_88, x_91, x_83);
x_100 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_99, x_92);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_79);
lean_inc_ref(x_3);
x_101 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_92);
return x_101;
}
}
}
}
case 10:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_109);
x_110 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_109, x_4);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc_ref(x_3);
x_113 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_3, x_111);
x_114 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_113, x_112);
return x_114;
}
case 11:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_115);
x_116 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_115, x_4);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
lean_inc_ref(x_3);
x_119 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_3, x_117);
x_120 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_119, x_118);
return x_120;
}
default: 
{
lean_object* x_121; 
lean_dec_ref(x_1);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_3);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_122 = lean_array_uget(x_6, x_8);
lean_dec_ref(x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_4);
return x_123;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
x_2 = lean_usize_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Level_replace(x_1, x_3);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_2, x_4);
lean_dec_ref(x_2);
return x_5;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_6, x_7);
x_9 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(x_2, x_8);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_12 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_10);
x_13 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_11);
x_14 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_2, x_12, x_13);
lean_dec_ref(x_2);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; size_t x_26; size_t x_27; uint8_t x_28; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_16);
lean_inc_ref(x_1);
x_19 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_16);
lean_inc_ref(x_17);
x_20 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_17);
x_26 = lean_ptr_addr(x_16);
lean_dec_ref(x_16);
x_27 = lean_ptr_addr(x_19);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_17);
x_21 = x_28;
goto block_25;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_17);
lean_dec_ref(x_17);
x_30 = lean_ptr_addr(x_20);
x_31 = lean_usize_dec_eq(x_29, x_30);
x_21 = x_31;
goto block_25;
}
block_25:
{
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_2);
x_22 = l_Lean_Expr_lam___override(x_15, x_19, x_20, x_18);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_18, x_18);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = l_Lean_Expr_lam___override(x_15, x_19, x_20, x_18);
return x_24;
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_15);
return x_2;
}
}
}
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; size_t x_43; size_t x_44; uint8_t x_45; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_34);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_33);
lean_inc_ref(x_1);
x_36 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_33);
lean_inc_ref(x_34);
x_37 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_34);
x_43 = lean_ptr_addr(x_33);
lean_dec_ref(x_33);
x_44 = lean_ptr_addr(x_36);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_dec_ref(x_34);
x_38 = x_45;
goto block_42;
}
else
{
size_t x_46; size_t x_47; uint8_t x_48; 
x_46 = lean_ptr_addr(x_34);
lean_dec_ref(x_34);
x_47 = lean_ptr_addr(x_37);
x_48 = lean_usize_dec_eq(x_46, x_47);
x_38 = x_48;
goto block_42;
}
block_42:
{
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_2);
x_39 = l_Lean_Expr_forallE___override(x_32, x_36, x_37, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_35, x_35);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_2);
x_41 = l_Lean_Expr_forallE___override(x_32, x_36, x_37, x_35);
return x_41;
}
else
{
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_32);
return x_2;
}
}
}
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; size_t x_64; size_t x_65; uint8_t x_66; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc_ref(x_50);
lean_inc_ref(x_1);
x_54 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_50);
lean_inc_ref(x_51);
lean_inc_ref(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_51);
lean_inc_ref(x_52);
x_56 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_52);
x_64 = lean_ptr_addr(x_50);
lean_dec_ref(x_50);
x_65 = lean_ptr_addr(x_54);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_dec_ref(x_51);
x_57 = x_66;
goto block_63;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_51);
lean_dec_ref(x_51);
x_68 = lean_ptr_addr(x_55);
x_69 = lean_usize_dec_eq(x_67, x_68);
x_57 = x_69;
goto block_63;
}
block_63:
{
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_52);
lean_dec_ref(x_2);
x_58 = l_Lean_Expr_letE___override(x_49, x_54, x_55, x_56, x_53);
return x_58;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_52);
lean_dec_ref(x_52);
x_60 = lean_ptr_addr(x_56);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec_ref(x_2);
x_62 = l_Lean_Expr_letE___override(x_49, x_54, x_55, x_56, x_53);
return x_62;
}
else
{
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_49);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_70);
x_71 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_70);
x_72 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_2, x_71);
return x_72;
}
case 11:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_73);
x_74 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_73);
x_75 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_2, x_74);
return x_75;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0 = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0();
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0 = _init_l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0();
lean_mark_persistent(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0);
l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr = _init_l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr();
lean_mark_persistent(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6);
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
