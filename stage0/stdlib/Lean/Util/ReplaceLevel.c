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
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_State_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(uint8_t, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
static lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
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
x_6 = l_Lean_Level_succ___override(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ReplaceLevelImpl_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_mod(x_7, x_2);
x_9 = lean_array_uget(x_5, x_8);
x_10 = lean_ptr_addr(x_9);
lean_dec_ref(x_9);
x_11 = lean_usize_dec_eq(x_10, x_7);
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace(x_1, x_12);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_ptr_addr(x_13);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_sort___override(x_13);
x_18 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_17, x_4);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_13);
lean_inc_ref(x_3);
x_19 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_19;
}
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_box(0);
lean_inc(x_21);
x_23 = l_List_mapTR_loop___at_____private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_21, x_22);
x_24 = l_ptrEqList___redArg(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_20);
x_25 = l_Lean_Expr_const___override(x_20, x_23);
x_26 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_25, x_4);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_inc_ref(x_3);
x_27 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_27;
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; size_t x_41; size_t x_42; uint8_t x_43; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_28);
lean_inc_ref(x_1);
x_30 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc_ref(x_29);
x_33 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_29, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_41 = lean_ptr_addr(x_28);
x_42 = lean_ptr_addr(x_31);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
x_36 = x_43;
goto block_40;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_29);
x_45 = lean_ptr_addr(x_34);
x_46 = lean_usize_dec_eq(x_44, x_45);
x_36 = x_46;
goto block_40;
}
block_40:
{
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_app___override(x_31, x_34);
x_38 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_37, x_35);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_31);
lean_inc_ref(x_3);
x_39 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_35);
return x_39;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; size_t x_65; size_t x_66; uint8_t x_67; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_48);
lean_inc_ref(x_1);
x_51 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_48, x_4);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
lean_inc_ref(x_49);
x_54 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_49, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_65 = lean_ptr_addr(x_48);
x_66 = lean_ptr_addr(x_52);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
x_57 = x_67;
goto block_64;
}
else
{
size_t x_68; size_t x_69; uint8_t x_70; 
x_68 = lean_ptr_addr(x_49);
x_69 = lean_ptr_addr(x_55);
x_70 = lean_usize_dec_eq(x_68, x_69);
x_57 = x_70;
goto block_64;
}
block_64:
{
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_inc(x_47);
x_58 = l_Lean_Expr_lam___override(x_47, x_52, x_55, x_50);
x_59 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_58, x_56);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_50, x_50);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_47);
x_61 = l_Lean_Expr_lam___override(x_47, x_52, x_55, x_50);
x_62 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_61, x_56);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_55);
lean_dec(x_52);
lean_inc_ref(x_3);
x_63 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_56);
return x_63;
}
}
}
}
case 7:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; size_t x_89; size_t x_90; uint8_t x_91; 
x_71 = lean_ctor_get(x_3, 0);
x_72 = lean_ctor_get(x_3, 1);
x_73 = lean_ctor_get(x_3, 2);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_72);
lean_inc_ref(x_1);
x_75 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_72, x_4);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
lean_inc_ref(x_73);
x_78 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_73, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_89 = lean_ptr_addr(x_72);
x_90 = lean_ptr_addr(x_76);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
x_81 = x_91;
goto block_88;
}
else
{
size_t x_92; size_t x_93; uint8_t x_94; 
x_92 = lean_ptr_addr(x_73);
x_93 = lean_ptr_addr(x_79);
x_94 = lean_usize_dec_eq(x_92, x_93);
x_81 = x_94;
goto block_88;
}
block_88:
{
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_inc(x_71);
x_82 = l_Lean_Expr_forallE___override(x_71, x_76, x_79, x_74);
x_83 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_82, x_80);
return x_83;
}
else
{
uint8_t x_84; 
x_84 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_74, x_74);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_inc(x_71);
x_85 = l_Lean_Expr_forallE___override(x_71, x_76, x_79, x_74);
x_86 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_85, x_80);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_79);
lean_dec(x_76);
lean_inc_ref(x_3);
x_87 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_80);
return x_87;
}
}
}
}
case 8:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; size_t x_119; size_t x_120; uint8_t x_121; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get(x_3, 2);
x_98 = lean_ctor_get(x_3, 3);
x_99 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc_ref(x_96);
lean_inc_ref(x_1);
x_100 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_96, x_4);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
lean_inc_ref(x_97);
lean_inc_ref(x_1);
x_103 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
lean_inc_ref(x_98);
x_106 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_98, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_119 = lean_ptr_addr(x_96);
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
x_109 = x_121;
goto block_118;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_97);
x_123 = lean_ptr_addr(x_104);
x_124 = lean_usize_dec_eq(x_122, x_123);
x_109 = x_124;
goto block_118;
}
block_118:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_inc(x_95);
x_110 = l_Lean_Expr_letE___override(x_95, x_101, x_104, x_107, x_99);
x_111 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_110, x_108);
return x_111;
}
else
{
size_t x_112; size_t x_113; uint8_t x_114; 
x_112 = lean_ptr_addr(x_98);
x_113 = lean_ptr_addr(x_107);
x_114 = lean_usize_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_inc(x_95);
x_115 = l_Lean_Expr_letE___override(x_95, x_101, x_104, x_107, x_99);
x_116 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_115, x_108);
return x_116;
}
else
{
lean_object* x_117; 
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_101);
lean_inc_ref(x_3);
x_117 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_108);
return x_117;
}
}
}
}
case 10:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; size_t x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_3, 0);
x_126 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_126);
x_127 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_126, x_4);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_ptr_addr(x_126);
x_131 = lean_ptr_addr(x_128);
x_132 = lean_usize_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_inc(x_125);
x_133 = l_Lean_Expr_mdata___override(x_125, x_128);
x_134 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_133, x_129);
return x_134;
}
else
{
lean_object* x_135; 
lean_dec(x_128);
lean_inc_ref(x_3);
x_135 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_129);
return x_135;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; uint8_t x_144; 
x_136 = lean_ctor_get(x_3, 0);
x_137 = lean_ctor_get(x_3, 1);
x_138 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_138);
x_139 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_138, x_4);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = lean_ptr_addr(x_138);
x_143 = lean_ptr_addr(x_140);
x_144 = lean_usize_dec_eq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_inc(x_137);
lean_inc(x_136);
x_145 = l_Lean_Expr_proj___override(x_136, x_137, x_140);
x_146 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_145, x_141);
return x_146;
}
else
{
lean_object* x_147; 
lean_dec(x_140);
lean_inc_ref(x_3);
x_147 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_141);
return x_147;
}
}
default: 
{
lean_object* x_148; 
lean_dec_ref(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_149 = lean_array_uget(x_6, x_8);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_4);
return x_150;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
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
x_5 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
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
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Level_replace(x_1, x_3);
x_5 = lean_ptr_addr(x_3);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_2);
x_8 = l_Lean_Expr_sort___override(x_4);
return x_8;
}
else
{
lean_dec(x_4);
return x_2;
}
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = l_List_mapTR_loop___at_____private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_10, x_11);
x_13 = l_ptrEqList___redArg(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_9);
lean_dec_ref(x_2);
x_14 = l_Lean_Expr_const___override(x_9, x_12);
return x_14;
}
else
{
lean_dec(x_12);
return x_2;
}
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; size_t x_22; size_t x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_15);
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_15);
lean_inc_ref(x_16);
x_18 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_16);
x_22 = lean_ptr_addr(x_15);
x_23 = lean_ptr_addr(x_17);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
x_19 = x_24;
goto block_21;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_16);
x_26 = lean_ptr_addr(x_18);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_19 = x_27;
goto block_21;
}
block_21:
{
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_2);
x_20 = l_Lean_Expr_app___override(x_17, x_18);
return x_20;
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
return x_2;
}
}
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; size_t x_39; size_t x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_29);
lean_inc_ref(x_1);
x_32 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_29);
lean_inc_ref(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_30);
x_39 = lean_ptr_addr(x_29);
x_40 = lean_ptr_addr(x_32);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
x_34 = x_41;
goto block_38;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_30);
x_43 = lean_ptr_addr(x_33);
x_44 = lean_usize_dec_eq(x_42, x_43);
x_34 = x_44;
goto block_38;
}
block_38:
{
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_28);
lean_dec_ref(x_2);
x_35 = l_Lean_Expr_lam___override(x_28, x_32, x_33, x_31);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_31, x_31);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_28);
lean_dec_ref(x_2);
x_37 = l_Lean_Expr_lam___override(x_28, x_32, x_33, x_31);
return x_37;
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
return x_2;
}
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; size_t x_56; size_t x_57; uint8_t x_58; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_46);
lean_inc_ref(x_1);
x_49 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_46);
lean_inc_ref(x_47);
x_50 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_47);
x_56 = lean_ptr_addr(x_46);
x_57 = lean_ptr_addr(x_49);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
x_51 = x_58;
goto block_55;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_47);
x_60 = lean_ptr_addr(x_50);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_51 = x_61;
goto block_55;
}
block_55:
{
if (x_51 == 0)
{
lean_object* x_52; 
lean_inc(x_45);
lean_dec_ref(x_2);
x_52 = l_Lean_Expr_forallE___override(x_45, x_49, x_50, x_48);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_48, x_48);
if (x_53 == 0)
{
lean_object* x_54; 
lean_inc(x_45);
lean_dec_ref(x_2);
x_54 = l_Lean_Expr_forallE___override(x_45, x_49, x_50, x_48);
return x_54;
}
else
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
return x_2;
}
}
}
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; size_t x_77; size_t x_78; uint8_t x_79; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc_ref(x_63);
lean_inc_ref(x_1);
x_67 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_63);
lean_inc_ref(x_64);
lean_inc_ref(x_1);
x_68 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_64);
lean_inc_ref(x_65);
x_69 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_65);
x_77 = lean_ptr_addr(x_63);
x_78 = lean_ptr_addr(x_67);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
x_70 = x_79;
goto block_76;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_64);
x_81 = lean_ptr_addr(x_68);
x_82 = lean_usize_dec_eq(x_80, x_81);
x_70 = x_82;
goto block_76;
}
block_76:
{
if (x_70 == 0)
{
lean_object* x_71; 
lean_inc(x_62);
lean_dec_ref(x_2);
x_71 = l_Lean_Expr_letE___override(x_62, x_67, x_68, x_69, x_66);
return x_71;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_65);
x_73 = lean_ptr_addr(x_69);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_inc(x_62);
lean_dec_ref(x_2);
x_75 = l_Lean_Expr_letE___override(x_62, x_67, x_68, x_69, x_66);
return x_75;
}
else
{
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_84);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_84);
x_86 = lean_ptr_addr(x_84);
x_87 = lean_ptr_addr(x_85);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_inc(x_83);
lean_dec_ref(x_2);
x_89 = l_Lean_Expr_mdata___override(x_83, x_85);
return x_89;
}
else
{
lean_dec_ref(x_85);
return x_2;
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_2, 0);
x_91 = lean_ctor_get(x_2, 1);
x_92 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_92);
x_93 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_92);
x_94 = lean_ptr_addr(x_92);
x_95 = lean_ptr_addr(x_93);
x_96 = lean_usize_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_inc(x_91);
lean_inc(x_90);
lean_dec_ref(x_2);
x_97 = l_Lean_Expr_proj___override(x_90, x_91, x_93);
return x_97;
}
else
{
lean_dec_ref(x_93);
return x_2;
}
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
