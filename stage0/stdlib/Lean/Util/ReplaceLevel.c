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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
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
lean_dec(x_2);
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
lean_dec(x_2);
lean_inc(x_1);
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
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Level_replace(x_1, x_12);
x_15 = l_Lean_Level_replace(x_1, x_13);
x_16 = l_Lean_mkLevelIMax_x27(x_14, x_15);
return x_16;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
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
lean_inc(x_3);
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
lean_inc(x_3);
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
lean_dec(x_1);
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
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_6);
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
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_10);
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
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_mod(x_7, x_2);
x_9 = lean_array_uget(x_5, x_8);
lean_dec(x_5);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = lean_usize_dec_eq(x_10, x_7);
if (x_11 == 0)
{
lean_dec(x_6);
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_inc(x_12);
x_13 = l_Lean_Level_replace(x_1, x_12);
x_14 = lean_ptr_addr(x_12);
lean_dec(x_12);
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
lean_inc(x_3);
x_19 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_19;
}
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_Lean_Level_replace), 2, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = lean_box(0);
lean_inc(x_21);
x_24 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_22, x_21, x_23);
x_25 = l_ptrEqList___redArg(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Expr_const___override(x_20, x_24);
x_27 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_26, x_4);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_20);
lean_inc(x_3);
x_28 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_28;
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; size_t x_42; size_t x_43; uint8_t x_44; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_1);
x_31 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_29, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_30);
x_34 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_30, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_42 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_43 = lean_ptr_addr(x_32);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_dec(x_30);
x_37 = x_44;
goto block_41;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_46 = lean_ptr_addr(x_35);
x_47 = lean_usize_dec_eq(x_45, x_46);
x_37 = x_47;
goto block_41;
}
block_41:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Expr_app___override(x_32, x_35);
x_39 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_38, x_36);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_32);
lean_inc(x_3);
x_40 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_36);
return x_40;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; size_t x_66; size_t x_67; uint8_t x_68; 
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_49);
lean_inc(x_1);
x_52 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_49, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_50, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_66 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_67 = lean_ptr_addr(x_53);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_dec(x_50);
x_58 = x_68;
goto block_65;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_70 = lean_ptr_addr(x_56);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_58 = x_71;
goto block_65;
}
block_65:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Expr_lam___override(x_48, x_53, x_56, x_51);
x_60 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_59, x_57);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_51, x_51);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Expr_lam___override(x_48, x_53, x_56, x_51);
x_63 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_62, x_57);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_3);
x_64 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_57);
return x_64;
}
}
}
}
case 7:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; size_t x_90; size_t x_91; uint8_t x_92; 
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 2);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_73);
lean_inc(x_1);
x_76 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_73, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_74);
x_79 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_74, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_90 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_91 = lean_ptr_addr(x_77);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_dec(x_74);
x_82 = x_92;
goto block_89;
}
else
{
size_t x_93; size_t x_94; uint8_t x_95; 
x_93 = lean_ptr_addr(x_74);
lean_dec(x_74);
x_94 = lean_ptr_addr(x_80);
x_95 = lean_usize_dec_eq(x_93, x_94);
x_82 = x_95;
goto block_89;
}
block_89:
{
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Expr_forallE___override(x_72, x_77, x_80, x_75);
x_84 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_83, x_81);
return x_84;
}
else
{
uint8_t x_85; 
x_85 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_75, x_75);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Expr_forallE___override(x_72, x_77, x_80, x_75);
x_87 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_86, x_81);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_72);
lean_inc(x_3);
x_88 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_81);
return x_88;
}
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; size_t x_120; size_t x_121; uint8_t x_122; 
x_96 = lean_ctor_get(x_3, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_3, 3);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_97);
lean_inc(x_1);
x_101 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_97, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_98);
lean_inc(x_1);
x_104 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_98, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_99);
x_107 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_99, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_120 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_121 = lean_ptr_addr(x_102);
x_122 = lean_usize_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_dec(x_98);
x_110 = x_122;
goto block_119;
}
else
{
size_t x_123; size_t x_124; uint8_t x_125; 
x_123 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_124 = lean_ptr_addr(x_105);
x_125 = lean_usize_dec_eq(x_123, x_124);
x_110 = x_125;
goto block_119;
}
block_119:
{
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
x_111 = l_Lean_Expr_letE___override(x_96, x_102, x_105, x_108, x_100);
x_112 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_111, x_109);
return x_112;
}
else
{
size_t x_113; size_t x_114; uint8_t x_115; 
x_113 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_114 = lean_ptr_addr(x_108);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Expr_letE___override(x_96, x_102, x_105, x_108, x_100);
x_117 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_116, x_109);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_96);
lean_inc(x_3);
x_118 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_109);
return x_118;
}
}
}
}
case 10:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; size_t x_131; size_t x_132; uint8_t x_133; 
x_126 = lean_ctor_get(x_3, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_3, 1);
lean_inc(x_127);
lean_inc(x_127);
x_128 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_127, x_4);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ptr_addr(x_127);
lean_dec(x_127);
x_132 = lean_ptr_addr(x_129);
x_133 = lean_usize_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_Expr_mdata___override(x_126, x_129);
x_135 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_134, x_130);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
lean_inc(x_3);
x_136 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_130);
return x_136;
}
}
case 11:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; uint8_t x_145; 
x_137 = lean_ctor_get(x_3, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 2);
lean_inc(x_139);
lean_inc(x_139);
x_140 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_139, x_4);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_144 = lean_ptr_addr(x_141);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Lean_Expr_proj___override(x_137, x_138, x_141);
x_147 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_146, x_142);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_137);
lean_inc(x_3);
x_148 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_142);
return x_148;
}
}
default: 
{
lean_object* x_149; 
lean_dec(x_1);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_3);
lean_ctor_set(x_149, 1, x_4);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_array_uget(x_6, x_8);
lean_dec(x_6);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_4);
return x_151;
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
x_1 = lean_box(0);
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
lean_dec(x_5);
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
lean_inc(x_3);
x_4 = l_Lean_Level_replace(x_1, x_3);
x_5 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Level_replace), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_11, x_10, x_12);
x_14 = l_ptrEqList___redArg(x_10, x_13);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Expr_const___override(x_9, x_13);
return x_15;
}
else
{
lean_dec(x_13);
lean_dec(x_9);
return x_2;
}
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; size_t x_23; size_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_18 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_16);
lean_inc(x_17);
x_19 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_17);
x_23 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_24 = lean_ptr_addr(x_18);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_17);
x_20 = x_25;
goto block_22;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_27 = lean_ptr_addr(x_19);
x_28 = lean_usize_dec_eq(x_26, x_27);
x_20 = x_28;
goto block_22;
}
block_22:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = l_Lean_Expr_app___override(x_18, x_19);
return x_21;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
return x_2;
}
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; size_t x_40; size_t x_41; uint8_t x_42; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_30);
lean_inc(x_1);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_31);
x_40 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_41 = lean_ptr_addr(x_33);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_31);
x_35 = x_42;
goto block_39;
}
else
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_44 = lean_ptr_addr(x_34);
x_45 = lean_usize_dec_eq(x_43, x_44);
x_35 = x_45;
goto block_39;
}
block_39:
{
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_32, x_32);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_38;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
return x_2;
}
}
}
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; size_t x_57; size_t x_58; uint8_t x_59; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_47);
lean_inc(x_48);
x_51 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_48);
x_57 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_58 = lean_ptr_addr(x_50);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_dec(x_48);
x_52 = x_59;
goto block_56;
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
x_60 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_61 = lean_ptr_addr(x_51);
x_62 = lean_usize_dec_eq(x_60, x_61);
x_52 = x_62;
goto block_56;
}
block_56:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_2);
x_53 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_49, x_49);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_2);
x_55 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_55;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
return x_2;
}
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; size_t x_78; size_t x_79; uint8_t x_80; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_64);
lean_inc(x_1);
x_68 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_64);
lean_inc(x_65);
lean_inc(x_1);
x_69 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_65);
lean_inc(x_66);
x_70 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_66);
x_78 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_79 = lean_ptr_addr(x_68);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_dec(x_65);
x_71 = x_80;
goto block_77;
}
else
{
size_t x_81; size_t x_82; uint8_t x_83; 
x_81 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_82 = lean_ptr_addr(x_69);
x_83 = lean_usize_dec_eq(x_81, x_82);
x_71 = x_83;
goto block_77;
}
block_77:
{
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_66);
lean_dec(x_2);
x_72 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_72;
}
else
{
size_t x_73; size_t x_74; uint8_t x_75; 
x_73 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_74 = lean_ptr_addr(x_70);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_76;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_63);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_inc(x_85);
x_86 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_85);
x_87 = lean_ptr_addr(x_85);
lean_dec(x_85);
x_88 = lean_ptr_addr(x_86);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_2);
x_90 = l_Lean_Expr_mdata___override(x_84, x_86);
return x_90;
}
else
{
lean_dec(x_86);
lean_dec(x_84);
return x_2;
}
}
case 11:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; uint8_t x_97; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
lean_inc(x_93);
x_94 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_93);
x_95 = lean_ptr_addr(x_93);
lean_dec(x_93);
x_96 = lean_ptr_addr(x_94);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_2);
x_98 = l_Lean_Expr_proj___override(x_91, x_92, x_94);
return x_98;
}
else
{
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
return x_2;
}
}
default: 
{
lean_dec(x_1);
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
