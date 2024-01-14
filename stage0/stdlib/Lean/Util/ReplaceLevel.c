// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: Init Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
size_t lean_usize_mod(size_t, size_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8191;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_uset(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_3);
x_8 = lean_array_uset(x_7, x_1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
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
lean_inc(x_1);
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
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = lean_usize_mod(x_5, x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
lean_dec(x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_9, x_5);
if (x_10 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_Level_replace(x_1, x_11);
x_13 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_sort___override(x_12);
x_17 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_16, x_4);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_12);
lean_inc(x_3);
x_18 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_4);
return x_18;
}
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_box(0);
lean_inc(x_20);
x_22 = l_List_mapTR_loop___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_20, x_21);
x_23 = l_ptrEqList___rarg(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_const___override(x_19, x_22);
x_25 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_24, x_4);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_inc(x_3);
x_26 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_4);
return x_26;
}
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_29 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_27, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_28);
x_32 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_28, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_36 = lean_ptr_addr(x_30);
x_37 = lean_usize_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_38 = l_Lean_Expr_app___override(x_30, x_33);
x_39 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_38, x_34);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_41 = lean_ptr_addr(x_33);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Expr_app___override(x_30, x_33);
x_44 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_43, x_34);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_30);
lean_inc(x_3);
x_45 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_34);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; uint8_t x_59; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_47, x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_48);
x_53 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_48, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_56 = l_Lean_Expr_lam___override(x_46, x_47, x_48, x_49);
x_57 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_58 = lean_ptr_addr(x_51);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_56);
lean_dec(x_48);
x_60 = l_Lean_Expr_lam___override(x_46, x_51, x_54, x_49);
x_61 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_60, x_55);
return x_61;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_63 = lean_ptr_addr(x_54);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
x_65 = l_Lean_Expr_lam___override(x_46, x_51, x_54, x_49);
x_66 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_65, x_55);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_49, x_49);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_56);
x_68 = l_Lean_Expr_lam___override(x_46, x_51, x_54, x_49);
x_69 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_68, x_55);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_46);
x_70 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_56, x_55);
return x_70;
}
}
}
}
case 7:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; uint8_t x_84; 
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 2);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_72);
lean_inc(x_1);
x_75 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_72, x_4);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_73);
x_78 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_73, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_81 = l_Lean_Expr_forallE___override(x_71, x_72, x_73, x_74);
x_82 = lean_ptr_addr(x_72);
lean_dec(x_72);
x_83 = lean_ptr_addr(x_76);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
lean_dec(x_73);
x_85 = l_Lean_Expr_forallE___override(x_71, x_76, x_79, x_74);
x_86 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_85, x_80);
return x_86;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_88 = lean_ptr_addr(x_79);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
x_90 = l_Lean_Expr_forallE___override(x_71, x_76, x_79, x_74);
x_91 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_90, x_80);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_74, x_74);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_81);
x_93 = l_Lean_Expr_forallE___override(x_71, x_76, x_79, x_74);
x_94 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_93, x_80);
return x_94;
}
else
{
lean_object* x_95; 
lean_dec(x_79);
lean_dec(x_76);
lean_dec(x_71);
x_95 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_81, x_80);
return x_95;
}
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; uint8_t x_112; 
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
x_110 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_111 = lean_ptr_addr(x_102);
x_112 = lean_usize_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_99);
lean_dec(x_98);
x_113 = l_Lean_Expr_letE___override(x_96, x_102, x_105, x_108, x_100);
x_114 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_113, x_109);
return x_114;
}
else
{
size_t x_115; size_t x_116; uint8_t x_117; 
x_115 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_116 = lean_ptr_addr(x_105);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_99);
x_118 = l_Lean_Expr_letE___override(x_96, x_102, x_105, x_108, x_100);
x_119 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_118, x_109);
return x_119;
}
else
{
size_t x_120; size_t x_121; uint8_t x_122; 
x_120 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_121 = lean_ptr_addr(x_108);
x_122 = lean_usize_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Expr_letE___override(x_96, x_102, x_105, x_108, x_100);
x_124 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_123, x_109);
return x_124;
}
else
{
lean_object* x_125; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_96);
lean_inc(x_3);
x_125 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_109);
return x_125;
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
x_135 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_134, x_130);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_126);
lean_inc(x_3);
x_136 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_130);
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
x_147 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_146, x_142);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_137);
lean_inc(x_3);
x_148 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_142);
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
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_ctor_get(x_4, 1);
lean_inc(x_150);
x_151 = lean_array_uget(x_150, x_6);
lean_dec(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_4);
return x_152;
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
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8191u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8191u);
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8191;
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
