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
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(uint8_t, uint8_t);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
size_t lean_usize_mod(size_t, size_t);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Lean_Level_replace(x_1, x_5);
x_8 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Level_replace(x_1, x_9);
x_12 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_20);
x_21 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_20);
x_22 = l_ptrEqList___rarg(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_const___override(x_19, x_21);
x_24 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_23, x_4);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_19);
lean_inc(x_3);
x_25 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_4);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_1);
x_28 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_26, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_27);
x_31 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_27, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ptr_addr(x_26);
lean_dec(x_26);
x_35 = lean_ptr_addr(x_29);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
x_37 = l_Lean_Expr_app___override(x_29, x_32);
x_38 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_37, x_33);
return x_38;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_40 = lean_ptr_addr(x_32);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Expr_app___override(x_29, x_32);
x_43 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_42, x_33);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_29);
lean_inc(x_3);
x_44 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_33);
return x_44;
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_46);
lean_inc(x_1);
x_49 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_46, x_4);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_47);
x_52 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_47, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_55 = l_Lean_Expr_lam___override(x_45, x_46, x_47, x_48);
x_56 = lean_ptr_addr(x_46);
lean_dec(x_46);
x_57 = lean_ptr_addr(x_50);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_55);
lean_dec(x_47);
x_59 = l_Lean_Expr_lam___override(x_45, x_50, x_53, x_48);
x_60 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_59, x_54);
return x_60;
}
else
{
size_t x_61; size_t x_62; uint8_t x_63; 
x_61 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_62 = lean_ptr_addr(x_53);
x_63 = lean_usize_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
x_64 = l_Lean_Expr_lam___override(x_45, x_50, x_53, x_48);
x_65 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_64, x_54);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_48, x_48);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
x_67 = l_Lean_Expr_lam___override(x_45, x_50, x_53, x_48);
x_68 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_67, x_54);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_45);
x_69 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_55, x_54);
return x_69;
}
}
}
}
case 7:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 2);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_71);
lean_inc(x_1);
x_74 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_71, x_4);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_72);
x_77 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
x_80 = l_Lean_Expr_forallE___override(x_70, x_71, x_72, x_73);
x_81 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_82 = lean_ptr_addr(x_75);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_72);
x_84 = l_Lean_Expr_forallE___override(x_70, x_75, x_78, x_73);
x_85 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_84, x_79);
return x_85;
}
else
{
size_t x_86; size_t x_87; uint8_t x_88; 
x_86 = lean_ptr_addr(x_72);
lean_dec(x_72);
x_87 = lean_ptr_addr(x_78);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
x_89 = l_Lean_Expr_forallE___override(x_70, x_75, x_78, x_73);
x_90 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_89, x_79);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_73, x_73);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_80);
x_92 = l_Lean_Expr_forallE___override(x_70, x_75, x_78, x_73);
x_93 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_92, x_79);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_70);
x_94 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_80, x_79);
return x_94;
}
}
}
}
case 8:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; size_t x_110; uint8_t x_111; 
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_96);
lean_inc(x_1);
x_100 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_96, x_4);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_97);
lean_inc(x_1);
x_103 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_98);
x_106 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_98, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_110 = lean_ptr_addr(x_101);
x_111 = lean_usize_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_98);
lean_dec(x_97);
x_112 = l_Lean_Expr_letE___override(x_95, x_101, x_104, x_107, x_99);
x_113 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_112, x_108);
return x_113;
}
else
{
size_t x_114; size_t x_115; uint8_t x_116; 
x_114 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_115 = lean_ptr_addr(x_104);
x_116 = lean_usize_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_98);
x_117 = l_Lean_Expr_letE___override(x_95, x_101, x_104, x_107, x_99);
x_118 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_117, x_108);
return x_118;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_120 = lean_ptr_addr(x_107);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_letE___override(x_95, x_101, x_104, x_107, x_99);
x_123 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_122, x_108);
return x_123;
}
else
{
lean_object* x_124; 
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_95);
lean_inc(x_3);
x_124 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_108);
return x_124;
}
}
}
}
case 10:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; size_t x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_3, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 1);
lean_inc(x_126);
lean_inc(x_126);
x_127 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_126, x_4);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ptr_addr(x_126);
lean_dec(x_126);
x_131 = lean_ptr_addr(x_128);
x_132 = lean_usize_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = l_Lean_Expr_mdata___override(x_125, x_128);
x_134 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_133, x_129);
return x_134;
}
else
{
lean_object* x_135; 
lean_dec(x_128);
lean_dec(x_125);
lean_inc(x_3);
x_135 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_129);
return x_135;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; uint8_t x_144; 
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
lean_inc(x_138);
x_139 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_138, x_4);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_143 = lean_ptr_addr(x_140);
x_144 = lean_usize_dec_eq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Lean_Expr_proj___override(x_136, x_137, x_140);
x_146 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_145, x_141);
return x_146;
}
else
{
lean_object* x_147; 
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_136);
lean_inc(x_3);
x_147 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_141);
return x_147;
}
}
default: 
{
lean_object* x_148; 
lean_dec(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
lean_dec(x_1);
x_149 = lean_ctor_get(x_4, 1);
lean_inc(x_149);
x_150 = lean_array_uget(x_149, x_6);
lean_dec(x_149);
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
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
