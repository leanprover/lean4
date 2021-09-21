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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static uint64_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_replaceLevel___spec__1(lean_object*, lean_object*, lean_object*);
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
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = l_Lean_Level_replace(x_1, x_8);
x_11 = lean_level_mk_max_simp(x_9, x_10);
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
x_16 = lean_level_mk_imax_simp(x_14, x_15);
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
x_1 = 8192;
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = x_2 == 0 ? x_5 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_5;
if (x_10 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_inc(x_11);
x_13 = l_Lean_Level_replace(x_1, x_11);
x_14 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_12);
x_15 = lean_expr_update_sort(x_14, x_13);
x_16 = lean_array_uset(x_7, x_6, x_3);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_15);
x_18 = lean_array_uset(x_17, x_6, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_24 = lean_box(0);
lean_inc(x_22);
x_25 = l_List_mapTRAux___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_22, x_24);
x_26 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_23);
x_27 = lean_expr_update_const(x_26, x_25);
x_28 = lean_array_uset(x_7, x_6, x_3);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
lean_inc(x_27);
x_30 = lean_array_uset(x_29, x_6, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_7);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_33);
lean_inc(x_1);
x_36 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_33, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_34);
x_39 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_34, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_inc(x_3);
x_44 = lean_array_uset(x_43, x_6, x_3);
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_3, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_expr_update_app(x_3, x_37, x_41);
lean_inc(x_49);
x_50 = lean_array_uset(x_48, x_6, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_39, 1, x_51);
lean_ctor_set(x_39, 0, x_49);
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_53, 0, x_33);
lean_ctor_set(x_53, 1, x_34);
lean_ctor_set_uint64(x_53, sizeof(void*)*2, x_35);
x_54 = lean_expr_update_app(x_53, x_37, x_41);
lean_inc(x_54);
x_55 = lean_array_uset(x_52, x_6, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_39, 1, x_56);
lean_ctor_set(x_39, 0, x_54);
return x_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_inc(x_3);
x_60 = lean_array_uset(x_59, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_61 = x_3;
} else {
 lean_dec_ref(x_3);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(5, 2, 8);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_34);
lean_ctor_set_uint64(x_63, sizeof(void*)*2, x_35);
x_64 = lean_expr_update_app(x_63, x_37, x_57);
lean_inc(x_64);
x_65 = lean_array_uset(x_62, x_6, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
case 6:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_7);
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_69);
lean_inc(x_1);
x_72 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_69, x_4);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_70);
x_75 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_70, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_inc(x_3);
x_80 = lean_array_uset(x_79, x_6, x_3);
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_3, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = (uint8_t)((x_71 << 24) >> 61);
x_87 = lean_expr_update_lambda(x_3, x_86, x_73, x_77);
lean_inc(x_87);
x_88 = lean_array_uset(x_85, x_6, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_75, 1, x_89);
lean_ctor_set(x_75, 0, x_87);
return x_75;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_3);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_70);
lean_ctor_set_uint64(x_91, sizeof(void*)*3, x_71);
x_92 = (uint8_t)((x_71 << 24) >> 61);
x_93 = lean_expr_update_lambda(x_91, x_92, x_73, x_77);
lean_inc(x_93);
x_94 = lean_array_uset(x_90, x_6, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_80);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_75, 1, x_95);
lean_ctor_set(x_75, 0, x_93);
return x_75;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_75, 0);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_75);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_100 = x_3;
} else {
 lean_dec_ref(x_3);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(6, 3, 8);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_68);
lean_ctor_set(x_102, 1, x_69);
lean_ctor_set(x_102, 2, x_70);
lean_ctor_set_uint64(x_102, sizeof(void*)*3, x_71);
x_103 = (uint8_t)((x_71 << 24) >> 61);
x_104 = lean_expr_update_lambda(x_102, x_103, x_73, x_96);
lean_inc(x_104);
x_105 = lean_array_uset(x_101, x_6, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
case 7:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_7);
x_108 = lean_ctor_get(x_3, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_3, 2);
lean_inc(x_110);
x_111 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_109, x_4);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_110);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_110, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_6, x_3);
x_121 = !lean_is_exclusive(x_3);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_3, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_3, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_dec(x_118);
x_126 = (uint8_t)((x_111 << 24) >> 61);
x_127 = lean_expr_update_forall(x_3, x_126, x_113, x_117);
lean_inc(x_127);
x_128 = lean_array_uset(x_125, x_6, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_115, 1, x_129);
lean_ctor_set(x_115, 0, x_127);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_3);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_dec(x_118);
x_131 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_131, 0, x_108);
lean_ctor_set(x_131, 1, x_109);
lean_ctor_set(x_131, 2, x_110);
lean_ctor_set_uint64(x_131, sizeof(void*)*3, x_111);
x_132 = (uint8_t)((x_111 << 24) >> 61);
x_133 = lean_expr_update_forall(x_131, x_132, x_113, x_117);
lean_inc(x_133);
x_134 = lean_array_uset(x_130, x_6, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_115, 1, x_135);
lean_ctor_set(x_115, 0, x_133);
return x_115;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_136 = lean_ctor_get(x_115, 0);
x_137 = lean_ctor_get(x_115, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_115);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_inc(x_3);
x_139 = lean_array_uset(x_138, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_140 = x_3;
} else {
 lean_dec_ref(x_3);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(7, 3, 8);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_108);
lean_ctor_set(x_142, 1, x_109);
lean_ctor_set(x_142, 2, x_110);
lean_ctor_set_uint64(x_142, sizeof(void*)*3, x_111);
x_143 = (uint8_t)((x_111 << 24) >> 61);
x_144 = lean_expr_update_forall(x_142, x_143, x_113, x_136);
lean_inc(x_144);
x_145 = lean_array_uset(x_141, x_6, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
case 8:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint64_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_7);
x_148 = lean_ctor_get(x_3, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_3, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_3, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_3, 3);
lean_inc(x_151);
x_152 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_149);
lean_inc(x_1);
x_153 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_149, x_4);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_150);
lean_inc(x_1);
x_156 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_150, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_151);
x_159 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_151, x_158);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_ctor_get(x_159, 1);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_inc(x_3);
x_164 = lean_array_uset(x_163, x_6, x_3);
x_165 = !lean_is_exclusive(x_3);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_3, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_3, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_3, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_3, 0);
lean_dec(x_169);
x_170 = lean_ctor_get(x_162, 1);
lean_inc(x_170);
lean_dec(x_162);
x_171 = lean_expr_update_let(x_3, x_154, x_157, x_161);
lean_inc(x_171);
x_172 = lean_array_uset(x_170, x_6, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_164);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_159, 1, x_173);
lean_ctor_set(x_159, 0, x_171);
return x_159;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_3);
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
lean_dec(x_162);
x_175 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_175, 0, x_148);
lean_ctor_set(x_175, 1, x_149);
lean_ctor_set(x_175, 2, x_150);
lean_ctor_set(x_175, 3, x_151);
lean_ctor_set_uint64(x_175, sizeof(void*)*4, x_152);
x_176 = lean_expr_update_let(x_175, x_154, x_157, x_161);
lean_inc(x_176);
x_177 = lean_array_uset(x_174, x_6, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_164);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_159, 1, x_178);
lean_ctor_set(x_159, 0, x_176);
return x_159;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_179 = lean_ctor_get(x_159, 0);
x_180 = lean_ctor_get(x_159, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_159);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_inc(x_3);
x_182 = lean_array_uset(x_181, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_183 = x_3;
} else {
 lean_dec_ref(x_3);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(8, 4, 8);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_148);
lean_ctor_set(x_185, 1, x_149);
lean_ctor_set(x_185, 2, x_150);
lean_ctor_set(x_185, 3, x_151);
lean_ctor_set_uint64(x_185, sizeof(void*)*4, x_152);
x_186 = lean_expr_update_let(x_185, x_154, x_157, x_179);
lean_inc(x_186);
x_187 = lean_array_uset(x_184, x_6, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_182);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
case 10:
{
lean_object* x_190; lean_object* x_191; uint64_t x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_7);
x_190 = lean_ctor_get(x_3, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_3, 1);
lean_inc(x_191);
x_192 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_191);
x_193 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_191, x_4);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_inc(x_3);
x_198 = lean_array_uset(x_197, x_6, x_3);
x_199 = !lean_is_exclusive(x_3);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_3, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_3, 0);
lean_dec(x_201);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
x_203 = lean_expr_update_mdata(x_3, x_195);
lean_inc(x_203);
x_204 = lean_array_uset(x_202, x_6, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_193, 1, x_205);
lean_ctor_set(x_193, 0, x_203);
return x_193;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_3);
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
lean_dec(x_196);
x_207 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_207, 0, x_190);
lean_ctor_set(x_207, 1, x_191);
lean_ctor_set_uint64(x_207, sizeof(void*)*2, x_192);
x_208 = lean_expr_update_mdata(x_207, x_195);
lean_inc(x_208);
x_209 = lean_array_uset(x_206, x_6, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_198);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_193, 1, x_210);
lean_ctor_set(x_193, 0, x_208);
return x_193;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_211 = lean_ctor_get(x_193, 0);
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_193);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_inc(x_3);
x_214 = lean_array_uset(x_213, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_215 = x_3;
} else {
 lean_dec_ref(x_3);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(10, 2, 8);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_190);
lean_ctor_set(x_217, 1, x_191);
lean_ctor_set_uint64(x_217, sizeof(void*)*2, x_192);
x_218 = lean_expr_update_mdata(x_217, x_211);
lean_inc(x_218);
x_219 = lean_array_uset(x_216, x_6, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
case 11:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint64_t x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_7);
x_222 = lean_ctor_get(x_3, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_3, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_3, 2);
lean_inc(x_224);
x_225 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_224);
x_226 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_224, x_4);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_ctor_get(x_226, 1);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_inc(x_3);
x_231 = lean_array_uset(x_230, x_6, x_3);
x_232 = !lean_is_exclusive(x_3);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_3, 2);
lean_dec(x_233);
x_234 = lean_ctor_get(x_3, 1);
lean_dec(x_234);
x_235 = lean_ctor_get(x_3, 0);
lean_dec(x_235);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_dec(x_229);
x_237 = lean_expr_update_proj(x_3, x_228);
lean_inc(x_237);
x_238 = lean_array_uset(x_236, x_6, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_226, 1, x_239);
lean_ctor_set(x_226, 0, x_237);
return x_226;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_3);
x_240 = lean_ctor_get(x_229, 1);
lean_inc(x_240);
lean_dec(x_229);
x_241 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_241, 0, x_222);
lean_ctor_set(x_241, 1, x_223);
lean_ctor_set(x_241, 2, x_224);
lean_ctor_set_uint64(x_241, sizeof(void*)*3, x_225);
x_242 = lean_expr_update_proj(x_241, x_228);
lean_inc(x_242);
x_243 = lean_array_uset(x_240, x_6, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_231);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_226, 1, x_244);
lean_ctor_set(x_226, 0, x_242);
return x_226;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_245 = lean_ctor_get(x_226, 0);
x_246 = lean_ctor_get(x_226, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_226);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_inc(x_3);
x_248 = lean_array_uset(x_247, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_249 = x_3;
} else {
 lean_dec_ref(x_3);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(11, 3, 8);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_222);
lean_ctor_set(x_251, 1, x_223);
lean_ctor_set(x_251, 2, x_224);
lean_ctor_set_uint64(x_251, sizeof(void*)*3, x_225);
x_252 = lean_expr_update_proj(x_251, x_245);
lean_inc(x_252);
x_253 = lean_array_uset(x_250, x_6, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_248);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
default: 
{
lean_object* x_256; 
lean_dec(x_7);
lean_dec(x_1);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_3);
lean_ctor_set(x_256, 1, x_4);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_257 = lean_ctor_get(x_4, 1);
lean_inc(x_257);
x_258 = lean_array_uget(x_257, x_6);
lean_dec(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_4);
return x_259;
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
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
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
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_replaceLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Level_replace(x_1, x_4);
x_6 = lean_expr_update_sort(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_7);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_8);
x_11 = lean_expr_update_sort(x_10, x_9);
return x_11;
}
}
case 4:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTRAux___at_Lean_Expr_replaceLevel___spec__1(x_1, x_13, x_14);
x_16 = lean_expr_update_const(x_2, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_20 = lean_box(0);
lean_inc(x_18);
x_21 = l_List_mapTRAux___at_Lean_Expr_replaceLevel___spec__1(x_1, x_18, x_20);
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_19);
x_23 = lean_expr_update_const(x_22, x_21);
return x_23;
}
}
case 5:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_1);
x_27 = l_Lean_Expr_replaceLevel(x_1, x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_replaceLevel(x_1, x_26);
x_29 = lean_expr_update_app(x_2, x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_30);
lean_inc(x_1);
x_33 = l_Lean_Expr_replaceLevel(x_1, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_replaceLevel(x_1, x_31);
x_35 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint64(x_35, sizeof(void*)*2, x_32);
x_36 = lean_expr_update_app(x_35, x_33, x_34);
return x_36;
}
}
case 6:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 2);
x_40 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_38);
lean_inc(x_1);
x_41 = l_Lean_Expr_replaceLevel(x_1, x_38);
lean_inc(x_39);
x_42 = l_Lean_Expr_replaceLevel(x_1, x_39);
x_43 = (uint8_t)((x_40 << 24) >> 61);
x_44 = lean_expr_update_lambda(x_2, x_43, x_41, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
lean_inc(x_46);
lean_inc(x_1);
x_49 = l_Lean_Expr_replaceLevel(x_1, x_46);
lean_inc(x_47);
x_50 = l_Lean_Expr_replaceLevel(x_1, x_47);
x_51 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set_uint64(x_51, sizeof(void*)*3, x_48);
x_52 = (uint8_t)((x_48 << 24) >> 61);
x_53 = lean_expr_update_lambda(x_51, x_52, x_49, x_50);
return x_53;
}
}
case 7:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_55);
lean_inc(x_1);
x_58 = l_Lean_Expr_replaceLevel(x_1, x_55);
lean_inc(x_56);
x_59 = l_Lean_Expr_replaceLevel(x_1, x_56);
x_60 = (uint8_t)((x_57 << 24) >> 61);
x_61 = lean_expr_update_forall(x_2, x_60, x_58, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
lean_inc(x_63);
lean_inc(x_1);
x_66 = l_Lean_Expr_replaceLevel(x_1, x_63);
lean_inc(x_64);
x_67 = l_Lean_Expr_replaceLevel(x_1, x_64);
x_68 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_65);
x_69 = (uint8_t)((x_65 << 24) >> 61);
x_70 = lean_expr_update_forall(x_68, x_69, x_66, x_67);
return x_70;
}
}
case 8:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_ctor_get(x_2, 2);
x_74 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
lean_inc(x_1);
x_75 = l_Lean_Expr_replaceLevel(x_1, x_72);
lean_inc(x_73);
lean_inc(x_1);
x_76 = l_Lean_Expr_replaceLevel(x_1, x_73);
lean_inc(x_74);
x_77 = l_Lean_Expr_replaceLevel(x_1, x_74);
x_78 = lean_expr_update_let(x_2, x_75, x_76, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
x_81 = lean_ctor_get(x_2, 2);
x_82 = lean_ctor_get(x_2, 3);
x_83 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_2);
lean_inc(x_80);
lean_inc(x_1);
x_84 = l_Lean_Expr_replaceLevel(x_1, x_80);
lean_inc(x_81);
lean_inc(x_1);
x_85 = l_Lean_Expr_replaceLevel(x_1, x_81);
lean_inc(x_82);
x_86 = l_Lean_Expr_replaceLevel(x_1, x_82);
x_87 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_80);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_82);
lean_ctor_set_uint64(x_87, sizeof(void*)*4, x_83);
x_88 = lean_expr_update_let(x_87, x_84, x_85, x_86);
return x_88;
}
}
case 10:
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_2);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
x_91 = l_Lean_Expr_replaceLevel(x_1, x_90);
x_92 = lean_expr_update_mdata(x_2, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_2, 0);
x_94 = lean_ctor_get(x_2, 1);
x_95 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_2);
lean_inc(x_94);
x_96 = l_Lean_Expr_replaceLevel(x_1, x_94);
x_97 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set_uint64(x_97, sizeof(void*)*2, x_95);
x_98 = lean_expr_update_mdata(x_97, x_96);
return x_98;
}
}
case 11:
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_2);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
x_101 = l_Lean_Expr_replaceLevel(x_1, x_100);
x_102 = lean_expr_update_proj(x_2, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get(x_2, 1);
x_105 = lean_ctor_get(x_2, 2);
x_106 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_2);
lean_inc(x_105);
x_107 = l_Lean_Expr_replaceLevel(x_1, x_105);
x_108 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_106);
x_109 = lean_expr_update_proj(x_108, x_107);
return x_109;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2();
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
