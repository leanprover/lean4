// Lean compiler output
// Module: Lean.Util.ReplaceExpr
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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Expr_ReplaceImpl_initCache___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__4;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_initCache;
static size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? x_5 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
lean_dec(x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_5;
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_12, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_13, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_14);
x_23 = lean_expr_update_app(x_22, x_16, x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_array_uset(x_25, x_6, x_3);
lean_inc(x_23);
x_28 = lean_array_uset(x_26, x_6, x_23);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_27);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_array_uset(x_29, x_6, x_3);
lean_inc(x_23);
x_32 = lean_array_uset(x_30, x_6, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_13);
lean_ctor_set_uint64(x_36, sizeof(void*)*2, x_14);
x_37 = lean_expr_update_app(x_36, x_16, x_34);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_40 = x_35;
} else {
 lean_dec_ref(x_35);
 x_40 = lean_box(0);
}
x_41 = lean_array_uset(x_38, x_6, x_3);
lean_inc(x_37);
x_42 = lean_array_uset(x_39, x_6, x_37);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_46);
lean_inc(x_1);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_46, x_4);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_47);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_47, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_48);
x_57 = (uint8_t)((x_48 << 24) >> 61);
x_58 = lean_expr_update_lambda(x_56, x_57, x_50, x_54);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
x_62 = lean_array_uset(x_60, x_6, x_3);
lean_inc(x_58);
x_63 = lean_array_uset(x_61, x_6, x_58);
lean_ctor_set(x_55, 1, x_63);
lean_ctor_set(x_55, 0, x_62);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_array_uset(x_64, x_6, x_3);
lean_inc(x_58);
x_67 = lean_array_uset(x_65, x_6, x_58);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_52, 1, x_68);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_52, 0);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_52);
x_71 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_71, 0, x_45);
lean_ctor_set(x_71, 1, x_46);
lean_ctor_set(x_71, 2, x_47);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_48);
x_72 = (uint8_t)((x_48 << 24) >> 61);
x_73 = lean_expr_update_lambda(x_71, x_72, x_50, x_69);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
x_77 = lean_array_uset(x_74, x_6, x_3);
lean_inc(x_73);
x_78 = lean_array_uset(x_75, x_6, x_73);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
case 7:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_81 = lean_ctor_get(x_3, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_82);
lean_inc(x_1);
x_85 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_82, x_4);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_83);
x_88 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_83, x_87);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_82);
lean_ctor_set(x_92, 2, x_83);
lean_ctor_set_uint64(x_92, sizeof(void*)*3, x_84);
x_93 = (uint8_t)((x_84 << 24) >> 61);
x_94 = lean_expr_update_forall(x_92, x_93, x_86, x_90);
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
x_97 = lean_ctor_get(x_91, 1);
x_98 = lean_array_uset(x_96, x_6, x_3);
lean_inc(x_94);
x_99 = lean_array_uset(x_97, x_6, x_94);
lean_ctor_set(x_91, 1, x_99);
lean_ctor_set(x_91, 0, x_98);
lean_ctor_set(x_88, 0, x_94);
return x_88;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_array_uset(x_100, x_6, x_3);
lean_inc(x_94);
x_103 = lean_array_uset(x_101, x_6, x_94);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_88, 1, x_104);
lean_ctor_set(x_88, 0, x_94);
return x_88;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_88, 0);
x_106 = lean_ctor_get(x_88, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_88);
x_107 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_107, 0, x_81);
lean_ctor_set(x_107, 1, x_82);
lean_ctor_set(x_107, 2, x_83);
lean_ctor_set_uint64(x_107, sizeof(void*)*3, x_84);
x_108 = (uint8_t)((x_84 << 24) >> 61);
x_109 = lean_expr_update_forall(x_107, x_108, x_86, x_105);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
x_113 = lean_array_uset(x_110, x_6, x_3);
lean_inc(x_109);
x_114 = lean_array_uset(x_111, x_6, x_109);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
case 8:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_117 = lean_ctor_get(x_3, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_3, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_3, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_3, 3);
lean_inc(x_120);
x_121 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_118);
lean_inc(x_1);
x_122 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_118, x_4);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_119);
lean_inc(x_1);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_119, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_120);
x_128 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_120, x_127);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_132, 0, x_117);
lean_ctor_set(x_132, 1, x_118);
lean_ctor_set(x_132, 2, x_119);
lean_ctor_set(x_132, 3, x_120);
lean_ctor_set_uint64(x_132, sizeof(void*)*4, x_121);
x_133 = lean_expr_update_let(x_132, x_123, x_126, x_130);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_131, 0);
x_136 = lean_ctor_get(x_131, 1);
x_137 = lean_array_uset(x_135, x_6, x_3);
lean_inc(x_133);
x_138 = lean_array_uset(x_136, x_6, x_133);
lean_ctor_set(x_131, 1, x_138);
lean_ctor_set(x_131, 0, x_137);
lean_ctor_set(x_128, 0, x_133);
return x_128;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_131, 0);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_131);
x_141 = lean_array_uset(x_139, x_6, x_3);
lean_inc(x_133);
x_142 = lean_array_uset(x_140, x_6, x_133);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_128, 1, x_143);
lean_ctor_set(x_128, 0, x_133);
return x_128;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_128);
x_146 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_146, 0, x_117);
lean_ctor_set(x_146, 1, x_118);
lean_ctor_set(x_146, 2, x_119);
lean_ctor_set(x_146, 3, x_120);
lean_ctor_set_uint64(x_146, sizeof(void*)*4, x_121);
x_147 = lean_expr_update_let(x_146, x_123, x_126, x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
x_151 = lean_array_uset(x_148, x_6, x_3);
lean_inc(x_147);
x_152 = lean_array_uset(x_149, x_6, x_147);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
case 10:
{
lean_object* x_155; lean_object* x_156; uint64_t x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_3, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
x_157 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_156);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_156, x_4);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ctor_get(x_158, 1);
x_162 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_162, 0, x_155);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set_uint64(x_162, sizeof(void*)*2, x_157);
x_163 = lean_expr_update_mdata(x_162, x_160);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_161, 0);
x_166 = lean_ctor_get(x_161, 1);
x_167 = lean_array_uset(x_165, x_6, x_3);
lean_inc(x_163);
x_168 = lean_array_uset(x_166, x_6, x_163);
lean_ctor_set(x_161, 1, x_168);
lean_ctor_set(x_161, 0, x_167);
lean_ctor_set(x_158, 0, x_163);
return x_158;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_161, 0);
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_161);
x_171 = lean_array_uset(x_169, x_6, x_3);
lean_inc(x_163);
x_172 = lean_array_uset(x_170, x_6, x_163);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_158, 1, x_173);
lean_ctor_set(x_158, 0, x_163);
return x_158;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_174 = lean_ctor_get(x_158, 0);
x_175 = lean_ctor_get(x_158, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_158);
x_176 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_176, 0, x_155);
lean_ctor_set(x_176, 1, x_156);
lean_ctor_set_uint64(x_176, sizeof(void*)*2, x_157);
x_177 = lean_expr_update_mdata(x_176, x_174);
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_array_uset(x_178, x_6, x_3);
lean_inc(x_177);
x_182 = lean_array_uset(x_179, x_6, x_177);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
case 11:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint64_t x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_3, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_3, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_3, 2);
lean_inc(x_187);
x_188 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_187);
x_189 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_187, x_4);
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_ctor_get(x_189, 1);
x_193 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_193, 0, x_185);
lean_ctor_set(x_193, 1, x_186);
lean_ctor_set(x_193, 2, x_187);
lean_ctor_set_uint64(x_193, sizeof(void*)*3, x_188);
x_194 = lean_expr_update_proj(x_193, x_191);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_192, 0);
x_197 = lean_ctor_get(x_192, 1);
x_198 = lean_array_uset(x_196, x_6, x_3);
lean_inc(x_194);
x_199 = lean_array_uset(x_197, x_6, x_194);
lean_ctor_set(x_192, 1, x_199);
lean_ctor_set(x_192, 0, x_198);
lean_ctor_set(x_189, 0, x_194);
return x_189;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_192, 0);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_array_uset(x_200, x_6, x_3);
lean_inc(x_194);
x_203 = lean_array_uset(x_201, x_6, x_194);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_189, 1, x_204);
lean_ctor_set(x_189, 0, x_194);
return x_189;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_205 = lean_ctor_get(x_189, 0);
x_206 = lean_ctor_get(x_189, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_189);
x_207 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_207, 0, x_185);
lean_ctor_set(x_207, 1, x_186);
lean_ctor_set(x_207, 2, x_187);
lean_ctor_set_uint64(x_207, sizeof(void*)*3, x_188);
x_208 = lean_expr_update_proj(x_207, x_205);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_array_uset(x_209, x_6, x_3);
lean_inc(x_208);
x_213 = lean_array_uset(x_210, x_6, x_208);
if (lean_is_scalar(x_211)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_211;
}
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
default: 
{
lean_object* x_216; 
lean_dec(x_1);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_3);
lean_ctor_set(x_216, 1, x_4);
return x_216;
}
}
}
else
{
lean_object* x_217; uint8_t x_218; 
lean_dec(x_1);
x_217 = lean_ctor_get(x_11, 0);
lean_inc(x_217);
lean_dec(x_11);
x_218 = !lean_is_exclusive(x_4);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_4, 0);
x_220 = lean_ctor_get(x_4, 1);
x_221 = lean_array_uset(x_219, x_6, x_3);
lean_inc(x_217);
x_222 = lean_array_uset(x_220, x_6, x_217);
lean_ctor_set(x_4, 1, x_222);
lean_ctor_set(x_4, 0, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_4);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_4, 0);
x_225 = lean_ctor_get(x_4, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_4);
x_226 = lean_array_uset(x_224, x_6, x_3);
lean_inc(x_217);
x_227 = lean_array_uset(x_225, x_6, x_217);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_217);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_3);
lean_dec(x_1);
x_230 = lean_ctor_get(x_4, 1);
lean_inc(x_230);
x_231 = lean_array_uget(x_230, x_6);
lean_dec(x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_4);
return x_232;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Expr_replace(x_1, x_5);
lean_inc(x_6);
x_8 = l_Lean_Expr_replace(x_1, x_6);
x_9 = lean_expr_update_app(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_Expr_replace(x_1, x_10);
lean_inc(x_11);
x_14 = l_Lean_Expr_replace(x_1, x_11);
x_15 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint64(x_15, sizeof(void*)*2, x_12);
x_16 = lean_expr_update_app(x_15, x_13, x_14);
return x_16;
}
}
case 6:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_1);
x_21 = l_Lean_Expr_replace(x_1, x_18);
lean_inc(x_19);
x_22 = l_Lean_Expr_replace(x_1, x_19);
x_23 = (uint8_t)((x_20 << 24) >> 61);
x_24 = lean_expr_update_lambda(x_2, x_23, x_21, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_26);
lean_inc(x_1);
x_29 = l_Lean_Expr_replace(x_1, x_26);
lean_inc(x_27);
x_30 = l_Lean_Expr_replace(x_1, x_27);
x_31 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_28);
x_32 = (uint8_t)((x_28 << 24) >> 61);
x_33 = lean_expr_update_lambda(x_31, x_32, x_29, x_30);
return x_33;
}
}
case 7:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_35);
lean_inc(x_1);
x_38 = l_Lean_Expr_replace(x_1, x_35);
lean_inc(x_36);
x_39 = l_Lean_Expr_replace(x_1, x_36);
x_40 = (uint8_t)((x_37 << 24) >> 61);
x_41 = lean_expr_update_forall(x_2, x_40, x_38, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_43);
lean_inc(x_1);
x_46 = l_Lean_Expr_replace(x_1, x_43);
lean_inc(x_44);
x_47 = l_Lean_Expr_replace(x_1, x_44);
x_48 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set_uint64(x_48, sizeof(void*)*3, x_45);
x_49 = (uint8_t)((x_45 << 24) >> 61);
x_50 = lean_expr_update_forall(x_48, x_49, x_46, x_47);
return x_50;
}
}
case 8:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Expr_replace(x_1, x_52);
lean_inc(x_53);
lean_inc(x_1);
x_56 = l_Lean_Expr_replace(x_1, x_53);
lean_inc(x_54);
x_57 = l_Lean_Expr_replace(x_1, x_54);
x_58 = lean_expr_update_let(x_2, x_55, x_56, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_60);
lean_inc(x_1);
x_64 = l_Lean_Expr_replace(x_1, x_60);
lean_inc(x_61);
lean_inc(x_1);
x_65 = l_Lean_Expr_replace(x_1, x_61);
lean_inc(x_62);
x_66 = l_Lean_Expr_replace(x_1, x_62);
x_67 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set_uint64(x_67, sizeof(void*)*4, x_63);
x_68 = lean_expr_update_let(x_67, x_64, x_65, x_66);
return x_68;
}
}
case 10:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = l_Lean_Expr_replace(x_1, x_70);
x_72 = lean_expr_update_mdata(x_2, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
lean_inc(x_74);
x_76 = l_Lean_Expr_replace(x_1, x_74);
x_77 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set_uint64(x_77, sizeof(void*)*2, x_75);
x_78 = lean_expr_update_mdata(x_77, x_76);
return x_78;
}
}
case 11:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_2);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
x_81 = l_Lean_Expr_replace(x_1, x_80);
x_82 = lean_expr_update_proj(x_2, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
x_86 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_2);
lean_inc(x_85);
x_87 = l_Lean_Expr_replace(x_1, x_85);
x_88 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set_uint64(x_88, sizeof(void*)*3, x_86);
x_89 = lean_expr_update_proj(x_88, x_87);
return x_89;
}
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
lean_object* x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
lean_dec(x_3);
return x_90;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__4);
l_Lean_Expr_ReplaceImpl_initCache___closed__5 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__5();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__5);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
