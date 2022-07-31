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
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__2;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__4;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(uint8_t, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
lean_object* x_11; 
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_12, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_13);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_21 = lean_ptr_addr(x_15);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_23 = l_Lean_Expr_app___override(x_15, x_18);
x_24 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_23, x_19);
return x_24;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_26 = lean_ptr_addr(x_18);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Expr_app___override(x_15, x_18);
x_29 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_28, x_19);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_15);
lean_inc(x_3);
x_30 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_3, x_19);
return x_30;
}
}
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; uint8_t x_44; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_32);
lean_inc(x_1);
x_35 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_32, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_33, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_41 = l_Lean_Expr_lam___override(x_31, x_32, x_33, x_34);
x_42 = lean_ptr_addr(x_32);
lean_dec(x_32);
x_43 = lean_ptr_addr(x_36);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_33);
x_45 = l_Lean_Expr_lam___override(x_31, x_36, x_39, x_34);
x_46 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_45, x_40);
return x_46;
}
else
{
size_t x_47; size_t x_48; uint8_t x_49; 
x_47 = lean_ptr_addr(x_33);
lean_dec(x_33);
x_48 = lean_ptr_addr(x_39);
x_49 = lean_usize_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_50 = l_Lean_Expr_lam___override(x_31, x_36, x_39, x_34);
x_51 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_50, x_40);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_34, x_34);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_41);
x_53 = l_Lean_Expr_lam___override(x_31, x_36, x_39, x_34);
x_54 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_53, x_40);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_31);
x_55 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_41, x_40);
return x_55;
}
}
}
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; uint8_t x_69; 
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_57);
lean_inc(x_1);
x_60 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_57, x_4);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_58);
x_63 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_58, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_66 = l_Lean_Expr_forallE___override(x_56, x_57, x_58, x_59);
x_67 = lean_ptr_addr(x_57);
lean_dec(x_57);
x_68 = lean_ptr_addr(x_61);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_58);
x_70 = l_Lean_Expr_forallE___override(x_56, x_61, x_64, x_59);
x_71 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_70, x_65);
return x_71;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_73 = lean_ptr_addr(x_64);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_66);
x_75 = l_Lean_Expr_forallE___override(x_56, x_61, x_64, x_59);
x_76 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_75, x_65);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_59, x_59);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_66);
x_78 = l_Lean_Expr_forallE___override(x_56, x_61, x_64, x_59);
x_79 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_78, x_65);
return x_79;
}
else
{
lean_object* x_80; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_56);
x_80 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_66, x_65);
return x_80;
}
}
}
}
case 8:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; uint8_t x_97; 
x_81 = lean_ctor_get(x_3, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 3);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_82);
lean_inc(x_1);
x_86 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_82, x_4);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_83);
lean_inc(x_1);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_83, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_84);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_84, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ptr_addr(x_82);
lean_dec(x_82);
x_96 = lean_ptr_addr(x_87);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_84);
lean_dec(x_83);
x_98 = l_Lean_Expr_letE___override(x_81, x_87, x_90, x_93, x_85);
x_99 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_98, x_94);
return x_99;
}
else
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_101 = lean_ptr_addr(x_90);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
x_103 = l_Lean_Expr_letE___override(x_81, x_87, x_90, x_93, x_85);
x_104 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_103, x_94);
return x_104;
}
else
{
size_t x_105; size_t x_106; uint8_t x_107; 
x_105 = lean_ptr_addr(x_84);
lean_dec(x_84);
x_106 = lean_ptr_addr(x_93);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Expr_letE___override(x_81, x_87, x_90, x_93, x_85);
x_109 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_108, x_94);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_81);
lean_inc(x_3);
x_110 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_3, x_94);
return x_110;
}
}
}
}
case 10:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; uint8_t x_118; 
x_111 = lean_ctor_get(x_3, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 1);
lean_inc(x_112);
lean_inc(x_112);
x_113 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_112, x_4);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ptr_addr(x_112);
lean_dec(x_112);
x_117 = lean_ptr_addr(x_114);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Expr_mdata___override(x_111, x_114);
x_120 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_119, x_115);
return x_120;
}
else
{
lean_object* x_121; 
lean_dec(x_114);
lean_dec(x_111);
lean_inc(x_3);
x_121 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_3, x_115);
return x_121;
}
}
case 11:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; size_t x_128; size_t x_129; uint8_t x_130; 
x_122 = lean_ctor_get(x_3, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 2);
lean_inc(x_124);
lean_inc(x_124);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_124, x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ptr_addr(x_124);
lean_dec(x_124);
x_129 = lean_ptr_addr(x_126);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = l_Lean_Expr_proj___override(x_122, x_123, x_126);
x_132 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_131, x_127);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_122);
lean_inc(x_3);
x_133 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_3, x_127);
return x_133;
}
}
default: 
{
lean_object* x_134; 
lean_dec(x_1);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_3);
lean_ctor_set(x_134, 1, x_4);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_135 = lean_ctor_get(x_11, 0);
lean_inc(x_135);
lean_dec(x_11);
x_136 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_135, x_4);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_3);
lean_dec(x_1);
x_137 = lean_ctor_get(x_4, 1);
lean_inc(x_137);
x_138 = lean_array_uget(x_137, x_6);
lean_dec(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_4);
return x_139;
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
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
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
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__4;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__4);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
