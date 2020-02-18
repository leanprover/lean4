// Lean compiler output
// Module: Init.Lean.Util.ReplaceExpr
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__2;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(lean_object*, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_Lean_Expr_replace___main(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__3;
lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
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
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_12, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_13, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_3);
x_22 = lean_array_uset(x_21, x_6, x_3);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_expr_update_app(x_3, x_15, x_19);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_6, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_inc(x_3);
x_30 = lean_array_uset(x_29, x_6, x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_expr_update_app(x_3, x_15, x_27);
lean_inc(x_32);
x_33 = lean_array_uset(x_31, x_6, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_39 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_36, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_37, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_inc(x_3);
x_47 = lean_array_uset(x_46, x_6, x_3);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = (uint8_t)((x_38 << 24) >> 61);
x_50 = lean_expr_update_lambda(x_3, x_49, x_40, x_44);
lean_inc(x_50);
x_51 = lean_array_uset(x_48, x_6, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_42, 1, x_52);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_inc(x_3);
x_56 = lean_array_uset(x_55, x_6, x_3);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = (uint8_t)((x_38 << 24) >> 61);
x_59 = lean_expr_update_lambda(x_3, x_58, x_40, x_53);
lean_inc(x_59);
x_60 = lean_array_uset(x_57, x_6, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
case 7:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_66 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_63, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_64, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_inc(x_3);
x_74 = lean_array_uset(x_73, x_6, x_3);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = (uint8_t)((x_65 << 24) >> 61);
x_77 = lean_expr_update_forall(x_3, x_76, x_67, x_71);
lean_inc(x_77);
x_78 = lean_array_uset(x_75, x_6, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_69, 1, x_79);
lean_ctor_set(x_69, 0, x_77);
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_inc(x_3);
x_83 = lean_array_uset(x_82, x_6, x_3);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = (uint8_t)((x_65 << 24) >> 61);
x_86 = lean_expr_update_forall(x_3, x_85, x_67, x_80);
lean_inc(x_86);
x_87 = lean_array_uset(x_84, x_6, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
case 8:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 3);
lean_inc(x_92);
lean_inc(x_1);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_90, x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_1);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_91, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_92, x_98);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_inc(x_3);
x_104 = lean_array_uset(x_103, x_6, x_3);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_expr_update_let(x_3, x_94, x_97, x_101);
lean_inc(x_106);
x_107 = lean_array_uset(x_105, x_6, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_99, 1, x_108);
lean_ctor_set(x_99, 0, x_106);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_99, 0);
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_99);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_inc(x_3);
x_112 = lean_array_uset(x_111, x_6, x_3);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_expr_update_let(x_3, x_94, x_97, x_109);
lean_inc(x_114);
x_115 = lean_array_uset(x_113, x_6, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_3, 1);
lean_inc(x_118);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_118, x_4);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_inc(x_3);
x_124 = lean_array_uset(x_123, x_6, x_3);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_expr_update_mdata(x_3, x_121);
lean_inc(x_126);
x_127 = lean_array_uset(x_125, x_6, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_119, 1, x_128);
lean_ctor_set(x_119, 0, x_126);
return x_119;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_119, 0);
x_130 = lean_ctor_get(x_119, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_119);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_inc(x_3);
x_132 = lean_array_uset(x_131, x_6, x_3);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_expr_update_mdata(x_3, x_129);
lean_inc(x_134);
x_135 = lean_array_uset(x_133, x_6, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
case 11:
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_138, x_4);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_inc(x_3);
x_144 = lean_array_uset(x_143, x_6, x_3);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_expr_update_proj(x_3, x_141);
lean_inc(x_146);
x_147 = lean_array_uset(x_145, x_6, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_139, 1, x_148);
lean_ctor_set(x_139, 0, x_146);
return x_139;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_inc(x_3);
x_152 = lean_array_uset(x_151, x_6, x_3);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_expr_update_proj(x_3, x_149);
lean_inc(x_154);
x_155 = lean_array_uset(x_153, x_6, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
case 12:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_3);
lean_dec(x_1);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_159 = l_unreachable_x21___rarg(x_158);
x_160 = lean_apply_1(x_159, x_4);
return x_160;
}
default: 
{
lean_object* x_161; 
lean_dec(x_1);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_3);
lean_ctor_set(x_161, 1, x_4);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_1);
x_162 = lean_ctor_get(x_11, 0);
lean_inc(x_162);
lean_dec(x_11);
x_163 = lean_array_uset(x_7, x_6, x_3);
x_164 = lean_ctor_get(x_4, 1);
lean_inc(x_164);
lean_dec(x_4);
lean_inc(x_162);
x_165 = lean_array_uset(x_164, x_6, x_162);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_168 = lean_ctor_get(x_4, 1);
lean_inc(x_168);
x_169 = lean_array_uget(x_168, x_6);
lean_dec(x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_4);
return x_170;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_replace___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Expr_replace___main(x_1, x_4);
x_7 = l_Lean_Expr_replace___main(x_1, x_5);
x_8 = lean_expr_update_app(x_2, x_6, x_7);
return x_8;
}
case 6:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_1);
x_12 = l_Lean_Expr_replace___main(x_1, x_9);
x_13 = l_Lean_Expr_replace___main(x_1, x_10);
x_14 = (uint8_t)((x_11 << 24) >> 61);
x_15 = lean_expr_update_lambda(x_2, x_14, x_12, x_13);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_1);
x_19 = l_Lean_Expr_replace___main(x_1, x_16);
x_20 = l_Lean_Expr_replace___main(x_1, x_17);
x_21 = (uint8_t)((x_18 << 24) >> 61);
x_22 = lean_expr_update_forall(x_2, x_21, x_19, x_20);
return x_22;
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_1);
x_26 = l_Lean_Expr_replace___main(x_1, x_23);
lean_inc(x_1);
x_27 = l_Lean_Expr_replace___main(x_1, x_24);
x_28 = l_Lean_Expr_replace___main(x_1, x_25);
x_29 = lean_expr_update_let(x_2, x_26, x_27, x_28);
return x_29;
}
case 10:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_replace___main(x_1, x_30);
x_32 = lean_expr_update_mdata(x_2, x_31);
return x_32;
}
case 11:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = l_Lean_Expr_replace___main(x_1, x_33);
x_35 = lean_expr_update_proj(x_2, x_34);
return x_35;
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
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
return x_36;
}
}
}
lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_replace___main(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_ReplaceExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
