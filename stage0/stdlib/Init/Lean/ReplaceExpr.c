// Lean compiler output
// Module: Init.Lean.ReplaceExpr
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_uset(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_array_uset(x_7, x_1, x_9);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_3);
x_12 = lean_array_uset(x_11, x_1, x_3);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
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
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_219 = lean_ctor_get(x_4, 1);
lean_inc(x_219);
x_220 = lean_array_uget(x_219, x_6);
lean_dec(x_219);
x_221 = lean_unbox(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_box(0);
x_7 = x_222;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; size_t x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_4, 0);
lean_inc(x_223);
x_224 = lean_array_uget(x_223, x_6);
lean_dec(x_223);
x_225 = lean_ptr_addr(x_224);
lean_dec(x_224);
x_226 = x_225 == x_5;
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_box(0);
x_7 = x_227;
goto block_218;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_3);
lean_dec(x_1);
x_228 = lean_ctor_get(x_4, 2);
lean_inc(x_228);
x_229 = lean_array_uget(x_228, x_6);
lean_dec(x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_4);
return x_230;
}
}
block_218:
{
lean_object* x_8; 
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_8) == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_9, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_10, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_3);
x_19 = lean_array_uset(x_18, x_6, x_3);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_array_uset(x_20, x_6, x_22);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_expr_update_app(x_3, x_12, x_16);
lean_inc(x_25);
x_26 = lean_array_uset(x_24, x_6, x_25);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_14, 1, x_27);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_inc(x_3);
x_31 = lean_array_uset(x_30, x_6, x_3);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_array_uset(x_32, x_6, x_34);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_expr_update_app(x_3, x_12, x_28);
lean_inc(x_37);
x_38 = lean_array_uset(x_36, x_6, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_44 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_41, x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_42, x_46);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_inc(x_3);
x_52 = lean_array_uset(x_51, x_6, x_3);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_array_uset(x_53, x_6, x_55);
x_57 = lean_ctor_get(x_50, 2);
lean_inc(x_57);
lean_dec(x_50);
x_58 = (uint8_t)((x_43 << 24) >> 61);
x_59 = lean_expr_update_lambda(x_3, x_58, x_45, x_49);
lean_inc(x_59);
x_60 = lean_array_uset(x_57, x_6, x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_47, 1, x_61);
lean_ctor_set(x_47, 0, x_59);
return x_47;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_47, 0);
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_47);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_inc(x_3);
x_65 = lean_array_uset(x_64, x_6, x_3);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_array_uset(x_66, x_6, x_68);
x_70 = lean_ctor_get(x_63, 2);
lean_inc(x_70);
lean_dec(x_63);
x_71 = (uint8_t)((x_43 << 24) >> 61);
x_72 = lean_expr_update_lambda(x_3, x_71, x_45, x_62);
lean_inc(x_72);
x_73 = lean_array_uset(x_70, x_6, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
case 7:
{
lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 2);
lean_inc(x_77);
x_78 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_79 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_76, x_4);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_77, x_81);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_inc(x_3);
x_87 = lean_array_uset(x_86, x_6, x_3);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
x_89 = 1;
x_90 = lean_box(x_89);
x_91 = lean_array_uset(x_88, x_6, x_90);
x_92 = lean_ctor_get(x_85, 2);
lean_inc(x_92);
lean_dec(x_85);
x_93 = (uint8_t)((x_78 << 24) >> 61);
x_94 = lean_expr_update_forall(x_3, x_93, x_80, x_84);
lean_inc(x_94);
x_95 = lean_array_uset(x_92, x_6, x_94);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_91);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_82, 1, x_96);
lean_ctor_set(x_82, 0, x_94);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_97 = lean_ctor_get(x_82, 0);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_inc(x_3);
x_100 = lean_array_uset(x_99, x_6, x_3);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
x_102 = 1;
x_103 = lean_box(x_102);
x_104 = lean_array_uset(x_101, x_6, x_103);
x_105 = lean_ctor_get(x_98, 2);
lean_inc(x_105);
lean_dec(x_98);
x_106 = (uint8_t)((x_78 << 24) >> 61);
x_107 = lean_expr_update_forall(x_3, x_106, x_80, x_97);
lean_inc(x_107);
x_108 = lean_array_uset(x_105, x_6, x_107);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_104);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
case 8:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_111 = lean_ctor_get(x_3, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 3);
lean_inc(x_113);
lean_inc(x_1);
x_114 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_111, x_4);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_1);
x_117 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_112, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_113, x_119);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_inc(x_3);
x_125 = lean_array_uset(x_124, x_6, x_3);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = 1;
x_128 = lean_box(x_127);
x_129 = lean_array_uset(x_126, x_6, x_128);
x_130 = lean_ctor_get(x_123, 2);
lean_inc(x_130);
lean_dec(x_123);
x_131 = lean_expr_update_let(x_3, x_115, x_118, x_122);
lean_inc(x_131);
x_132 = lean_array_uset(x_130, x_6, x_131);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_120, 1, x_133);
lean_ctor_set(x_120, 0, x_131);
return x_120;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_134 = lean_ctor_get(x_120, 0);
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_120);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_inc(x_3);
x_137 = lean_array_uset(x_136, x_6, x_3);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = 1;
x_140 = lean_box(x_139);
x_141 = lean_array_uset(x_138, x_6, x_140);
x_142 = lean_ctor_get(x_135, 2);
lean_inc(x_142);
lean_dec(x_135);
x_143 = lean_expr_update_let(x_3, x_115, x_118, x_134);
lean_inc(x_143);
x_144 = lean_array_uset(x_142, x_6, x_143);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_141);
lean_ctor_set(x_145, 2, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
case 10:
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_3, 1);
lean_inc(x_147);
x_148 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_147, x_4);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_inc(x_3);
x_153 = lean_array_uset(x_152, x_6, x_3);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
x_155 = 1;
x_156 = lean_box(x_155);
x_157 = lean_array_uset(x_154, x_6, x_156);
x_158 = lean_ctor_get(x_151, 2);
lean_inc(x_158);
lean_dec(x_151);
x_159 = lean_expr_update_mdata(x_3, x_150);
lean_inc(x_159);
x_160 = lean_array_uset(x_158, x_6, x_159);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_153);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set(x_161, 2, x_160);
lean_ctor_set(x_148, 1, x_161);
lean_ctor_set(x_148, 0, x_159);
return x_148;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_162 = lean_ctor_get(x_148, 0);
x_163 = lean_ctor_get(x_148, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_148);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_inc(x_3);
x_165 = lean_array_uset(x_164, x_6, x_3);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
x_167 = 1;
x_168 = lean_box(x_167);
x_169 = lean_array_uset(x_166, x_6, x_168);
x_170 = lean_ctor_get(x_163, 2);
lean_inc(x_170);
lean_dec(x_163);
x_171 = lean_expr_update_mdata(x_3, x_162);
lean_inc(x_171);
x_172 = lean_array_uset(x_170, x_6, x_171);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_165);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
case 11:
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_3, 2);
lean_inc(x_175);
x_176 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_175, x_4);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_inc(x_3);
x_181 = lean_array_uset(x_180, x_6, x_3);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
x_183 = 1;
x_184 = lean_box(x_183);
x_185 = lean_array_uset(x_182, x_6, x_184);
x_186 = lean_ctor_get(x_179, 2);
lean_inc(x_186);
lean_dec(x_179);
x_187 = lean_expr_update_proj(x_3, x_178);
lean_inc(x_187);
x_188 = lean_array_uset(x_186, x_6, x_187);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_181);
lean_ctor_set(x_189, 1, x_185);
lean_ctor_set(x_189, 2, x_188);
lean_ctor_set(x_176, 1, x_189);
lean_ctor_set(x_176, 0, x_187);
return x_176;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_190 = lean_ctor_get(x_176, 0);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_176);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_inc(x_3);
x_193 = lean_array_uset(x_192, x_6, x_3);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
x_195 = 1;
x_196 = lean_box(x_195);
x_197 = lean_array_uset(x_194, x_6, x_196);
x_198 = lean_ctor_get(x_191, 2);
lean_inc(x_198);
lean_dec(x_191);
x_199 = lean_expr_update_proj(x_3, x_190);
lean_inc(x_199);
x_200 = lean_array_uset(x_198, x_6, x_199);
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
case 12:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_3);
lean_dec(x_1);
x_203 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_204 = l_unreachable_x21___rarg(x_203);
x_205 = lean_apply_1(x_204, x_4);
return x_205;
}
default: 
{
lean_object* x_206; 
lean_dec(x_1);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_3);
lean_ctor_set(x_206, 1, x_4);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_1);
x_207 = lean_ctor_get(x_8, 0);
lean_inc(x_207);
lean_dec(x_8);
x_208 = lean_ctor_get(x_4, 0);
lean_inc(x_208);
x_209 = lean_array_uset(x_208, x_6, x_3);
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
x_211 = 1;
x_212 = lean_box(x_211);
x_213 = lean_array_uset(x_210, x_6, x_212);
x_214 = lean_ctor_get(x_4, 2);
lean_inc(x_214);
lean_dec(x_4);
lean_inc(x_207);
x_215 = lean_array_uset(x_214, x_6, x_207);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_209);
lean_ctor_set(x_216, 1, x_213);
lean_ctor_set(x_216, 2, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
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
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_mk_array(x_1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
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
lean_object* initialize_Init_Lean_ReplaceExpr(lean_object* w) {
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
