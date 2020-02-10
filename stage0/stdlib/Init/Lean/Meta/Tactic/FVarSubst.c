// Lean compiler output
// Module: Init.Lean.Meta.Tactic.FVarSubst
// Imports: Init.Lean.Expr Init.Lean.ReplaceExpr
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
lean_object* l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_RBNode_fold___main___at_Lean_Meta_FVarSubst_compose___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
uint8_t l_Lean_Meta_FVarSubst_contains(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_compose(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
uint8_t l_Lean_Meta_FVarSubst_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_NameMap_contains___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_FVarSubst_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_207; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_224 = lean_ctor_get(x_4, 1);
lean_inc(x_224);
x_225 = lean_array_uget(x_224, x_6);
lean_dec(x_224);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_box(0);
x_207 = x_227;
goto block_223;
}
else
{
lean_object* x_228; lean_object* x_229; size_t x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_4, 0);
lean_inc(x_228);
x_229 = lean_array_uget(x_228, x_6);
lean_dec(x_228);
x_230 = lean_ptr_addr(x_229);
lean_dec(x_229);
x_231 = x_230 == x_5;
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_box(0);
x_207 = x_232;
goto block_223;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_3);
x_233 = lean_ctor_get(x_4, 2);
lean_inc(x_233);
x_234 = lean_array_uget(x_233, x_6);
lean_dec(x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_4);
return x_235;
}
}
block_206:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_8, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_inc(x_3);
x_18 = lean_array_uset(x_17, x_6, x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_array_uset(x_19, x_6, x_21);
x_23 = lean_ctor_get(x_16, 2);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_expr_update_app(x_3, x_11, x_15);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_6, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_inc(x_3);
x_30 = lean_array_uset(x_29, x_6, x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_array_uset(x_31, x_6, x_33);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_expr_update_app(x_3, x_11, x_27);
lean_inc(x_36);
x_37 = lean_array_uset(x_35, x_6, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
case 6:
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_43 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_40, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_41, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_inc(x_3);
x_51 = lean_array_uset(x_50, x_6, x_3);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_array_uset(x_52, x_6, x_54);
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = (uint8_t)((x_42 << 24) >> 61);
x_58 = lean_expr_update_lambda(x_3, x_57, x_44, x_48);
lean_inc(x_58);
x_59 = lean_array_uset(x_56, x_6, x_58);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_46, 1, x_60);
lean_ctor_set(x_46, 0, x_58);
return x_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_46, 0);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_46);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_inc(x_3);
x_64 = lean_array_uset(x_63, x_6, x_3);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_array_uset(x_65, x_6, x_67);
x_69 = lean_ctor_get(x_62, 2);
lean_inc(x_69);
lean_dec(x_62);
x_70 = (uint8_t)((x_42 << 24) >> 61);
x_71 = lean_expr_update_lambda(x_3, x_70, x_44, x_61);
lean_inc(x_71);
x_72 = lean_array_uset(x_69, x_6, x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
case 7:
{
lean_object* x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_78 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_76, x_80);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_inc(x_3);
x_86 = lean_array_uset(x_85, x_6, x_3);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
x_88 = 1;
x_89 = lean_box(x_88);
x_90 = lean_array_uset(x_87, x_6, x_89);
x_91 = lean_ctor_get(x_84, 2);
lean_inc(x_91);
lean_dec(x_84);
x_92 = (uint8_t)((x_77 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_79, x_83);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_6, x_93);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_86);
lean_ctor_set(x_95, 1, x_90);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_81, 1, x_95);
lean_ctor_set(x_81, 0, x_93);
return x_81;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_81, 0);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_81);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_6, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = 1;
x_102 = lean_box(x_101);
x_103 = lean_array_uset(x_100, x_6, x_102);
x_104 = lean_ctor_get(x_97, 2);
lean_inc(x_104);
lean_dec(x_97);
x_105 = (uint8_t)((x_77 << 24) >> 61);
x_106 = lean_expr_update_forall(x_3, x_105, x_79, x_96);
lean_inc(x_106);
x_107 = lean_array_uset(x_104, x_6, x_106);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_103);
lean_ctor_set(x_108, 2, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
case 8:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_110 = lean_ctor_get(x_3, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_3, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 3);
lean_inc(x_112);
x_113 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_110, x_4);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_111, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_112, x_118);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_inc(x_3);
x_124 = lean_array_uset(x_123, x_6, x_3);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
x_126 = 1;
x_127 = lean_box(x_126);
x_128 = lean_array_uset(x_125, x_6, x_127);
x_129 = lean_ctor_get(x_122, 2);
lean_inc(x_129);
lean_dec(x_122);
x_130 = lean_expr_update_let(x_3, x_114, x_117, x_121);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_6, x_130);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_119, 1, x_132);
lean_ctor_set(x_119, 0, x_130);
return x_119;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = lean_ctor_get(x_119, 0);
x_134 = lean_ctor_get(x_119, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_119);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_inc(x_3);
x_136 = lean_array_uset(x_135, x_6, x_3);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
x_138 = 1;
x_139 = lean_box(x_138);
x_140 = lean_array_uset(x_137, x_6, x_139);
x_141 = lean_ctor_get(x_134, 2);
lean_inc(x_141);
lean_dec(x_134);
x_142 = lean_expr_update_let(x_3, x_114, x_117, x_133);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_6, x_142);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_140);
lean_ctor_set(x_144, 2, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
case 10:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_3, 1);
lean_inc(x_146);
x_147 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_146, x_4);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_inc(x_3);
x_152 = lean_array_uset(x_151, x_6, x_3);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
x_154 = 1;
x_155 = lean_box(x_154);
x_156 = lean_array_uset(x_153, x_6, x_155);
x_157 = lean_ctor_get(x_150, 2);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_expr_update_mdata(x_3, x_149);
lean_inc(x_158);
x_159 = lean_array_uset(x_157, x_6, x_158);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_152);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_147, 1, x_160);
lean_ctor_set(x_147, 0, x_158);
return x_147;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_161 = lean_ctor_get(x_147, 0);
x_162 = lean_ctor_get(x_147, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_147);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_inc(x_3);
x_164 = lean_array_uset(x_163, x_6, x_3);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
x_166 = 1;
x_167 = lean_box(x_166);
x_168 = lean_array_uset(x_165, x_6, x_167);
x_169 = lean_ctor_get(x_162, 2);
lean_inc(x_169);
lean_dec(x_162);
x_170 = lean_expr_update_mdata(x_3, x_161);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_6, x_170);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_164);
lean_ctor_set(x_172, 1, x_168);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 11:
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_3, 2);
lean_inc(x_174);
x_175 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_2, x_174, x_4);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_inc(x_3);
x_180 = lean_array_uset(x_179, x_6, x_3);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
x_182 = 1;
x_183 = lean_box(x_182);
x_184 = lean_array_uset(x_181, x_6, x_183);
x_185 = lean_ctor_get(x_178, 2);
lean_inc(x_185);
lean_dec(x_178);
x_186 = lean_expr_update_proj(x_3, x_177);
lean_inc(x_186);
x_187 = lean_array_uset(x_185, x_6, x_186);
x_188 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_188, 0, x_180);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_187);
lean_ctor_set(x_175, 1, x_188);
lean_ctor_set(x_175, 0, x_186);
return x_175;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_ctor_get(x_175, 0);
x_190 = lean_ctor_get(x_175, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_175);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_inc(x_3);
x_192 = lean_array_uset(x_191, x_6, x_3);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
x_194 = 1;
x_195 = lean_box(x_194);
x_196 = lean_array_uset(x_193, x_6, x_195);
x_197 = lean_ctor_get(x_190, 2);
lean_inc(x_197);
lean_dec(x_190);
x_198 = lean_expr_update_proj(x_3, x_189);
lean_inc(x_198);
x_199 = lean_array_uset(x_197, x_6, x_198);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_196);
lean_ctor_set(x_200, 2, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
case 12:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_3);
x_202 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_203 = l_unreachable_x21___rarg(x_202);
x_204 = lean_apply_1(x_203, x_4);
return x_204;
}
default: 
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_3);
lean_ctor_set(x_205, 1, x_4);
return x_205;
}
}
}
block_223:
{
lean_dec(x_207);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_3, 0);
lean_inc(x_208);
x_209 = l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_208);
lean_dec(x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_box(0);
x_7 = x_210;
goto block_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_4, 0);
lean_inc(x_212);
x_213 = lean_array_uset(x_212, x_6, x_3);
x_214 = lean_ctor_get(x_4, 1);
lean_inc(x_214);
x_215 = 1;
x_216 = lean_box(x_215);
x_217 = lean_array_uset(x_214, x_6, x_216);
x_218 = lean_ctor_get(x_4, 2);
lean_inc(x_218);
lean_dec(x_4);
lean_inc(x_211);
x_219 = lean_array_uset(x_218, x_6, x_211);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_211);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
lean_object* x_222; 
x_222 = lean_box(0);
x_7 = x_222;
goto block_206;
}
}
}
}
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 8192;
x_5 = l_Lean_Expr_ReplaceImpl_initCache;
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
}
lean_object* l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Meta_FVarSubst_apply___spec__2(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_fold___main___at_Lean_Meta_FVarSubst_compose___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_RBNode_fold___main___at_Lean_Meta_FVarSubst_compose___spec__1(x_1, x_3);
x_8 = l_Lean_NameMap_contains___rarg(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_FVarSubst_apply(x_7, x_5);
x_10 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_4, x_9);
x_1 = x_10;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_FVarSubst_compose(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_Meta_FVarSubst_compose___spec__1(x_1, x_2);
return x_3;
}
}
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_ReplaceExpr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
