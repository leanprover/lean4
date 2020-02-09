// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Revert
// Imports: Init.Lean.Meta.Tactic.Util
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
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_elimMVarDeps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_mkFVar(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = l_Lean_Expr_fvarId_x21(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_10, x_2);
x_12 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Meta_revert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_revert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_revert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_revert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_array_get_size(x_11);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_15);
lean_inc(x_10);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
if (x_18 == 0)
{
lean_object* x_226; 
lean_dec(x_15);
lean_dec(x_7);
x_226 = lean_box(0);
x_20 = x_226;
goto block_225;
}
else
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_unsigned_to_nat(0u);
x_228 = l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(x_3, x_7, lean_box(0), x_11, x_15, x_227);
lean_dec(x_15);
lean_dec(x_7);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_box(0);
x_20 = x_229;
goto block_225;
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_9);
x_230 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_231 = l_Lean_Meta_checkNotAssigned(x_1, x_230, x_19, x_8);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_233 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_227, x_2);
x_234 = l_Lean_mkMVar(x_1);
x_235 = l_Lean_Meta_elimMVarDeps(x_233, x_234, x_19, x_232);
lean_dec(x_19);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = l_Lean_Expr_getAppNumArgsAux___main(x_237, x_227);
x_239 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_238);
x_240 = lean_mk_array(x_238, x_239);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_sub(x_238, x_241);
lean_dec(x_238);
x_243 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_237, x_240, x_242);
lean_ctor_set(x_235, 0, x_243);
return x_235;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_244 = lean_ctor_get(x_235, 0);
x_245 = lean_ctor_get(x_235, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_235);
x_246 = l_Lean_Expr_getAppNumArgsAux___main(x_244, x_227);
x_247 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_246);
x_248 = lean_mk_array(x_246, x_247);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_sub(x_246, x_249);
lean_dec(x_246);
x_251 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_244, x_248, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
}
else
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_235);
if (x_253 == 0)
{
return x_235;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_235, 0);
x_255 = lean_ctor_get(x_235, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_235);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_231);
if (x_257 == 0)
{
return x_231;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_231, 0);
x_259 = lean_ctor_get(x_231, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_231);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
block_225:
{
uint8_t x_21; 
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_8, 2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_24 = lean_ctor_get(x_22, 2);
x_49 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_22, 2, x_49);
x_50 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_51 = l_Lean_Meta_checkNotAssigned(x_1, x_50, x_19, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_53, x_2);
x_55 = l_Lean_mkMVar(x_1);
x_56 = l_Lean_Meta_elimMVarDeps(x_54, x_55, x_19, x_52);
lean_dec(x_19);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = l_Lean_Expr_getAppNumArgsAux___main(x_58, x_53);
x_61 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_60);
x_62 = lean_mk_array(x_60, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_60, x_63);
lean_dec(x_60);
x_65 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_58, x_62, x_64);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_59, 2);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 2);
lean_dec(x_69);
lean_ctor_set(x_67, 2, x_24);
lean_ctor_set(x_56, 0, x_65);
return x_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_24);
lean_ctor_set(x_59, 2, x_72);
lean_ctor_set(x_56, 0, x_65);
return x_56;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_59, 2);
x_74 = lean_ctor_get(x_59, 0);
x_75 = lean_ctor_get(x_59, 1);
x_76 = lean_ctor_get(x_59, 3);
x_77 = lean_ctor_get(x_59, 4);
x_78 = lean_ctor_get(x_59, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_73);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_59);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_24);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_76);
lean_ctor_set(x_83, 4, x_77);
lean_ctor_set(x_83, 5, x_78);
lean_ctor_set(x_56, 1, x_83);
lean_ctor_set(x_56, 0, x_65);
return x_56;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_84 = lean_ctor_get(x_56, 0);
x_85 = lean_ctor_get(x_56, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_56);
x_86 = l_Lean_Expr_getAppNumArgsAux___main(x_84, x_53);
x_87 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_86);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_86, x_89);
lean_dec(x_86);
x_91 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_84, x_88, x_90);
x_92 = lean_ctor_get(x_85, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 5);
lean_inc(x_97);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 lean_ctor_release(x_85, 5);
 x_98 = x_85;
} else {
 lean_dec_ref(x_85);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_92, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_101 = x_92;
} else {
 lean_dec_ref(x_92);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 3, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_24);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 6, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_94);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_95);
lean_ctor_set(x_103, 4, x_96);
lean_ctor_set(x_103, 5, x_97);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_56, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_56, 1);
lean_inc(x_106);
lean_dec(x_56);
x_25 = x_105;
x_26 = x_106;
goto block_48;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_51, 1);
lean_inc(x_108);
lean_dec(x_51);
x_25 = x_107;
x_26 = x_108;
goto block_48;
}
block_48:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 2);
lean_dec(x_30);
lean_ctor_set(x_28, 2, x_24);
if (lean_is_scalar(x_9)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_9;
 lean_ctor_set_tag(x_31, 1);
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_26, 2, x_34);
if (lean_is_scalar(x_9)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_9;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 3, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_24);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
if (lean_is_scalar(x_9)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_9;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_109 = lean_ctor_get(x_22, 0);
x_110 = lean_ctor_get(x_22, 1);
x_111 = lean_ctor_get(x_22, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_22);
x_128 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_109);
lean_ctor_set(x_129, 1, x_110);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_8, 2, x_129);
x_130 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_131 = l_Lean_Meta_checkNotAssigned(x_1, x_130, x_19, x_8);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_133, x_2);
x_135 = l_Lean_mkMVar(x_1);
x_136 = l_Lean_Meta_elimMVarDeps(x_134, x_135, x_19, x_132);
lean_dec(x_19);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_9);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = l_Lean_Expr_getAppNumArgsAux___main(x_137, x_133);
x_141 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_140, x_143);
lean_dec(x_140);
x_145 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_137, x_142, x_144);
x_146 = lean_ctor_get(x_138, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_138, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_138, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 x_152 = x_138;
} else {
 lean_dec_ref(x_138);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_146, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 x_155 = x_146;
} else {
 lean_dec_ref(x_146);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_111);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_149);
lean_ctor_set(x_157, 4, x_150);
lean_ctor_set(x_157, 5, x_151);
if (lean_is_scalar(x_139)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_139;
}
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_136, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_136, 1);
lean_inc(x_160);
lean_dec(x_136);
x_112 = x_159;
x_113 = x_160;
goto block_127;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_131, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_131, 1);
lean_inc(x_162);
lean_dec(x_131);
x_112 = x_161;
x_113 = x_162;
goto block_127;
}
block_127:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_114 = lean_ctor_get(x_113, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 x_123 = x_114;
} else {
 lean_dec_ref(x_114);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 3, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_111);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set(x_125, 4, x_118);
lean_ctor_set(x_125, 5, x_119);
if (lean_is_scalar(x_9)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_9;
 lean_ctor_set_tag(x_126, 1);
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_163 = lean_ctor_get(x_8, 2);
x_164 = lean_ctor_get(x_8, 0);
x_165 = lean_ctor_get(x_8, 1);
x_166 = lean_ctor_get(x_8, 3);
x_167 = lean_ctor_get(x_8, 4);
x_168 = lean_ctor_get(x_8, 5);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_163);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_8);
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 2);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
x_189 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_172)) {
 x_190 = lean_alloc_ctor(0, 3, 0);
} else {
 x_190 = x_172;
}
lean_ctor_set(x_190, 0, x_169);
lean_ctor_set(x_190, 1, x_170);
lean_ctor_set(x_190, 2, x_189);
x_191 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_191, 0, x_164);
lean_ctor_set(x_191, 1, x_165);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_166);
lean_ctor_set(x_191, 4, x_167);
lean_ctor_set(x_191, 5, x_168);
x_192 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_193 = l_Lean_Meta_checkNotAssigned(x_1, x_192, x_19, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_unsigned_to_nat(0u);
x_196 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_195, x_2);
x_197 = l_Lean_mkMVar(x_1);
x_198 = l_Lean_Meta_elimMVarDeps(x_196, x_197, x_19, x_194);
lean_dec(x_19);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_9);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Expr_getAppNumArgsAux___main(x_199, x_195);
x_203 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_202);
x_204 = lean_mk_array(x_202, x_203);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_nat_sub(x_202, x_205);
lean_dec(x_202);
x_207 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_199, x_204, x_206);
x_208 = lean_ctor_get(x_200, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 3);
lean_inc(x_211);
x_212 = lean_ctor_get(x_200, 4);
lean_inc(x_212);
x_213 = lean_ctor_get(x_200, 5);
lean_inc(x_213);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 x_214 = x_200;
} else {
 lean_dec_ref(x_200);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_208, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_208, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_217 = x_208;
} else {
 lean_dec_ref(x_208);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 3, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
lean_ctor_set(x_218, 2, x_171);
if (lean_is_scalar(x_214)) {
 x_219 = lean_alloc_ctor(0, 6, 0);
} else {
 x_219 = x_214;
}
lean_ctor_set(x_219, 0, x_209);
lean_ctor_set(x_219, 1, x_210);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_211);
lean_ctor_set(x_219, 4, x_212);
lean_ctor_set(x_219, 5, x_213);
if (lean_is_scalar(x_201)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_201;
}
lean_ctor_set(x_220, 0, x_207);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_198, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_198, 1);
lean_inc(x_222);
lean_dec(x_198);
x_173 = x_221;
x_174 = x_222;
goto block_188;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_193, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_193, 1);
lean_inc(x_224);
lean_dec(x_193);
x_173 = x_223;
x_174 = x_224;
goto block_188;
}
block_188:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_175 = lean_ctor_get(x_174, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 x_184 = x_175;
} else {
 lean_dec_ref(x_175);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_171);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
if (lean_is_scalar(x_9)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_9;
 lean_ctor_set_tag(x_187, 1);
}
lean_ctor_set(x_187, 0, x_173);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_6);
if (x_261 == 0)
{
return x_6;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_6, 0);
x_263 = lean_ctor_get(x_6, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_6);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_2);
lean_ctor_set(x_265, 1, x_1);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_4);
return x_266;
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_revert(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Revert(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_revert___closed__1 = _init_l_Lean_Meta_revert___closed__1();
lean_mark_persistent(l_Lean_Meta_revert___closed__1);
l_Lean_Meta_revert___closed__2 = _init_l_Lean_Meta_revert___closed__2();
lean_mark_persistent(l_Lean_Meta_revert___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
