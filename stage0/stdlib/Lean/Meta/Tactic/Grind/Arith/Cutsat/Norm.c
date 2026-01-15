// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.IntInstTesters
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
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1;
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6;
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_61; 
lean_inc_ref(x_1);
x_61 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Expr_cleanupAnnotations(x_62);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec_ref(x_63);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_65);
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_67 = l_Lean_Expr_isApp(x_66);
if (x_67 == 0)
{
lean_dec_ref(x_66);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_68);
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_66);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_71);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
x_76 = l_Lean_Expr_isConstOf(x_72, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Expr_isApp(x_72);
if (x_77 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_79 = l_Lean_Expr_isApp(x_78);
if (x_79 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
x_86 = l_Lean_Expr_isConstOf(x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
x_88 = l_Lean_Expr_isConstOf(x_82, x_87);
lean_dec_ref(x_82);
if (x_88 == 0)
{
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_71, x_9);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_93 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_65, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_95, 0, x_98);
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean_dec(x_94);
return x_95;
}
}
else
{
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_93;
}
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_89);
if (x_102 == 0)
{
return x_89;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
lean_dec(x_89);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; 
lean_dec_ref(x_82);
x_105 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_71, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_108 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_65, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_111, 0, x_114);
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_dec(x_110);
return x_111;
}
}
else
{
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_109;
}
}
}
else
{
uint8_t x_118; 
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
return x_105;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_105, 0);
lean_inc(x_119);
lean_dec(x_105);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; 
lean_dec_ref(x_82);
x_121 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_71, x_9);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_124; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_68);
x_124 = l_Lean_Meta_getIntValue_x3f(x_68, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_126 = l_Lean_Meta_getIntValue_x3f(x_65, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_dec_ref(x_68);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_unsigned_to_nat(0u);
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_129, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_130, 0, x_133);
return x_130;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
lean_dec(x_130);
x_135 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_128);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
lean_dec(x_128);
return x_130;
}
}
}
else
{
uint8_t x_137; 
lean_dec_ref(x_68);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_137 = !lean_is_exclusive(x_126);
if (x_137 == 0)
{
return x_126;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_126, 0);
lean_inc(x_138);
lean_dec(x_126);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_68);
lean_dec(x_2);
lean_dec_ref(x_1);
x_140 = lean_ctor_get(x_125, 0);
lean_inc(x_140);
lean_dec_ref(x_125);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_65, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_142, 0, x_145);
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
else
{
lean_dec(x_140);
return x_142;
}
}
}
else
{
uint8_t x_149; 
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_149 = !lean_is_exclusive(x_124);
if (x_149 == 0)
{
return x_124;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_124, 0);
lean_inc(x_150);
lean_dec(x_124);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_121);
if (x_152 == 0)
{
return x_121;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_121, 0);
lean_inc(x_153);
lean_dec(x_121);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
}
}
}
}
else
{
lean_object* x_155; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_155 = l_Lean_Meta_getIntValue_x3f(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_155, 0);
if (lean_obj_tag(x_157) == 1)
{
uint8_t x_158; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_ctor_set_tag(x_157, 0);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_free_object(x_155);
lean_dec(x_157);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
lean_dec(x_155);
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_163;
 lean_ctor_set_tag(x_164, 0);
}
lean_ctor_set(x_164, 0, x_162);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
else
{
lean_dec(x_161);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_155);
if (x_166 == 0)
{
return x_155;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_155, 0);
lean_inc(x_167);
lean_dec(x_155);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
}
else
{
lean_object* x_169; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
x_169 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_68, x_9);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_dec_ref(x_65);
x_13 = x_1;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_172 = lean_unsigned_to_nat(0u);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_65, x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_173, 0, x_176);
return x_173;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
else
{
return x_173;
}
}
}
else
{
uint8_t x_180; 
lean_dec_ref(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = !lean_is_exclusive(x_169);
if (x_180 == 0)
{
return x_169;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_169, 0);
lean_inc(x_181);
lean_dec(x_169);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
}
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_61);
if (x_183 == 0)
{
return x_61;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_61, 0);
lean_inc(x_184);
lean_dec(x_61);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
block_60:
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Sym_shareCommon___redArg(x_13, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_25, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_25);
x_30 = lean_grind_internalize(x_25, x_2, x_29, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec_ref(x_30);
x_31 = lean_grind_cutsat_mk_var(x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_2);
x_44 = lean_grind_cutsat_mk_var(x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_24, 0);
lean_inc(x_58);
lean_dec(x_24);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13);
l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
