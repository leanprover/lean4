// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.IntInstTesters
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4;
lean_object* l_Lean_Meta_isInstHSubInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstNegInt___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7;
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_70; 
lean_inc_ref(x_1);
x_70 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8, x_11);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = l_Lean_Expr_cleanupAnnotations(x_71);
x_74 = l_Lean_Expr_isApp(x_73);
if (x_74 == 0)
{
lean_dec_ref(x_73);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_inc_ref(x_73);
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_73);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_73);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_inc_ref(x_75);
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_73);
x_80 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_75);
lean_inc_ref(x_77);
x_81 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
x_83 = l_Lean_Expr_isConstOf(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
x_85 = l_Lean_Expr_isConstOf(x_81, x_84);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Expr_isApp(x_81);
if (x_86 == 0)
{
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Expr_appFnCleanup___redArg(x_81);
x_88 = l_Lean_Expr_isApp(x_87);
if (x_88 == 0)
{
lean_dec_ref(x_87);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_Expr_appFnCleanup___redArg(x_87);
x_90 = l_Lean_Expr_isApp(x_89);
if (x_90 == 0)
{
lean_dec_ref(x_89);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_91);
lean_dec_ref(x_77);
x_92 = l_Lean_Expr_appFnCleanup___redArg(x_89);
x_93 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
x_94 = l_Lean_Expr_isConstOf(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
x_96 = l_Lean_Expr_isConstOf(x_92, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
x_98 = l_Lean_Expr_isConstOf(x_92, x_97);
lean_dec_ref(x_92);
if (x_98 == 0)
{
lean_dec_ref(x_91);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_72;
goto block_69;
}
else
{
lean_object* x_99; 
x_99 = l_Lean_Meta_isInstHAddInt___redArg(x_91, x_8, x_72);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec_ref(x_99);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_102;
goto block_69;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec_ref(x_99);
x_104 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_80, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_ctor_set_tag(x_105, 2);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_109, 0, x_105);
return x_109;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_109, 0);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set_tag(x_105, 2);
lean_ctor_set(x_105, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
lean_free_object(x_105);
lean_dec(x_107);
return x_109;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_105, 0);
x_116 = lean_ctor_get(x_105, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_105);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_118);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_dec(x_115);
return x_117;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_105;
}
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_99);
if (x_123 == 0)
{
return x_99;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_99, 0);
x_125 = lean_ctor_get(x_99, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_99);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
lean_object* x_127; 
lean_dec_ref(x_92);
x_127 = l_Lean_Meta_isInstHSubInt___redArg(x_91, x_8, x_72);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec_ref(x_127);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_130;
goto block_69;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec_ref(x_127);
x_132 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_80, x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_131);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_ctor_get(x_133, 1);
x_137 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_ctor_set_tag(x_133, 3);
lean_ctor_set(x_133, 1, x_139);
lean_ctor_set(x_137, 0, x_133);
return x_137;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_137, 0);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_137);
lean_ctor_set_tag(x_133, 3);
lean_ctor_set(x_133, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_133);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
lean_free_object(x_133);
lean_dec(x_135);
return x_137;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_133, 0);
x_144 = lean_ctor_get(x_133, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_133);
x_145 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_146);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
return x_150;
}
else
{
lean_dec(x_143);
return x_145;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_133;
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_151 = !lean_is_exclusive(x_127);
if (x_151 == 0)
{
return x_127;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_127, 0);
x_153 = lean_ctor_get(x_127, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_127);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_155; 
lean_dec_ref(x_92);
x_155 = l_Lean_Meta_isInstHMulInt___redArg(x_91, x_8, x_72);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec_ref(x_155);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_158;
goto block_69;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec_ref(x_155);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_80);
x_160 = l_Lean_Meta_getIntValue_x3f(x_80, x_7, x_8, x_9, x_10, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_163 = l_Lean_Meta_getIntValue_x3f(x_79, x_7, x_8, x_9, x_10, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec_ref(x_80);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_165;
goto block_69;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec_ref(x_163);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
lean_dec_ref(x_164);
x_168 = lean_unsigned_to_nat(0u);
x_169 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_80, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_166);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
lean_ctor_set(x_169, 0, x_172);
return x_169;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_169, 0);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_169);
x_175 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_167);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_dec(x_167);
return x_169;
}
}
}
else
{
uint8_t x_177; 
lean_dec_ref(x_80);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = !lean_is_exclusive(x_163);
if (x_177 == 0)
{
return x_163;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_163, 0);
x_179 = lean_ctor_get(x_163, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_163);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec_ref(x_80);
lean_dec(x_2);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_160, 1);
lean_inc(x_181);
lean_dec_ref(x_160);
x_182 = lean_ctor_get(x_161, 0);
lean_inc(x_182);
lean_dec_ref(x_161);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_183, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_181);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_184, 0, x_187);
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_184, 0);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_184);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_dec(x_182);
return x_184;
}
}
}
else
{
uint8_t x_192; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_160);
if (x_192 == 0)
{
return x_160;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_160, 0);
x_194 = lean_ctor_get(x_160, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_160);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_196 = !lean_is_exclusive(x_155);
if (x_196 == 0)
{
return x_155;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_155, 0);
x_198 = lean_ctor_get(x_155, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_155);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
}
}
else
{
lean_object* x_200; 
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_200 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_202;
goto block_69;
}
else
{
uint8_t x_203; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_203 = !lean_is_exclusive(x_200);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_200, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
lean_ctor_set_tag(x_201, 0);
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_201, 0);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_200, 0, x_207);
return x_200;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
lean_dec(x_200);
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_210;
 lean_ctor_set_tag(x_211, 0);
}
lean_ctor_set(x_211, 0, x_209);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_200);
if (x_213 == 0)
{
return x_200;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_200, 0);
x_215 = lean_ctor_get(x_200, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_200);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
else
{
lean_object* x_217; 
lean_dec_ref(x_81);
lean_dec_ref(x_77);
x_217 = l_Lean_Meta_isInstNegInt___redArg(x_80, x_8, x_72);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec_ref(x_79);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec_ref(x_217);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_220;
goto block_69;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec_ref(x_217);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_79, x_222, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_221);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_223, 0, x_226);
return x_223;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_223, 0);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_223);
x_229 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_229, 0, x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
return x_223;
}
}
}
else
{
uint8_t x_231; 
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_231 = !lean_is_exclusive(x_217);
if (x_231 == 0)
{
return x_217;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_217, 0);
x_233 = lean_ctor_get(x_217, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_217);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_235 = !lean_is_exclusive(x_70);
if (x_235 == 0)
{
return x_70;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_70, 0);
x_237 = lean_ctor_get(x_70, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_70);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
block_69:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_shareCommon___redArg(x_12, x_16, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_23, x_13, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_box(0);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_30 = lean_grind_internalize(x_23, x_2, x_29, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_dec_ref(x_25);
x_49 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
return x_25;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_25, 0);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_25);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_22);
if (x_65 == 0)
{
return x_22;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_22, 0);
x_67 = lean_ctor_get(x_22, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_22);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin, lean_io_mk_world());
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
