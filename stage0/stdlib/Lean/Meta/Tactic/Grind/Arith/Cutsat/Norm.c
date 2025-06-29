// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_inc(x_1);
x_62 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8, x_11);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_cleanupAnnotations(x_63);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_69 = l_Lean_Expr_isApp(x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_68);
x_72 = l_Lean_Expr_isApp(x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
x_76 = l_Lean_Expr_isConstOf(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
x_78 = l_Lean_Expr_isConstOf(x_74, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_isApp(x_74);
if (x_79 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_74);
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_dec(x_80);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_83 = l_Lean_Expr_isApp(x_82);
if (x_83 == 0)
{
lean_dec(x_82);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Expr_appFnCleanup___redArg(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
x_86 = l_Lean_Expr_isConstOf(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
x_88 = l_Lean_Expr_isConstOf(x_84, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
x_90 = l_Lean_Expr_isConstOf(x_84, x_89);
lean_dec(x_84);
if (x_90 == 0)
{
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Meta_isInstHAddInt___redArg(x_73, x_8, x_64);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_70);
lean_dec(x_67);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_94;
goto block_61;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_70, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_95);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_ctor_set_tag(x_97, 2);
lean_ctor_set(x_97, 1, x_103);
lean_ctor_set(x_101, 0, x_97);
return x_101;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_101);
lean_ctor_set_tag(x_97, 2);
lean_ctor_set(x_97, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_free_object(x_97);
lean_dec(x_99);
return x_101;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_97);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_110);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_dec(x_107);
return x_109;
}
}
}
else
{
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_97;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_84);
x_115 = l_Lean_Meta_isInstHSubInt___redArg(x_73, x_8, x_64);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_70);
lean_dec(x_67);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_118;
goto block_61;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_70, x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_119);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
x_125 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_ctor_set_tag(x_121, 3);
lean_ctor_set(x_121, 1, x_127);
lean_ctor_set(x_125, 0, x_121);
return x_125;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_125, 0);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_125);
lean_ctor_set_tag(x_121, 3);
lean_ctor_set(x_121, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_free_object(x_121);
lean_dec(x_123);
return x_125;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_121, 0);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_121);
x_133 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_dec(x_131);
return x_133;
}
}
}
else
{
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_121;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_84);
x_139 = l_Lean_Meta_isInstHMulInt___redArg(x_73, x_8, x_64);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_70);
lean_dec(x_67);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_142;
goto block_61;
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_139);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_139, 1);
x_145 = lean_ctor_get(x_139, 0);
lean_dec(x_145);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_70);
x_146 = l_Lean_Meta_getIntValue_x3f(x_70, x_7, x_8, x_9, x_10, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_149 = l_Lean_Meta_getIntValue_x3f(x_67, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_free_object(x_139);
lean_dec(x_70);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_151;
goto block_61;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_70, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_152);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_155, 0);
lean_ctor_set_tag(x_139, 6);
lean_ctor_set(x_139, 1, x_153);
lean_ctor_set(x_139, 0, x_157);
lean_ctor_set(x_155, 0, x_139);
return x_155;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_155, 0);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_155);
lean_ctor_set_tag(x_139, 6);
lean_ctor_set(x_139, 1, x_153);
lean_ctor_set(x_139, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_139);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
lean_dec(x_153);
lean_free_object(x_139);
return x_155;
}
}
}
else
{
uint8_t x_161; 
lean_free_object(x_139);
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_149);
if (x_161 == 0)
{
return x_149;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_149, 0);
x_163 = lean_ctor_get(x_149, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_149);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_146, 1);
lean_inc(x_165);
lean_dec(x_146);
x_166 = lean_ctor_get(x_147, 0);
lean_inc(x_166);
lean_dec(x_147);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_165);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_168, 0);
lean_ctor_set_tag(x_139, 5);
lean_ctor_set(x_139, 1, x_170);
lean_ctor_set(x_139, 0, x_166);
lean_ctor_set(x_168, 0, x_139);
return x_168;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_168, 0);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_168);
lean_ctor_set_tag(x_139, 5);
lean_ctor_set(x_139, 1, x_171);
lean_ctor_set(x_139, 0, x_166);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_139);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
else
{
lean_dec(x_166);
lean_free_object(x_139);
return x_168;
}
}
}
else
{
uint8_t x_174; 
lean_free_object(x_139);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_146);
if (x_174 == 0)
{
return x_146;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_146, 0);
x_176 = lean_ctor_get(x_146, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_146);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_139, 1);
lean_inc(x_178);
lean_dec(x_139);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_70);
x_179 = l_Lean_Meta_getIntValue_x3f(x_70, x_7, x_8, x_9, x_10, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_182 = l_Lean_Meta_getIntValue_x3f(x_67, x_7, x_8, x_9, x_10, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
lean_dec(x_70);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_184;
goto block_61;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_unsigned_to_nat(0u);
x_188 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_70, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_185);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_dec(x_186);
return x_188;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_182, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_182, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_196 = x_182;
} else {
 lean_dec_ref(x_182);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_179, 1);
lean_inc(x_198);
lean_dec(x_179);
x_199 = lean_ctor_get(x_180, 0);
lean_inc(x_199);
lean_dec(x_180);
x_200 = lean_unsigned_to_nat(0u);
x_201 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_200, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_198);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_205, 0, x_199);
lean_ctor_set(x_205, 1, x_202);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
else
{
lean_dec(x_199);
return x_201;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_179, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_179, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_209 = x_179;
} else {
 lean_dec_ref(x_179);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
}
}
}
}
}
else
{
lean_object* x_211; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_211 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_213;
goto block_61;
}
else
{
uint8_t x_214; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_211);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_211, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_212);
if (x_216 == 0)
{
lean_ctor_set_tag(x_212, 0);
return x_211;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
lean_dec(x_212);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_211, 0, x_218);
return x_211;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
lean_dec(x_211);
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_221 = x_212;
} else {
 lean_dec_ref(x_212);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_221;
 lean_ctor_set_tag(x_222, 0);
}
lean_ctor_set(x_222, 0, x_220);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_219);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_211);
if (x_224 == 0)
{
return x_211;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_211, 0);
x_226 = lean_ctor_get(x_211, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_211);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_74);
lean_dec(x_73);
x_228 = l_Lean_Meta_isInstNegInt___redArg(x_70, x_8, x_64);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_67);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_231;
goto block_61;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_2);
lean_dec(x_1);
x_232 = lean_ctor_get(x_228, 1);
lean_inc(x_232);
lean_dec(x_228);
x_233 = lean_unsigned_to_nat(0u);
x_234 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_233, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_232);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_234, 0, x_237);
return x_234;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_234, 0);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_234);
x_240 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_240, 0, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
return x_234;
}
}
}
}
}
}
block_61:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = l_Lean_Meta_Grind_shareCommon___redArg(x_12, x_16, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_23, x_13, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_30 = lean_grind_internalize(x_23, x_2, x_29, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
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
lean_dec(x_25);
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
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
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
