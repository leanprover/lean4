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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4;
lean_object* l_Lean_Meta_isInstHSubInt___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstNegInt___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7;
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_59; 
lean_inc_ref(x_1);
x_59 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_Expr_cleanupAnnotations(x_60);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec_ref(x_61);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_inc_ref(x_61);
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_61);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_inc_ref(x_63);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_63);
lean_dec_ref(x_61);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_61);
x_68 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_63);
lean_inc_ref(x_65);
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
x_71 = l_Lean_Expr_isConstOf(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
x_73 = l_Lean_Expr_isConstOf(x_69, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_isApp(x_69);
if (x_74 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_65, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_65);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
x_84 = l_Lean_Expr_isConstOf(x_80, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
x_86 = l_Lean_Expr_isConstOf(x_80, x_85);
lean_dec_ref(x_80);
if (x_86 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_87; 
x_87 = l_Lean_Meta_isInstHAddInt___redArg(x_79, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_dec(x_92);
return x_93;
}
}
else
{
lean_dec_ref(x_67);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_91;
}
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
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
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
return x_87;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_87, 0);
lean_inc(x_101);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_80);
x_103 = l_Lean_Meta_isInstHSubInt___redArg(x_79, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
lean_dec(x_109);
x_114 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
else
{
lean_dec(x_108);
return x_109;
}
}
else
{
lean_dec_ref(x_67);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
}
}
else
{
uint8_t x_116; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
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
x_116 = !lean_is_exclusive(x_103);
if (x_116 == 0)
{
return x_103;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_103, 0);
lean_inc(x_117);
lean_dec(x_103);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; 
lean_dec_ref(x_80);
x_119 = l_Lean_Meta_isInstHMulInt___redArg(x_79, x_8);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_122; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_68);
x_122 = l_Lean_Meta_getIntValue_x3f(x_68, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_124 = l_Lean_Meta_getIntValue_x3f(x_67, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_68);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_68, x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_126);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
else
{
lean_dec(x_126);
return x_128;
}
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_68);
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
x_135 = !lean_is_exclusive(x_124);
if (x_135 == 0)
{
return x_124;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
lean_dec(x_124);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_68);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = lean_ctor_get(x_123, 0);
lean_inc(x_138);
lean_dec_ref(x_123);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_140, 0, x_143);
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
lean_dec(x_138);
return x_140;
}
}
}
else
{
uint8_t x_147; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
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
x_147 = !lean_is_exclusive(x_122);
if (x_147 == 0)
{
return x_122;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_122, 0);
lean_inc(x_148);
lean_dec(x_122);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
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
x_150 = !lean_is_exclusive(x_119);
if (x_150 == 0)
{
return x_119;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_119, 0);
lean_inc(x_151);
lean_dec(x_119);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
}
}
}
}
else
{
lean_object* x_153; 
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_65);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_153 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
if (lean_obj_tag(x_155) == 0)
{
lean_free_object(x_153);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
uint8_t x_156; 
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
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_ctor_set_tag(x_155, 0);
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_153, 0, x_158);
return x_153;
}
}
}
else
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_153, 0);
lean_inc(x_159);
lean_dec(x_153);
if (lean_obj_tag(x_159) == 0)
{
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
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
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 1, 0);
} else {
 x_162 = x_161;
 lean_ctor_set_tag(x_162, 0);
}
lean_ctor_set(x_162, 0, x_160);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
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
x_164 = !lean_is_exclusive(x_153);
if (x_164 == 0)
{
return x_153;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_153, 0);
lean_inc(x_165);
lean_dec(x_153);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
lean_dec_ref(x_69);
lean_dec_ref(x_65);
x_167 = l_Lean_Meta_isInstNegInt___redArg(x_68, x_8);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_dec_ref(x_67);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_67, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_171, 0, x_174);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
else
{
return x_171;
}
}
}
else
{
uint8_t x_178; 
lean_dec_ref(x_67);
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
x_178 = !lean_is_exclusive(x_167);
if (x_178 == 0)
{
return x_167;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_167, 0);
lean_inc(x_179);
lean_dec(x_167);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
}
}
}
}
}
else
{
uint8_t x_181; 
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
x_181 = !lean_is_exclusive(x_59);
if (x_181 == 0)
{
return x_59;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_59, 0);
lean_inc(x_182);
lean_dec(x_59);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
block_58:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_shareCommon___redArg(x_12, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_23, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_28 = lean_grind_internalize(x_23, x_2, x_27, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_2);
x_42 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
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
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_24;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_24, 0);
lean_inc(x_53);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
return x_22;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 0);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
