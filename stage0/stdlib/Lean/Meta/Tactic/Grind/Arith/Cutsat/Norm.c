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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value;
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_93; 
lean_inc_ref(x_1);
x_93 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_10);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = l_Lean_Expr_cleanupAnnotations(x_94);
x_96 = l_Lean_Expr_isApp(x_95);
if (x_96 == 0)
{
lean_dec_ref(x_95);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc_ref(x_97);
x_98 = l_Lean_Expr_appFnCleanup___redArg(x_95);
x_99 = l_Lean_Expr_isApp(x_98);
if (x_99 == 0)
{
lean_dec_ref(x_98);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc_ref(x_100);
x_101 = l_Lean_Expr_appFnCleanup___redArg(x_98);
x_102 = l_Lean_Expr_isApp(x_101);
if (x_102 == 0)
{
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc_ref(x_103);
x_104 = l_Lean_Expr_appFnCleanup___redArg(x_101);
x_105 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2));
x_106 = l_Lean_Expr_isConstOf(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5));
x_108 = l_Lean_Expr_isConstOf(x_104, x_107);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Expr_isApp(x_104);
if (x_109 == 0)
{
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = l_Lean_Expr_appFnCleanup___redArg(x_104);
x_111 = l_Lean_Expr_isApp(x_110);
if (x_111 == 0)
{
lean_dec_ref(x_110);
lean_dec_ref(x_103);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Expr_appFnCleanup___redArg(x_110);
x_113 = l_Lean_Expr_isApp(x_112);
if (x_113 == 0)
{
lean_dec_ref(x_112);
lean_dec_ref(x_103);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_115 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8));
x_116 = l_Lean_Expr_isConstOf(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11));
x_118 = l_Lean_Expr_isConstOf(x_114, x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14));
x_120 = l_Lean_Expr_isConstOf(x_114, x_119);
lean_dec_ref(x_114);
if (x_120 == 0)
{
lean_dec_ref(x_103);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_121; 
x_121 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_103, x_10);
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
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_124 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_125 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_100, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_97, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_136; 
x_128 = lean_ctor_get(x_127, 0);
x_136 = !lean_is_exclusive(x_127);
if (x_136 == 0)
{
x_129 = x_127;
x_130 = x_136;
goto block_135;
}
else
{
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_128);
if (x_130 == 0)
{
lean_ctor_set(x_129, 0, x_131);
x_132 = x_129;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_131);
x_132 = x_134;
goto block_133;
}
block_133:
{
return x_132;
}
}
}
else
{
lean_dec(x_126);
return x_127;
}
}
else
{
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_125;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_dec_ref(x_100);
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_137 = lean_ctor_get(x_121, 0);
x_144 = !lean_is_exclusive(x_121);
if (x_144 == 0)
{
x_138 = x_121;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_121);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
else
{
lean_object* x_145; 
lean_dec_ref(x_114);
x_145 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_103, x_10);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_149 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_100, x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_97, x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_160; 
x_152 = lean_ctor_get(x_151, 0);
x_160 = !lean_is_exclusive(x_151);
if (x_160 == 0)
{
x_153 = x_151;
x_154 = x_160;
goto block_159;
}
else
{
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_box(0);
x_154 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_152);
if (x_154 == 0)
{
lean_ctor_set(x_153, 0, x_155);
x_156 = x_153;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
else
{
lean_dec(x_150);
return x_151;
}
}
else
{
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_149;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec_ref(x_100);
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_161 = lean_ctor_get(x_145, 0);
x_168 = !lean_is_exclusive(x_145);
if (x_168 == 0)
{
x_162 = x_145;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_145);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
}
}
else
{
lean_object* x_169; 
lean_dec_ref(x_114);
x_169 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_103, x_10);
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
lean_dec_ref(x_100);
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_172; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_100);
x_172 = l_Lean_Meta_getIntValue_x3f(x_100, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_174 = l_Lean_Meta_getIntValue_x3f(x_97, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_dec_ref(x_100);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_100, x_177, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_187; 
x_179 = lean_ctor_get(x_178, 0);
x_187 = !lean_is_exclusive(x_178);
if (x_187 == 0)
{
x_180 = x_178;
x_181 = x_187;
goto block_186;
}
else
{
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_176);
if (x_181 == 0)
{
lean_ctor_set(x_180, 0, x_182);
x_183 = x_180;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_182);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
else
{
lean_dec(x_176);
return x_178;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_195; 
lean_dec_ref(x_100);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_188 = lean_ctor_get(x_174, 0);
x_195 = !lean_is_exclusive(x_174);
if (x_195 == 0)
{
x_189 = x_174;
x_190 = x_195;
goto block_194;
}
else
{
lean_inc(x_188);
lean_dec(x_174);
x_189 = lean_box(0);
x_190 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_191; 
if (x_190 == 0)
{
x_191 = x_189;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_188);
x_191 = x_193;
goto block_192;
}
block_192:
{
return x_191;
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_100);
lean_dec(x_2);
lean_dec_ref(x_1);
x_196 = lean_ctor_get(x_173, 0);
lean_inc(x_196);
lean_dec_ref(x_173);
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_97, x_197, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_207; 
x_199 = lean_ctor_get(x_198, 0);
x_207 = !lean_is_exclusive(x_198);
if (x_207 == 0)
{
x_200 = x_198;
x_201 = x_207;
goto block_206;
}
else
{
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_box(0);
x_201 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_202, 0, x_196);
lean_ctor_set(x_202, 1, x_199);
if (x_201 == 0)
{
lean_ctor_set(x_200, 0, x_202);
x_203 = x_200;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_202);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
else
{
lean_dec(x_196);
return x_198;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec_ref(x_100);
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_208 = lean_ctor_get(x_172, 0);
x_215 = !lean_is_exclusive(x_172);
if (x_215 == 0)
{
x_209 = x_172;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_dec(x_172);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_223; 
lean_dec_ref(x_100);
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_216 = lean_ctor_get(x_169, 0);
x_223 = !lean_is_exclusive(x_169);
if (x_223 == 0)
{
x_217 = x_169;
x_218 = x_223;
goto block_222;
}
else
{
lean_inc(x_216);
lean_dec(x_169);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
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
lean_object* x_224; 
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_100);
lean_dec_ref(x_97);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_224 = l_Lean_Meta_getIntValue_x3f(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_240; 
x_225 = lean_ctor_get(x_224, 0);
x_240 = !lean_is_exclusive(x_224);
if (x_240 == 0)
{
x_226 = x_224;
x_227 = x_240;
goto block_239;
}
else
{
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_box(0);
x_227 = x_240;
goto block_239;
}
block_239:
{
if (lean_obj_tag(x_225) == 1)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_238; 
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_228 = lean_ctor_get(x_225, 0);
x_238 = !lean_is_exclusive(x_225);
if (x_238 == 0)
{
x_229 = x_225;
x_230 = x_238;
goto block_237;
}
else
{
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_box(0);
x_230 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_231; 
if (x_230 == 0)
{
lean_ctor_set_tag(x_229, 0);
x_231 = x_229;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_228);
x_231 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_232; 
if (x_227 == 0)
{
lean_ctor_set(x_226, 0, x_231);
x_232 = x_226;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
else
{
lean_del_object(x_226);
lean_dec(x_225);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_248; 
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_241 = lean_ctor_get(x_224, 0);
x_248 = !lean_is_exclusive(x_224);
if (x_248 == 0)
{
x_242 = x_224;
x_243 = x_248;
goto block_247;
}
else
{
lean_inc(x_241);
lean_dec(x_224);
x_242 = lean_box(0);
x_243 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_244; 
if (x_243 == 0)
{
x_244 = x_242;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_241);
x_244 = x_246;
goto block_245;
}
block_245:
{
return x_244;
}
}
}
}
}
else
{
lean_object* x_249; 
lean_dec_ref(x_104);
lean_dec_ref(x_103);
x_249 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_100, x_10);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_dec_ref(x_97);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
goto block_92;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_252 = lean_unsigned_to_nat(0u);
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_97, x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_262; 
x_254 = lean_ctor_get(x_253, 0);
x_262 = !lean_is_exclusive(x_253);
if (x_262 == 0)
{
x_255 = x_253;
x_256 = x_262;
goto block_261;
}
else
{
lean_inc(x_254);
lean_dec(x_253);
x_255 = lean_box(0);
x_256 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_257, 0, x_254);
if (x_256 == 0)
{
lean_ctor_set(x_255, 0, x_257);
x_258 = x_255;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_257);
x_258 = x_260;
goto block_259;
}
block_259:
{
return x_258;
}
}
}
else
{
return x_253;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_270; 
lean_dec_ref(x_97);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_263 = lean_ctor_get(x_249, 0);
x_270 = !lean_is_exclusive(x_249);
if (x_270 == 0)
{
x_264 = x_249;
x_265 = x_270;
goto block_269;
}
else
{
lean_inc(x_263);
lean_dec(x_249);
x_264 = lean_box(0);
x_265 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_266; 
if (x_265 == 0)
{
x_266 = x_264;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_263);
x_266 = x_268;
goto block_267;
}
block_267:
{
return x_266;
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
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_271 = lean_ctor_get(x_93, 0);
x_278 = !lean_is_exclusive(x_93);
if (x_278 == 0)
{
x_272 = x_93;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_93);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
block_92:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Sym_shareCommon___redArg(x_14, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_26, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_26);
x_31 = lean_grind_internalize(x_26, x_2, x_30, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
x_32 = lean_grind_cutsat_mk_var(x_26, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_41; 
x_33 = lean_ctor_get(x_32, 0);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
x_34 = x_32;
x_35 = x_41;
goto block_40;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
x_42 = lean_ctor_get(x_32, 0);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
x_43 = x_32;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_50 = lean_ctor_get(x_31, 0);
x_57 = !lean_is_exclusive(x_31);
if (x_57 == 0)
{
x_51 = x_31;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_2);
x_58 = lean_grind_cutsat_mk_var(x_26, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_67; 
x_59 = lean_ctor_get(x_58, 0);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
x_60 = x_58;
x_61 = x_67;
goto block_66;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_59);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_62);
x_63 = x_60;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
x_68 = lean_ctor_get(x_58, 0);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
x_69 = x_58;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_76 = lean_ctor_get(x_27, 0);
x_83 = !lean_is_exclusive(x_27);
if (x_83 == 0)
{
x_77 = x_27;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_27);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_84 = lean_ctor_get(x_25, 0);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
x_85 = x_25;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_25);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
}
#ifdef __cplusplus
}
#endif
