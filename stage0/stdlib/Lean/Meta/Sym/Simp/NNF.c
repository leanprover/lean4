// Lean compiler output
// Module: Lean.Meta.Sym.Simp.NNF
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Util import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Init.Grind.Norm import Init.Sym.Lemmas
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
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkNotS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkOrS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkExistsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_Sym_mkAndS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "imp_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 83, 152, 39, 213, 103, 165, 10)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__4;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_forall"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__7_value),LEAN_SCALAR_PTR_LITERAL(133, 192, 91, 90, 91, 211, 131, 26)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__10_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__11_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__12_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__13_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__14_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__15_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__16_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__17_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__18_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ite_eq_and"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__19_value),LEAN_SCALAR_PTR_LITERAL(129, 97, 31, 89, 241, 41, 194, 82)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__23;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__24_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__25_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cond_eq_and"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__26_value),LEAN_SCALAR_PTR_LITERAL(83, 251, 1, 132, 120, 220, 250, 120)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__28;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_prop_eq_and"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__30_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__29_value),LEAN_SCALAR_PTR_LITERAL(196, 211, 222, 129, 241, 70, 136, 15)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__31;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "iff_eq_and"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__32_value),LEAN_SCALAR_PTR_LITERAL(121, 72, 168, 42, 146, 38, 94, 94)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__33 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__34;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__35 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__35_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__36 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__36_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__37 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__37_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__38 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__38_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__39 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__39_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__40 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__40_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__41 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__41_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__42 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__42_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__43_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__44 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__44_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_and"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__45 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__46_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__46_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__45_value),LEAN_SCALAR_PTR_LITERAL(239, 225, 24, 71, 205, 142, 249, 26)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__46 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__46_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__47;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "not_or"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__48 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__48_value),LEAN_SCALAR_PTR_LITERAL(235, 74, 178, 162, 31, 3, 143, 38)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__49 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__49_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__50;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__51 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__51_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__52 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__52_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_exists"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__53 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__54_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__54_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__53_value),LEAN_SCALAR_PTR_LITERAL(122, 84, 103, 56, 9, 28, 88, 199)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__54 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__54_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_not"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__55 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__55_value),LEAN_SCALAR_PTR_LITERAL(37, 13, 167, 116, 75, 172, 227, 19)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__56 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__56_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__57;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__58 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__59_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__59_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__58_value),LEAN_SCALAR_PTR_LITERAL(189, 233, 184, 33, 201, 88, 141, 182)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__59 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__59_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__60;
static const lean_string_object l_Lean_Meta_Sym_Simp_nnf___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__61 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__62_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__6_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_nnf___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__62_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__61_value),LEAN_SCALAR_PTR_LITERAL(32, 161, 26, 17, 134, 82, 22, 22)}};
static const lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__62 = (const lean_object*)&l_Lean_Meta_Sym_Simp_nnf___closed__62_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_nnf___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_nnf___closed__63;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_nnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_nnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0(lean_object* v_x_1_, uint8_t v_bi_2_, lean_object* v_t_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___y_13_; lean_object* v___x_16_; uint8_t v_debug_17_; 
v___x_16_ = lean_st_ref_get(v___y_6_);
v_debug_17_ = lean_ctor_get_uint8(v___x_16_, sizeof(void*)*13);
lean_dec(v___x_16_);
if (v_debug_17_ == 0)
{
v___y_13_ = v___y_6_;
goto v___jp_12_;
}
else
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_3_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v___x_19_; 
lean_dec_ref_known(v___x_18_, 1);
v___x_19_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_dec_ref_known(v___x_19_, 1);
v___y_13_ = v___y_6_;
goto v___jp_12_;
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec_ref(v_b_4_);
lean_dec_ref(v_t_3_);
lean_dec(v_x_1_);
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
lean_dec_ref(v_b_4_);
lean_dec_ref(v_t_3_);
lean_dec(v_x_1_);
v_a_28_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_18_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_18_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
v___jp_12_:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = l_Lean_Expr_forallE___override(v_x_1_, v_t_3_, v_b_4_, v_bi_2_);
v___x_15_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_14_, v___y_13_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0___boxed(lean_object* v_x_36_, lean_object* v_bi_37_, lean_object* v_t_38_, lean_object* v_b_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_bi_boxed_47_; lean_object* v_res_48_; 
v_bi_boxed_47_ = lean_unbox(v_bi_37_);
v_res_48_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0(v_x_36_, v_bi_boxed_47_, v_t_38_, v_b_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(lean_object* v_p_49_, lean_object* v_q_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = 0;
v___x_60_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS_spec__0(v___x_58_, v___x_59_, v_p_49_, v_q_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS___boxed(lean_object* v_p_61_, lean_object* v_q_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_p_61_, v_q_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg(lean_object* v_x_71_, uint8_t v_bi_72_, lean_object* v_t_73_, lean_object* v_b_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___y_83_; lean_object* v___x_86_; uint8_t v_debug_87_; 
v___x_86_ = lean_st_ref_get(v___y_76_);
v_debug_87_ = lean_ctor_get_uint8(v___x_86_, sizeof(void*)*13);
lean_dec(v___x_86_);
if (v_debug_87_ == 0)
{
v___y_83_ = v___y_76_;
goto v___jp_82_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_73_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_dec_ref_known(v___x_89_, 1);
v___y_83_ = v___y_76_;
goto v___jp_82_;
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_dec_ref(v_b_74_);
lean_dec_ref(v_t_73_);
lean_dec(v_x_71_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_b_74_);
lean_dec_ref(v_t_73_);
lean_dec(v_x_71_);
v_a_98_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_88_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = l_Lean_Expr_lam___override(v_x_71_, v_t_73_, v_b_74_, v_bi_72_);
v___x_85_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_84_, v___y_83_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg___boxed(lean_object* v_x_106_, lean_object* v_bi_107_, lean_object* v_t_108_, lean_object* v_b_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
uint8_t v_bi_boxed_117_; lean_object* v_res_118_; 
v_bi_boxed_117_ = lean_unbox(v_bi_107_);
v_res_118_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg(v_x_106_, v_bi_boxed_117_, v_t_108_, v_b_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0(lean_object* v_x_119_, uint8_t v_bi_120_, lean_object* v_t_121_, lean_object* v_b_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg(v_x_119_, v_bi_120_, v_t_121_, v_b_122_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___boxed(lean_object* v_x_134_, lean_object* v_bi_135_, lean_object* v_t_136_, lean_object* v_b_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v_bi_boxed_148_; lean_object* v_res_149_; 
v_bi_boxed_148_ = lean_unbox(v_bi_135_);
v_res_149_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0(v_x_134_, v_bi_boxed_148_, v_t_136_, v_b_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(lean_object* v_declName_150_, lean_object* v_us_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = l_Lean_Expr_const___override(v_declName_150_, v_us_151_);
v___x_155_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_154_, v___y_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg___boxed(lean_object* v_declName_156_, lean_object* v_us_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(v_declName_156_, v_us_157_, v___y_158_);
lean_dec(v___y_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1(lean_object* v_declName_161_, lean_object* v_us_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(v_declName_161_, v_us_162_, v___y_167_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___boxed(lean_object* v_declName_174_, lean_object* v_us_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1(v_declName_174_, v_us_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg(lean_object* v_idx_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Lean_Expr_bvar___override(v_idx_187_);
v___x_191_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_190_, v___y_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg___boxed(lean_object* v_idx_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg(v_idx_192_, v___y_193_);
lean_dec(v___y_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3(lean_object* v_idx_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg(v_idx_196_, v___y_201_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___boxed(lean_object* v_idx_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3(v_idx_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg(lean_object* v_x_220_, uint8_t v_bi_221_, lean_object* v_t_222_, lean_object* v_b_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___y_232_; lean_object* v___x_235_; uint8_t v_debug_236_; 
v___x_235_ = lean_st_ref_get(v___y_225_);
v_debug_236_ = lean_ctor_get_uint8(v___x_235_, sizeof(void*)*13);
lean_dec(v___x_235_);
if (v_debug_236_ == 0)
{
v___y_232_ = v___y_225_;
goto v___jp_231_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_222_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; 
lean_dec_ref_known(v___x_237_, 1);
v___x_238_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_dec_ref_known(v___x_238_, 1);
v___y_232_ = v___y_225_;
goto v___jp_231_;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_t_222_);
lean_dec(v_x_220_);
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_t_222_);
lean_dec(v_x_220_);
v_a_247_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_237_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Lean_Expr_forallE___override(v_x_220_, v_t_222_, v_b_223_, v_bi_221_);
v___x_234_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_233_, v___y_232_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg___boxed(lean_object* v_x_255_, lean_object* v_bi_256_, lean_object* v_t_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_bi_boxed_266_; lean_object* v_res_267_; 
v_bi_boxed_266_ = lean_unbox(v_bi_256_);
v_res_267_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg(v_x_255_, v_bi_boxed_266_, v_t_257_, v_b_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4(lean_object* v_x_268_, uint8_t v_bi_269_, lean_object* v_t_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg(v_x_268_, v_bi_269_, v_t_270_, v_b_271_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___boxed(lean_object* v_x_283_, lean_object* v_bi_284_, lean_object* v_t_285_, lean_object* v_b_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v_bi_boxed_297_; lean_object* v_res_298_; 
v_bi_boxed_297_ = lean_unbox(v_bi_284_);
v_res_298_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4(v_x_283_, v_bi_boxed_297_, v_t_285_, v_b_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(lean_object* v_f_299_, lean_object* v_a_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___y_309_; lean_object* v___x_312_; uint8_t v_debug_313_; 
v___x_312_ = lean_st_ref_get(v___y_302_);
v_debug_313_ = lean_ctor_get_uint8(v___x_312_, sizeof(void*)*13);
lean_dec(v___x_312_);
if (v_debug_313_ == 0)
{
v___y_309_ = v___y_302_;
goto v___jp_308_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_299_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; 
lean_dec_ref_known(v___x_314_, 1);
v___x_315_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_dec_ref_known(v___x_315_, 1);
v___y_309_ = v___y_302_;
goto v___jp_308_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_a_300_);
lean_dec_ref(v_f_299_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_a_300_);
lean_dec_ref(v_f_299_);
v_a_324_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_314_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_314_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = l_Lean_Expr_app___override(v_f_299_, v_a_300_);
v___x_311_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_310_, v___y_309_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg___boxed(lean_object* v_f_332_, lean_object* v_a_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(v_f_332_, v_a_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2(lean_object* v_f_342_, lean_object* v_a_u2081_343_, lean_object* v_a_u2082_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(v_f_342_, v_a_u2081_343_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(v_a_356_, v_a_u2082_344_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_357_;
}
else
{
lean_dec_ref(v_a_u2082_344_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2___boxed(lean_object* v_f_358_, lean_object* v_a_u2081_359_, lean_object* v_a_u2082_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2(v_f_358_, v_a_u2081_359_, v_a_u2082_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2(lean_object* v_f_372_, lean_object* v_a_u2081_373_, lean_object* v_a_u2082_374_, lean_object* v_a_u2083_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__2(v_f_372_, v_a_u2081_373_, v_a_u2082_374_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(v_a_387_, v_a_u2083_375_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_388_;
}
else
{
lean_dec_ref(v_a_u2083_375_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2___boxed(lean_object* v_f_389_, lean_object* v_a_u2081_390_, lean_object* v_a_u2082_391_, lean_object* v_a_u2083_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2(v_f_389_, v_a_u2081_390_, v_a_u2082_391_, v_a_u2083_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__4(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_box(0);
v___x_412_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__3));
v___x_413_ = l_Lean_mkConst(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__21(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__20));
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__22(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = l_Lean_Level_ofNat(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__23(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__22, &l_Lean_Meta_Sym_Simp_nnf___closed__22_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__22);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__28(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__27));
v___x_460_ = l_Lean_mkConst(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__31(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__30));
v___x_468_ = l_Lean_mkConst(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__34(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(0);
v___x_475_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__33));
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__47(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
v___x_498_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__46));
v___x_499_ = l_Lean_mkConst(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__50(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_box(0);
v___x_506_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__49));
v___x_507_ = l_Lean_mkConst(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__57(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_box(0);
v___x_522_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__56));
v___x_523_ = l_Lean_mkConst(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__60(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
v___x_530_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__59));
v___x_531_ = l_Lean_mkConst(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_nnf___closed__63(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__62));
v___x_539_ = l_Lean_mkConst(v___x_538_, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_nnf(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
uint8_t v_a_552_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___x_622_; 
lean_inc_ref(v_e_540_);
v___x_622_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_540_, v_a_547_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_1189_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_1189_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_1189_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = l_Lean_Expr_cleanupAnnotations(v_a_623_);
lean_dec(v_a_623_);
v___x_628_ = l_Lean_Expr_isApp(v___x_627_);
if (v___x_628_ == 0)
{
lean_dec_ref(v___x_627_);
lean_del_object(v___x_625_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v_arg_629_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_arg_629_ = lean_ctor_get(v___x_627_, 1);
lean_inc_ref(v_arg_629_);
v___x_708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_627_);
lean_dec_ref(v___x_627_);
v___x_709_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__10));
v___x_710_ = l_Lean_Expr_isConstOf(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
lean_del_object(v___x_625_);
v___x_711_ = l_Lean_Expr_isApp(v___x_708_);
if (v___x_711_ == 0)
{
lean_dec_ref(v___x_708_);
lean_dec_ref(v_arg_629_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v_arg_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_arg_712_ = lean_ctor_get(v___x_708_, 1);
lean_inc_ref(v_arg_712_);
v___x_713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
lean_dec_ref(v___x_708_);
v___x_714_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__12));
v___x_715_ = l_Lean_Expr_isConstOf(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_716_ == 0)
{
lean_dec_ref(v___x_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v_arg_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_arg_717_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_arg_717_);
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
lean_dec_ref(v___x_713_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__14));
v___x_720_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_718_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v_arg_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_arg_722_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_722_);
v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
lean_dec_ref(v___x_718_);
v___x_724_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__16));
v___x_725_ = l_Lean_Expr_isConstOf(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_Expr_isApp(v___x_723_);
if (v___x_726_ == 0)
{
lean_dec_ref(v___x_723_);
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_723_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__18));
v___x_729_ = l_Lean_Expr_isConstOf(v___x_727_, v___x_728_);
lean_dec_ref(v___x_727_);
if (v___x_729_ == 0)
{
lean_dec_ref(v___x_723_);
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_555_;
}
else
{
lean_object* v_arg_730_; uint8_t v___x_731_; 
lean_dec_ref(v_e_540_);
v_arg_730_ = lean_ctor_get(v___x_723_, 1);
lean_inc_ref(v_arg_730_);
lean_dec_ref(v___x_723_);
v___x_731_ = l_Lean_Expr_isProp(v_arg_730_);
lean_dec_ref(v_arg_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___x_732_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_732_, 0, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; 
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_arg_722_);
v___x_734_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_arg_722_, v_arg_712_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
lean_inc_ref(v_arg_722_);
v___x_736_ = l_Lean_Meta_Sym_mkNotS(v_arg_722_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
lean_inc_ref(v_arg_629_);
v___x_738_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_a_737_, v_arg_629_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Meta_Sym_mkAndS(v_a_735_, v_a_739_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_751_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__21, &l_Lean_Meta_Sym_Simp_nnf___closed__21_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__21);
v___x_746_ = l_Lean_mkApp4(v___x_745_, v_arg_722_, v_arg_717_, v_arg_712_, v_arg_629_);
v___x_747_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_747_, 0, v_a_741_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*2, v___x_725_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*2 + 1, v___x_725_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_752_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_740_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_740_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_735_);
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_760_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_738_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_738_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_a_735_);
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_768_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_736_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_736_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_arg_722_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_776_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_734_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_734_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_784_; 
lean_dec_ref(v___x_723_);
lean_dec_ref(v_e_540_);
v___x_784_ = l_Lean_Expr_isProp(v_arg_722_);
lean_dec_ref(v_arg_722_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___x_785_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_785_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_box(0);
v___x_788_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__23, &l_Lean_Meta_Sym_Simp_nnf___closed__23_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__23);
v___x_789_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(v___x_719_, v___x_788_, v_a_545_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__25));
v___x_792_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_Simp_nnf_spec__1___redArg(v___x_791_, v___x_787_, v_a_545_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_544_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
lean_inc_ref(v_arg_717_);
v___x_796_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2(v_a_790_, v_a_793_, v_arg_717_, v_a_795_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_n(v_a_797_, 2);
lean_dec_ref_known(v___x_796_, 1);
lean_inc_ref(v_arg_712_);
v___x_798_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_a_797_, v_arg_712_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_Meta_Sym_mkNotS(v_a_797_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
lean_inc_ref(v_arg_629_);
v___x_802_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_a_801_, v_arg_629_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = l_Lean_Meta_Sym_mkAndS(v_a_799_, v_a_803_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_809_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__28, &l_Lean_Meta_Sym_Simp_nnf___closed__28_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__28);
v___x_810_ = l_Lean_mkApp3(v___x_809_, v_arg_717_, v_arg_712_, v_arg_629_);
v___x_811_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_811_, 0, v_a_805_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*2, v___x_720_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*2 + 1, v___x_720_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_816_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_804_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_804_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_799_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_824_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_802_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_802_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_799_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_832_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_800_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_800_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_797_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_840_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_798_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_798_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_848_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_796_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_796_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_793_);
lean_dec(v_a_790_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_856_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_794_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_794_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_790_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_864_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_792_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_792_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_872_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_789_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_789_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_880_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v_e_540_);
v___x_880_ = l_Lean_Expr_isProp(v_arg_717_);
lean_dec_ref(v_arg_717_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v___x_881_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_881_, 0, v___x_880_);
lean_ctor_set_uint8(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; 
lean_inc_ref(v_arg_629_);
lean_inc_ref(v_arg_712_);
v___x_883_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_arg_712_, v_arg_629_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_arg_629_);
v___x_885_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_arg_629_, v_arg_712_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Meta_Sym_mkAndS(v_a_884_, v_a_886_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_898_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_898_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_892_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__31, &l_Lean_Meta_Sym_Simp_nnf___closed__31_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__31);
v___x_893_ = l_Lean_mkAppB(v___x_892_, v_arg_712_, v_arg_629_);
v___x_894_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_894_, 0, v_a_888_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*2, v___x_715_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*2 + 1, v___x_715_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_894_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_899_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_887_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_887_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_884_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_907_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_885_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_885_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_915_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_883_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_883_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec_ref(v___x_713_);
lean_dec_ref(v_e_540_);
lean_inc_ref(v_arg_629_);
lean_inc_ref(v_arg_712_);
v___x_923_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_arg_712_, v_arg_629_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
lean_inc_ref(v_arg_712_);
lean_inc_ref(v_arg_629_);
v___x_925_ = l___private_Lean_Meta_Sym_Simp_NNF_0__Lean_Meta_Sym_Simp_nnf_mkArrowS(v_arg_629_, v_arg_712_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l_Lean_Meta_Sym_mkAndS(v_a_924_, v_a_926_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_938_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_938_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__34, &l_Lean_Meta_Sym_Simp_nnf___closed__34_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__34);
v___x_933_ = l_Lean_mkAppB(v___x_932_, v_arg_712_, v_arg_629_);
v___x_934_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_934_, 0, v_a_928_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*2, v___x_710_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*2 + 1, v___x_710_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_934_);
v___x_936_ = v___x_930_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_939_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_927_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_927_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_a_924_);
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_947_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_925_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_925_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec_ref(v_arg_712_);
lean_dec_ref(v_arg_629_);
v_a_955_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_923_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_923_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v___x_708_);
lean_dec_ref(v_e_540_);
lean_inc_ref(v_arg_629_);
v___x_963_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_629_, v_a_547_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1180_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_1180_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1180_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_968_ = l_Lean_Expr_cleanupAnnotations(v_a_964_);
lean_dec(v_a_964_);
v___x_969_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__36));
v___x_970_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__38));
v___x_972_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_971_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_Expr_isApp(v___x_968_);
if (v___x_973_ == 0)
{
lean_dec_ref(v___x_968_);
lean_del_object(v___x_966_);
v___y_631_ = v_a_541_;
v___y_632_ = v_a_542_;
v___y_633_ = v_a_543_;
v___y_634_ = v_a_544_;
v___y_635_ = v_a_545_;
v___y_636_ = v_a_546_;
v___y_637_ = v_a_547_;
v___y_638_ = v_a_548_;
v___y_639_ = v_a_549_;
goto v___jp_630_;
}
else
{
lean_object* v_arg_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_arg_974_ = lean_ctor_get(v___x_968_, 1);
lean_inc_ref(v_arg_974_);
v___x_975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_968_);
lean_dec_ref(v___x_968_);
v___x_976_ = l_Lean_Expr_isConstOf(v___x_975_, v___x_709_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; 
lean_del_object(v___x_966_);
v___x_977_ = l_Lean_Expr_isApp(v___x_975_);
if (v___x_977_ == 0)
{
lean_dec_ref(v___x_975_);
lean_dec_ref(v_arg_974_);
v___y_631_ = v_a_541_;
v___y_632_ = v_a_542_;
v___y_633_ = v_a_543_;
v___y_634_ = v_a_544_;
v___y_635_ = v_a_545_;
v___y_636_ = v_a_546_;
v___y_637_ = v_a_547_;
v___y_638_ = v_a_548_;
v___y_639_ = v_a_549_;
goto v___jp_630_;
}
else
{
lean_object* v_arg_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_arg_978_ = lean_ctor_get(v___x_975_, 1);
lean_inc_ref(v_arg_978_);
v___x_979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_975_);
lean_dec_ref(v___x_975_);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__40));
v___x_981_ = l_Lean_Expr_isConstOf(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__42));
v___x_983_ = l_Lean_Expr_isConstOf(v___x_979_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__44));
v___x_985_ = l_Lean_Expr_isConstOf(v___x_979_, v___x_984_);
lean_dec_ref(v___x_979_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v___y_631_ = v_a_541_;
v___y_632_ = v_a_542_;
v___y_633_ = v_a_543_;
v___y_634_ = v_a_544_;
v___y_635_ = v_a_545_;
v___y_636_ = v_a_546_;
v___y_637_ = v_a_547_;
v___y_638_ = v_a_548_;
v___y_639_ = v_a_549_;
goto v___jp_630_;
}
else
{
lean_object* v___x_986_; 
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
lean_inc_ref(v_arg_978_);
v___x_986_ = l_Lean_Meta_Sym_mkNotS(v_arg_978_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
lean_inc_ref(v_arg_974_);
v___x_988_ = l_Lean_Meta_Sym_mkNotS(v_arg_974_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_Lean_Meta_Sym_mkOrS(v_a_987_, v_a_989_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1001_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_995_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__47, &l_Lean_Meta_Sym_Simp_nnf___closed__47_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__47);
v___x_996_ = l_Lean_mkAppB(v___x_995_, v_arg_978_, v_arg_974_);
v___x_997_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_997_, 0, v_a_991_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*2, v___x_983_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*2 + 1, v___x_983_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_997_);
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1002_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_990_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_990_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_987_);
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1010_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_988_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_988_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1018_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_986_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_986_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_979_);
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
lean_inc_ref(v_arg_978_);
v___x_1026_ = l_Lean_Meta_Sym_mkNotS(v_arg_978_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
lean_inc_ref(v_arg_974_);
v___x_1028_ = l_Lean_Meta_Sym_mkNotS(v_arg_974_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = l_Lean_Meta_Sym_mkAndS(v_a_1027_, v_a_1029_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__50, &l_Lean_Meta_Sym_Simp_nnf___closed__50_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__50);
v___x_1036_ = l_Lean_mkAppB(v___x_1035_, v_arg_978_, v_arg_974_);
v___x_1037_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1037_, 0, v_a_1031_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*2, v___x_981_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*2 + 1, v___x_981_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1039_ = v___x_1033_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1042_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1030_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1027_);
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1050_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1028_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1028_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1058_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1026_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1026_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec_ref(v___x_979_);
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_Simp_nnf_spec__3___redArg(v___x_1066_, v_a_545_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_mk_empty_array_with_capacity(v___x_1069_);
v___x_1071_ = lean_array_push(v___x_1070_, v_a_1068_);
lean_inc_ref(v_arg_974_);
v___x_1072_ = l_Lean_Meta_Sym_betaS(v_arg_974_, v___x_1071_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = l_Lean_Meta_Sym_mkNotS(v_a_1073_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__52));
v___x_1077_ = 0;
lean_inc_ref(v_arg_978_);
v___x_1078_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_nnf_spec__4___redArg(v___x_1076_, v___x_1077_, v_arg_978_, v_a_1075_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
lean_inc_ref(v_arg_978_);
v___x_1080_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_978_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1094_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1085_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__54));
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_a_1081_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_mkConst(v___x_1085_, v___x_1087_);
v___x_1089_ = l_Lean_mkAppB(v___x_1088_, v_arg_978_, v_arg_974_);
v___x_1090_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1090_, 0, v_a_1079_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*2, v___x_976_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*2 + 1, v___x_976_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1090_);
v___x_1092_ = v___x_1083_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_a_1079_);
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1095_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1080_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1080_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1103_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1078_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1078_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1111_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1074_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1074_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1119_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1072_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1072_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_974_);
v_a_1127_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1067_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1067_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_975_);
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__57, &l_Lean_Meta_Sym_Simp_nnf___closed__57_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__57);
lean_inc_ref(v_arg_974_);
v___x_1136_ = l_Lean_Expr_app___override(v___x_1135_, v_arg_974_);
v___x_1137_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1137_, 0, v_arg_974_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*2, v___x_972_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*2 + 1, v___x_972_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_1137_);
v___x_1139_ = v___x_966_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_968_);
lean_del_object(v___x_966_);
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
v___x_1141_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_544_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1151_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1146_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__60, &l_Lean_Meta_Sym_Simp_nnf___closed__60_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__60);
v___x_1147_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1147_, 0, v_a_1142_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*2, v___x_970_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*2 + 1, v___x_970_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1147_);
v___x_1149_ = v___x_1144_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1141_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1141_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v___x_1160_; 
lean_dec_ref(v___x_968_);
lean_del_object(v___x_966_);
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
v___x_1160_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_544_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1165_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__63, &l_Lean_Meta_Sym_Simp_nnf___closed__63_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__63);
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1167_, 0, v_a_1161_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*2, v___x_1166_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*2 + 1, v___x_1166_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1167_);
v___x_1169_ = v___x_1163_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1160_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1160_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_arg_629_);
lean_del_object(v___x_625_);
v_a_1181_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_963_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_963_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
v___jp_630_:
{
if (lean_obj_tag(v_arg_629_) == 7)
{
lean_object* v_binderName_640_; lean_object* v_binderType_641_; lean_object* v_body_642_; uint8_t v_binderInfo_643_; uint8_t v___x_644_; 
v_binderName_640_ = lean_ctor_get(v_arg_629_, 0);
lean_inc(v_binderName_640_);
v_binderType_641_ = lean_ctor_get(v_arg_629_, 1);
lean_inc_ref(v_binderType_641_);
v_body_642_ = lean_ctor_get(v_arg_629_, 2);
lean_inc_ref(v_body_642_);
v_binderInfo_643_ = lean_ctor_get_uint8(v_arg_629_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_629_, 3);
v___x_644_ = l_Lean_Expr_hasLooseBVars(v_body_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec_ref(v_body_642_);
lean_dec_ref(v_binderType_641_);
lean_dec(v_binderName_640_);
v___x_645_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_645_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_645_, 1, v___x_644_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_645_);
v___x_647_ = v___x_625_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_625_);
lean_inc_ref(v_body_642_);
lean_inc_ref(v_binderType_641_);
lean_inc(v_binderName_640_);
v___x_649_ = l_Lean_mkLambda(v_binderName_640_, v_binderInfo_643_, v_binderType_641_, v_body_642_);
v___x_650_ = l_Lean_Meta_Sym_mkNotS(v_body_642_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
lean_inc_ref(v_binderType_641_);
v___x_652_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_nnf_spec__0___redArg(v_binderName_640_, v_binderInfo_643_, v_binderType_641_, v_a_651_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
lean_inc_ref(v_binderType_641_);
v___x_654_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_641_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_n(v_a_655_, 2);
lean_dec_ref_known(v___x_654_, 1);
lean_inc_ref(v_binderType_641_);
v___x_656_ = l_Lean_Meta_Sym_mkExistsS(v_a_655_, v_binderType_641_, v_a_653_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_671_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_671_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_661_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__8));
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v_a_655_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_mkConst(v___x_661_, v___x_663_);
v___x_665_ = l_Lean_mkAppB(v___x_664_, v_binderType_641_, v___x_649_);
v___x_666_ = 0;
v___x_667_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_667_, 0, v_a_657_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*2, v___x_666_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*2 + 1, v___x_666_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_667_);
v___x_669_ = v___x_659_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v_a_655_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v_binderType_641_);
v_a_672_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_656_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_656_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_a_653_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v_binderType_641_);
v_a_680_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_654_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_654_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_binderType_641_);
v_a_688_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_652_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_652_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_binderType_641_);
lean_dec(v_binderName_640_);
v_a_696_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_650_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_650_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_706_; 
lean_dec_ref(v_arg_629_);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__5));
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_704_);
v___x_706_ = v___x_625_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_e_540_);
v_a_1190_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_622_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_622_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_553_, 0, v_a_552_);
lean_ctor_set_uint8(v___x_553_, 1, v_a_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
v___jp_555_:
{
if (lean_obj_tag(v_e_540_) == 7)
{
lean_object* v_binderType_562_; lean_object* v_body_563_; uint8_t v___x_564_; 
v_binderType_562_ = lean_ctor_get(v_e_540_, 1);
lean_inc_ref(v_binderType_562_);
v_body_563_ = lean_ctor_get(v_e_540_, 2);
lean_inc_ref(v_body_563_);
lean_dec_ref_known(v_e_540_, 3);
v___x_564_ = l_Lean_Expr_hasLooseBVars(v_body_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_inc_ref(v_binderType_562_);
v___x_565_ = l_Lean_Meta_isProp(v_binderType_562_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; uint8_t v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_unbox(v_a_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v___x_568_ = lean_unbox(v_a_566_);
lean_dec(v_a_566_);
v_a_552_ = v___x_568_;
goto v___jp_551_;
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_566_);
lean_inc_ref(v_body_563_);
v___x_569_ = l_Lean_Meta_isProp(v_body_563_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_unbox(v_a_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v___x_572_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
v_a_552_ = v___x_572_;
goto v___jp_551_;
}
else
{
lean_object* v___x_573_; 
lean_dec(v_a_570_);
lean_inc_ref(v_binderType_562_);
v___x_573_ = l_Lean_Meta_Sym_mkNotS(v_binderType_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
lean_inc_ref(v_body_563_);
v___x_575_ = l_Lean_Meta_Sym_mkOrS(v_a_574_, v_body_563_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_580_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_nnf___closed__4, &l_Lean_Meta_Sym_Simp_nnf___closed__4_once, _init_l_Lean_Meta_Sym_Simp_nnf___closed__4);
v___x_581_ = l_Lean_mkAppB(v___x_580_, v_binderType_562_, v_body_563_);
v___x_582_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_582_, 0, v_a_576_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*2, v___x_564_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*2 + 1, v___x_564_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v_a_587_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_575_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_575_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v_a_595_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_573_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_573_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v_a_603_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_569_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_569_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v_a_611_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_565_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_565_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
uint8_t v___x_619_; 
lean_dec_ref(v_body_563_);
lean_dec_ref(v_binderType_562_);
v___x_619_ = 0;
v_a_552_ = v___x_619_;
goto v___jp_551_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_e_540_);
v___x_620_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_nnf___closed__5));
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_nnf___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_Sym_Simp_nnf(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3(lean_object* v_f_1210_, lean_object* v_a_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___redArg(v_f_1210_, v_a_1211_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3___boxed(lean_object* v_f_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Simp_nnf_spec__2_spec__3(v_f_1223_, v_a_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
return v_res_1235_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_NNF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_NNF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_NNF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_NNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_NNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_NNF(builtin);
}
#ifdef __cplusplus
}
#endif
