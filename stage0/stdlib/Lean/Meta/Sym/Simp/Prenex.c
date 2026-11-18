// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Prenex
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Util import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.SynthInstance import Init.Sym.Lemmas
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkAndS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkOrS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_mkExistsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "forall_and_forall_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 13, 103, 95, 21, 122, 58, 227)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "and_forall_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__4_value),LEAN_SCALAR_PTR_LITERAL(36, 172, 61, 141, 8, 129, 196, 171)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "forall_and_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 166, 170, 16, 44, 93, 62, 234)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__9_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__10_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__11_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__12_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_or_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__13_value),LEAN_SCALAR_PTR_LITERAL(242, 206, 182, 190, 146, 92, 103, 33)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__14_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "or_forall_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__15_value),LEAN_SCALAR_PTR_LITERAL(122, 37, 30, 223, 229, 251, 153, 12)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__16_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__17_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__18_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "exists_or_exists_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__19_value),LEAN_SCALAR_PTR_LITERAL(224, 71, 207, 181, 43, 97, 114, 221)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__20_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "or_exists_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__21_value),LEAN_SCALAR_PTR_LITERAL(26, 6, 136, 197, 141, 230, 130, 72)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__22_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "exists_or_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__24_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__23_value),LEAN_SCALAR_PTR_LITERAL(157, 130, 6, 245, 143, 255, 150, 25)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__24_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "exists_and_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__25_value),LEAN_SCALAR_PTR_LITERAL(61, 88, 124, 21, 166, 60, 66, 142)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__26_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_minscope___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "and_exists_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_minscope___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__27_value),LEAN_SCALAR_PTR_LITERAL(68, 181, 148, 151, 123, 45, 23, 181)}};
static const lean_object* l_Lean_Meta_Sym_Simp_minscope___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_minscope___closed__28_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg(lean_object* v_declName_1_, lean_object* v_us_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_Expr_const___override(v_declName_1_, v_us_2_);
v___x_6_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_5_, v___y_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg___boxed(lean_object* v_declName_7_, lean_object* v_us_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg(v_declName_7_, v_us_8_, v___y_9_);
lean_dec(v___y_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0(lean_object* v_declName_12_, lean_object* v_us_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg(v_declName_12_, v_us_13_, v___y_15_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___boxed(lean_object* v_declName_22_, lean_object* v_us_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0(v_declName_22_, v_us_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1(lean_object* v_f_32_, lean_object* v_a_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___y_42_; lean_object* v___x_45_; uint8_t v_debug_46_; 
v___x_45_ = lean_st_ref_get(v___y_35_);
v_debug_46_ = lean_ctor_get_uint8(v___x_45_, sizeof(void*)*13);
lean_dec(v___x_45_);
if (v_debug_46_ == 0)
{
v___y_42_ = v___y_35_;
goto v___jp_41_;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_32_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v___x_48_; 
lean_dec_ref_known(v___x_47_, 1);
v___x_48_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_dec_ref_known(v___x_48_, 1);
v___y_42_ = v___y_35_;
goto v___jp_41_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
lean_dec_ref(v_a_33_);
lean_dec_ref(v_f_32_);
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
lean_dec_ref(v_a_33_);
lean_dec_ref(v_f_32_);
v_a_57_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_47_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_47_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
v___jp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Lean_Expr_app___override(v_f_32_, v_a_33_);
v___x_44_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_43_, v___y_42_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1___boxed(lean_object* v_f_65_, lean_object* v_a_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1(v_f_65_, v_a_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(lean_object* v_00_u03b1_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; 
lean_inc_ref(v_00_u03b1_78_);
v___x_86_ = l_Lean_Meta_Sym_getLevel___redArg(v_00_u03b1_78_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___closed__1));
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v_a_87_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__0___redArg(v___x_88_, v___x_90_, v_a_80_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_93_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f_spec__1(v_a_92_, v_00_u03b1_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_94_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
return v___x_95_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_93_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_93_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec_ref(v_00_u03b1_78_);
v_a_104_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_91_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_91_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v_00_u03b1_78_);
v_a_112_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_86_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_86_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f___boxed(lean_object* v_00_u03b1_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_00_u03b1_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = l_Lean_Level_ofNat(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3, &l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__3);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4, &l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__4);
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__2));
v___x_141_ = l_Lean_mkConst(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Lean_Level_ofNat(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6, &l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__6);
v___x_145_ = l_Lean_mkSort(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(lean_object* v_lhs_146_, lean_object* v_rhs_147_, lean_object* v_h_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5, &l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__5);
v___x_150_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7, &l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm___closed__7);
v___x_151_ = l_Lean_mkApp4(v___x_149_, v___x_150_, v_rhs_147_, v_lhs_146_, v_h_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(lean_object* v_x_152_, uint8_t v_bi_153_, lean_object* v_t_154_, lean_object* v_b_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___y_164_; lean_object* v___x_167_; uint8_t v_debug_168_; 
v___x_167_ = lean_st_ref_get(v___y_157_);
v_debug_168_ = lean_ctor_get_uint8(v___x_167_, sizeof(void*)*13);
lean_dec(v___x_167_);
if (v_debug_168_ == 0)
{
v___y_164_ = v___y_157_;
goto v___jp_163_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_154_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref_known(v___x_169_, 1);
v___x_170_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_dec_ref_known(v___x_170_, 1);
v___y_164_ = v___y_157_;
goto v___jp_163_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v_b_155_);
lean_dec_ref(v_t_154_);
lean_dec(v_x_152_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_b_155_);
lean_dec_ref(v_t_154_);
lean_dec(v_x_152_);
v_a_179_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_169_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Lean_Expr_forallE___override(v_x_152_, v_t_154_, v_b_155_, v_bi_153_);
v___x_166_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_165_, v___y_164_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg___boxed(lean_object* v_x_187_, lean_object* v_bi_188_, lean_object* v_t_189_, lean_object* v_b_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
uint8_t v_bi_boxed_198_; lean_object* v_res_199_; 
v_bi_boxed_198_ = lean_unbox(v_bi_188_);
v_res_199_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_x_187_, v_bi_boxed_198_, v_t_189_, v_b_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0(lean_object* v_x_200_, uint8_t v_bi_201_, lean_object* v_t_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_x_200_, v_bi_201_, v_t_202_, v_b_203_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___boxed(lean_object* v_x_215_, lean_object* v_bi_216_, lean_object* v_t_217_, lean_object* v_b_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
uint8_t v_bi_boxed_229_; lean_object* v_res_230_; 
v_bi_boxed_229_ = lean_unbox(v_bi_216_);
v_res_230_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0(v_x_215_, v_bi_boxed_229_, v_t_217_, v_b_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(lean_object* v_x_231_, uint8_t v_bi_232_, lean_object* v_t_233_, lean_object* v_b_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___y_243_; lean_object* v___x_246_; uint8_t v_debug_247_; 
v___x_246_ = lean_st_ref_get(v___y_236_);
v_debug_247_ = lean_ctor_get_uint8(v___x_246_, sizeof(void*)*13);
lean_dec(v___x_246_);
if (v_debug_247_ == 0)
{
v___y_243_ = v___y_236_;
goto v___jp_242_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_233_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_249_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_dec_ref_known(v___x_249_, 1);
v___y_243_ = v___y_236_;
goto v___jp_242_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v_b_234_);
lean_dec_ref(v_t_233_);
lean_dec(v_x_231_);
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v_b_234_);
lean_dec_ref(v_t_233_);
lean_dec(v_x_231_);
v_a_258_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_248_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_248_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = l_Lean_Expr_lam___override(v_x_231_, v_t_233_, v_b_234_, v_bi_232_);
v___x_245_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_244_, v___y_243_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1___boxed(lean_object* v_x_266_, lean_object* v_bi_267_, lean_object* v_t_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
uint8_t v_bi_boxed_277_; lean_object* v_res_278_; 
v_bi_boxed_277_ = lean_unbox(v_bi_267_);
v_res_278_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(v_x_266_, v_bi_boxed_277_, v_t_268_, v_b_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___lam__0(lean_object* v_binderName_279_, uint8_t v_binderInfo_280_, lean_object* v_binderType_281_, lean_object* v_a_282_, lean_object* v_p_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
lean_inc_ref(v_binderType_281_);
v___x_291_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(v_binderName_279_, v_binderInfo_280_, v_binderType_281_, v_p_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = l_Lean_Meta_Sym_mkExistsS(v_a_282_, v_binderType_281_, v_a_292_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
return v___x_293_;
}
else
{
lean_dec(v_a_282_);
lean_dec_ref(v_binderType_281_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___lam__0___boxed(lean_object* v_binderName_294_, lean_object* v_binderInfo_295_, lean_object* v_binderType_296_, lean_object* v_a_297_, lean_object* v_p_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_binderInfo_67919__boxed_306_; lean_object* v_res_307_; 
v_binderInfo_67919__boxed_306_ = lean_unbox(v_binderInfo_295_);
v_res_307_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_294_, v_binderInfo_67919__boxed_306_, v_binderType_296_, v_a_297_, v_p_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope(lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___y_383_; lean_object* v___y_384_; uint8_t v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; uint8_t v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_694_; 
lean_inc_ref(v_e_371_);
v___x_694_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_371_, v_a_378_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_967_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_967_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_967_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_967_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = l_Lean_Expr_cleanupAnnotations(v_a_695_);
lean_dec(v_a_695_);
v___x_700_ = l_Lean_Expr_isApp(v___x_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v___x_699_);
lean_del_object(v___x_697_);
v___y_562_ = v_a_375_;
v___y_563_ = v_a_376_;
v___y_564_ = v_a_377_;
v___y_565_ = v_a_378_;
v___y_566_ = v_a_379_;
v___y_567_ = v_a_380_;
goto v___jp_561_;
}
else
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_699_);
v___x_702_ = l_Lean_Expr_isApp(v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_del_object(v___x_697_);
v___y_562_ = v_a_375_;
v___y_563_ = v_a_376_;
v___y_564_ = v_a_377_;
v___y_565_ = v_a_378_;
v___y_566_ = v_a_379_;
v___y_567_ = v_a_380_;
goto v___jp_561_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
lean_dec_ref(v___x_701_);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__18));
v___x_705_ = l_Lean_Expr_isConstOf(v___x_703_, v___x_704_);
lean_dec_ref(v___x_703_);
if (v___x_705_ == 0)
{
lean_dec_ref(v___x_699_);
lean_del_object(v___x_697_);
v___y_562_ = v_a_375_;
v___y_563_ = v_a_376_;
v___y_564_ = v_a_377_;
v___y_565_ = v_a_378_;
v___y_566_ = v_a_379_;
v___y_567_ = v_a_380_;
goto v___jp_561_;
}
else
{
lean_object* v_arg_706_; 
v_arg_706_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref(v_arg_706_);
lean_dec_ref(v___x_699_);
if (lean_obj_tag(v_arg_706_) == 6)
{
lean_object* v_binderName_707_; lean_object* v_binderType_708_; lean_object* v_body_709_; uint8_t v_binderInfo_710_; lean_object* v___x_711_; 
lean_del_object(v___x_697_);
v_binderName_707_ = lean_ctor_get(v_arg_706_, 0);
lean_inc(v_binderName_707_);
v_binderType_708_ = lean_ctor_get(v_arg_706_, 1);
lean_inc_ref_n(v_binderType_708_, 2);
v_body_709_ = lean_ctor_get(v_arg_706_, 2);
lean_inc_ref(v_body_709_);
v_binderInfo_710_ = lean_ctor_get_uint8(v_arg_706_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_706_, 3);
v___x_711_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_708_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_709_, v_a_378_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_946_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_946_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_946_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_946_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_cleanupAnnotations(v_a_714_);
lean_dec(v_a_714_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_dec_ref(v___x_718_);
lean_del_object(v___x_716_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
goto v___jp_691_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_720_);
lean_dec_ref(v___x_718_);
lean_del_object(v___x_716_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
goto v___jp_691_;
}
else
{
lean_object* v_arg_722_; lean_object* v_arg_723_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_779_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_arg_722_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_722_);
lean_dec_ref(v___x_718_);
v_arg_723_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_arg_723_);
v___x_863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
lean_dec_ref(v___x_720_);
v___x_864_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__10));
v___x_865_ = l_Lean_Expr_isConstOf(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__12));
v___x_867_ = l_Lean_Expr_isConstOf(v___x_863_, v___x_866_);
lean_dec_ref(v___x_863_);
if (v___x_867_ == 0)
{
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_722_);
lean_del_object(v___x_716_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
goto v___jp_691_;
}
else
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Expr_hasLooseBVars(v_arg_722_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_del_object(v___x_716_);
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
v___x_869_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_723_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_n(v_a_870_, 2);
lean_dec_ref_known(v___x_869_, 1);
lean_inc_ref(v_arg_722_);
v___x_871_ = l_Lean_Meta_Sym_mkAndS(v_a_870_, v_arg_722_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_887_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_876_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__26));
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v_a_712_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_mkConst(v___x_876_, v___x_878_);
v___x_880_ = l_Lean_Expr_appArg_x21(v_a_870_);
lean_dec(v_a_870_);
v___x_881_ = l_Lean_mkApp3(v___x_879_, v_binderType_708_, v___x_880_, v_arg_722_);
lean_inc(v_a_872_);
v___x_882_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_872_, v___x_881_);
v___x_883_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_883_, 0, v_a_872_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*2, v___x_865_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*2 + 1, v___x_865_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_883_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_870_);
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_888_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_871_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_871_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_896_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_869_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_869_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Expr_hasLooseBVars(v_arg_723_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_del_object(v___x_716_);
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
v___x_905_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_722_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_n(v_a_906_, 2);
lean_dec_ref_known(v___x_905_, 1);
lean_inc_ref(v_arg_723_);
v___x_907_ = l_Lean_Meta_Sym_mkAndS(v_arg_723_, v_a_906_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_923_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_923_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_923_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_923_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__28));
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_914_, 0, v_a_712_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_mkConst(v___x_912_, v___x_914_);
v___x_916_ = l_Lean_Expr_appArg_x21(v_a_906_);
lean_dec(v_a_906_);
v___x_917_ = l_Lean_mkApp3(v___x_915_, v_binderType_708_, v_arg_723_, v___x_916_);
lean_inc(v_a_908_);
v___x_918_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_908_, v___x_917_);
v___x_919_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_919_, 0, v_a_908_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*2, v___x_865_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*2 + 1, v___x_865_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_919_);
v___x_921_ = v___x_910_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_906_);
lean_dec_ref(v_arg_723_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_924_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_907_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_907_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_arg_723_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_932_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_905_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_905_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
v___x_940_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_940_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_940_, 1, v___x_865_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_940_);
v___x_942_ = v___x_716_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
uint8_t v___x_944_; 
lean_dec_ref(v___x_863_);
lean_del_object(v___x_716_);
v___x_944_ = l_Lean_Expr_hasLooseBVars(v_arg_722_);
if (v___x_944_ == 0)
{
v___y_779_ = v___x_865_;
goto v___jp_778_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Expr_hasLooseBVars(v_arg_723_);
if (v___x_945_ == 0)
{
v___y_779_ = v___x_945_;
goto v___jp_778_;
}
else
{
v___y_725_ = v_a_375_;
v___y_726_ = v_a_376_;
v___y_727_ = v_a_377_;
v___y_728_ = v_a_378_;
v___y_729_ = v_a_379_;
v___y_730_ = v_a_380_;
goto v___jp_724_;
}
}
}
v___jp_724_:
{
lean_object* v___x_731_; 
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
lean_inc(v_binderName_707_);
v___x_731_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_723_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
v___x_733_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_722_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
lean_inc(v_a_732_);
v___x_735_ = l_Lean_Meta_Sym_mkOrS(v_a_732_, v_a_734_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_753_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_753_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_753_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_753_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_740_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__20));
v___x_741_ = lean_box(0);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_712_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_mkConst(v___x_740_, v___x_742_);
v___x_744_ = l_Lean_Expr_appArg_x21(v_a_732_);
lean_dec(v_a_732_);
v___x_745_ = l_Lean_Expr_appArg_x21(v_a_734_);
lean_dec(v_a_734_);
v___x_746_ = l_Lean_mkApp3(v___x_743_, v_binderType_708_, v___x_744_, v___x_745_);
lean_inc(v_a_736_);
v___x_747_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_736_, v___x_746_);
v___x_748_ = 0;
v___x_749_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_749_, 0, v_a_736_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*2, v___x_748_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*2 + 1, v___x_748_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_749_);
v___x_751_ = v___x_738_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_734_);
lean_dec(v_a_732_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_754_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_735_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_735_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_732_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_762_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_733_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_733_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
v_a_770_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_731_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_731_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
v___jp_778_:
{
lean_object* v___x_780_; 
lean_inc_ref(v_binderType_708_);
v___x_780_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_binderType_708_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
if (lean_obj_tag(v_a_781_) == 1)
{
if (v___y_779_ == 0)
{
lean_object* v_val_782_; lean_object* v___x_783_; 
v_val_782_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v_a_781_, 1);
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
v___x_783_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_722_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc_n(v_a_784_, 2);
lean_dec_ref_known(v___x_783_, 1);
lean_inc_ref(v_arg_723_);
v___x_785_ = l_Lean_Meta_Sym_mkOrS(v_arg_723_, v_a_784_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_801_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_801_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_790_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__22));
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v_a_712_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_mkConst(v___x_790_, v___x_792_);
v___x_794_ = l_Lean_Expr_appArg_x21(v_a_784_);
lean_dec(v_a_784_);
v___x_795_ = l_Lean_mkApp4(v___x_793_, v_binderType_708_, v_val_782_, v_arg_723_, v___x_794_);
lean_inc(v_a_786_);
v___x_796_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_786_, v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_797_, 0, v_a_786_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*2, v___y_779_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*2 + 1, v___y_779_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_797_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_a_784_);
lean_dec(v_val_782_);
lean_dec_ref(v_arg_723_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_802_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_785_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_785_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_val_782_);
lean_dec_ref(v_arg_723_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_810_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_783_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_783_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_val_818_; lean_object* v___x_819_; 
v_val_818_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_a_781_, 1);
lean_inc(v_a_712_);
lean_inc_ref(v_binderType_708_);
v___x_819_ = l_Lean_Meta_Sym_Simp_minscope___lam__0(v_binderName_707_, v_binderInfo_710_, v_binderType_708_, v_a_712_, v_arg_723_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_n(v_a_820_, 2);
lean_dec_ref_known(v___x_819_, 1);
lean_inc_ref(v_arg_722_);
v___x_821_ = l_Lean_Meta_Sym_mkOrS(v_a_820_, v_arg_722_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_838_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_838_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_838_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_838_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_826_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__24));
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_712_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_mkConst(v___x_826_, v___x_828_);
v___x_830_ = l_Lean_Expr_appArg_x21(v_a_820_);
lean_dec(v_a_820_);
v___x_831_ = l_Lean_mkApp4(v___x_829_, v_binderType_708_, v_val_818_, v___x_830_, v_arg_722_);
lean_inc(v_a_822_);
v___x_832_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_822_, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_834_, 0, v_a_822_);
lean_ctor_set(v___x_834_, 1, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2, v___x_833_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2 + 1, v___x_833_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_834_);
v___x_836_ = v___x_824_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_820_);
lean_dec(v_val_818_);
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_839_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_821_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_821_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_val_818_);
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec_ref(v_e_371_);
v_a_847_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_819_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_819_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_dec(v_a_781_);
v___y_725_ = v_a_375_;
v___y_726_ = v_a_376_;
v___y_727_ = v_a_377_;
v___y_728_ = v_a_378_;
v___y_729_ = v_a_379_;
v___y_730_ = v_a_380_;
goto v___jp_724_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_722_);
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
v_a_855_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_780_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_780_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
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
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_a_712_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
v_a_947_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_713_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_713_);
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
lean_dec_ref(v_body_709_);
lean_dec_ref(v_binderType_708_);
lean_dec(v_binderName_707_);
lean_dec_ref(v_e_371_);
v_a_955_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_711_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_711_);
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
else
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_e_371_);
v___x_963_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_963_);
v___x_965_ = v___x_697_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v_e_371_);
v_a_968_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_694_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_694_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
v___jp_382_:
{
lean_object* v___x_396_; 
lean_inc_ref(v___y_384_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_386_);
v___x_396_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v___y_386_, v___y_385_, v___y_388_, v___y_384_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
lean_inc_ref(v___y_383_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_386_);
v___x_398_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v___y_386_, v___y_385_, v___y_388_, v___y_383_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Meta_Sym_mkAndS(v_a_397_, v_a_399_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_417_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_417_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_417_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_417_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__3));
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_387_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_mkConst(v___x_405_, v___x_407_);
lean_inc_ref_n(v___y_388_, 2);
lean_inc(v___y_386_);
v___x_409_ = l_Lean_mkLambda(v___y_386_, v___y_385_, v___y_388_, v___y_384_);
v___x_410_ = l_Lean_mkLambda(v___y_386_, v___y_385_, v___y_388_, v___y_383_);
v___x_411_ = l_Lean_mkApp3(v___x_408_, v___y_388_, v___x_409_, v___x_410_);
lean_inc(v_a_401_);
v___x_412_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_401_, v___x_411_);
v___x_413_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_413_, 0, v_a_401_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*2, v___y_389_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*2 + 1, v___y_389_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_413_);
v___x_415_ = v___x_403_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec_ref(v_e_371_);
v_a_418_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_400_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_400_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_a_397_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec_ref(v_e_371_);
v_a_426_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_398_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_398_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec_ref(v_e_371_);
v_a_434_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_396_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_396_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_457_; 
lean_inc_ref(v___y_454_);
v___x_457_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v___y_454_, v___y_455_, v___y_444_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
if (lean_obj_tag(v_a_458_) == 1)
{
if (v___y_453_ == 0)
{
lean_object* v_val_459_; lean_object* v___x_460_; 
v_val_459_ = lean_ctor_get(v_a_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v_a_458_, 1);
lean_inc_ref(v___y_443_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_447_);
v___x_460_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v___y_447_, v___y_452_, v___y_454_, v___y_443_, v___y_455_, v___y_444_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
lean_inc_ref(v___y_446_);
v___x_462_ = l_Lean_Meta_Sym_mkAndS(v___y_446_, v_a_461_, v___y_455_, v___y_444_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_478_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_478_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_478_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_478_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__5));
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___y_448_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_mkConst(v___x_467_, v___x_469_);
lean_inc_ref(v___y_454_);
v___x_471_ = l_Lean_mkLambda(v___y_447_, v___y_452_, v___y_454_, v___y_443_);
v___x_472_ = l_Lean_mkApp4(v___x_470_, v___y_454_, v_val_459_, v___y_446_, v___x_471_);
lean_inc(v_a_463_);
v___x_473_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_463_, v___x_472_);
v___x_474_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_474_, 0, v_a_463_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*2, v___y_453_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*2 + 1, v___y_453_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_474_);
v___x_476_ = v___x_465_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_val_459_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_479_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_462_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_462_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_val_459_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_487_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_460_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_460_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
v_val_495_ = lean_ctor_get(v_a_458_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_a_458_, 1);
lean_inc_ref(v___y_446_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_447_);
v___x_496_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v___y_447_, v___y_452_, v___y_454_, v___y_446_, v___y_455_, v___y_444_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
lean_inc_ref(v___y_443_);
v___x_498_ = l_Lean_Meta_Sym_mkAndS(v_a_497_, v___y_443_, v___y_455_, v___y_444_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_514_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_514_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_514_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_514_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_503_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__7));
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_505_, 0, v___y_448_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_mkConst(v___x_503_, v___x_505_);
lean_inc_ref(v___y_454_);
v___x_507_ = l_Lean_mkLambda(v___y_447_, v___y_452_, v___y_454_, v___y_446_);
v___x_508_ = l_Lean_mkApp4(v___x_506_, v___y_454_, v_val_495_, v___x_507_, v___y_443_);
lean_inc(v_a_499_);
v___x_509_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_499_, v___x_508_);
v___x_510_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_510_, 0, v_a_499_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2, v___y_456_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2 + 1, v___y_456_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_510_);
v___x_512_ = v___x_501_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_val_495_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_515_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_498_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_498_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_val_495_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_523_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_496_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_496_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v_a_458_);
lean_inc_ref(v___y_454_);
v___x_531_ = l_Lean_Meta_isProp(v___y_454_, v___y_449_, v___y_450_, v___y_451_, v___y_445_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; 
v___x_536_ = lean_unbox(v_a_532_);
lean_dec(v_a_532_);
if (v___x_536_ == 0)
{
lean_del_object(v___x_534_);
v___y_383_ = v___y_443_;
v___y_384_ = v___y_446_;
v___y_385_ = v___y_452_;
v___y_386_ = v___y_447_;
v___y_387_ = v___y_448_;
v___y_388_ = v___y_454_;
v___y_389_ = v___y_456_;
v___y_390_ = v___y_455_;
v___y_391_ = v___y_444_;
v___y_392_ = v___y_449_;
v___y_393_ = v___y_450_;
v___y_394_ = v___y_451_;
v___y_395_ = v___y_445_;
goto v___jp_382_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v___x_537_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_537_, 0, v___y_456_);
lean_ctor_set_uint8(v___x_537_, 1, v___y_456_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_542_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_531_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___y_454_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_e_371_);
v_a_550_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_457_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_457_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
v___jp_561_:
{
if (lean_obj_tag(v_e_371_) == 7)
{
lean_object* v_binderName_568_; lean_object* v_binderType_569_; lean_object* v_body_570_; uint8_t v_binderInfo_571_; uint8_t v___x_572_; 
v_binderName_568_ = lean_ctor_get(v_e_371_, 0);
v_binderType_569_ = lean_ctor_get(v_e_371_, 1);
v_body_570_ = lean_ctor_get(v_e_371_, 2);
v_binderInfo_571_ = lean_ctor_get_uint8(v_e_371_, sizeof(void*)*3 + 8);
v___x_572_ = l_Lean_Expr_hasLooseBVars(v_body_570_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v_e_371_, 3);
v___x_573_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_573_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; 
lean_inc_ref(v_binderType_569_);
v___x_575_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_569_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
lean_inc_ref(v_body_570_);
v___x_577_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_570_, v___y_565_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_672_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_672_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_672_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_672_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = l_Lean_Expr_cleanupAnnotations(v_a_578_);
lean_dec(v_a_578_);
v___x_583_ = l_Lean_Expr_isApp(v___x_582_);
if (v___x_583_ == 0)
{
lean_dec_ref(v___x_582_);
lean_del_object(v___x_580_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
goto v___jp_558_;
}
else
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_582_);
v___x_585_ = l_Lean_Expr_isApp(v___x_584_);
if (v___x_585_ == 0)
{
lean_dec_ref(v___x_584_);
lean_dec_ref(v___x_582_);
lean_del_object(v___x_580_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
goto v___jp_558_;
}
else
{
lean_object* v_arg_586_; lean_object* v_arg_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_arg_586_ = lean_ctor_get(v___x_582_, 1);
lean_inc_ref(v_arg_586_);
lean_dec_ref(v___x_582_);
v_arg_587_ = lean_ctor_get(v___x_584_, 1);
lean_inc_ref(v_arg_587_);
v___x_588_ = l_Lean_Expr_appFnCleanup___redArg(v___x_584_);
lean_dec_ref(v___x_584_);
v___x_589_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__10));
v___x_590_ = l_Lean_Expr_isConstOf(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
lean_del_object(v___x_580_);
v___x_591_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__12));
v___x_592_ = l_Lean_Expr_isConstOf(v___x_588_, v___x_591_);
lean_dec_ref(v___x_588_);
if (v___x_592_ == 0)
{
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
goto v___jp_558_;
}
else
{
uint8_t v___x_593_; 
v___x_593_ = l_Lean_Expr_hasLooseBVars(v_arg_586_);
if (v___x_593_ == 0)
{
lean_inc_ref(v_binderType_569_);
lean_inc(v_binderName_568_);
v___y_443_ = v_arg_586_;
v___y_444_ = v___y_563_;
v___y_445_ = v___y_567_;
v___y_446_ = v_arg_587_;
v___y_447_ = v_binderName_568_;
v___y_448_ = v_a_576_;
v___y_449_ = v___y_564_;
v___y_450_ = v___y_565_;
v___y_451_ = v___y_566_;
v___y_452_ = v_binderInfo_571_;
v___y_453_ = v___x_572_;
v___y_454_ = v_binderType_569_;
v___y_455_ = v___y_562_;
v___y_456_ = v___x_590_;
goto v___jp_442_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Expr_hasLooseBVars(v_arg_587_);
if (v___x_594_ == 0)
{
lean_inc_ref(v_binderType_569_);
lean_inc(v_binderName_568_);
v___y_443_ = v_arg_586_;
v___y_444_ = v___y_563_;
v___y_445_ = v___y_567_;
v___y_446_ = v_arg_587_;
v___y_447_ = v_binderName_568_;
v___y_448_ = v_a_576_;
v___y_449_ = v___y_564_;
v___y_450_ = v___y_565_;
v___y_451_ = v___y_566_;
v___y_452_ = v_binderInfo_571_;
v___y_453_ = v___x_590_;
v___y_454_ = v_binderType_569_;
v___y_455_ = v___y_562_;
v___y_456_ = v___x_590_;
goto v___jp_442_;
}
else
{
lean_inc_ref(v_binderType_569_);
lean_inc(v_binderName_568_);
v___y_383_ = v_arg_586_;
v___y_384_ = v_arg_587_;
v___y_385_ = v_binderInfo_571_;
v___y_386_ = v_binderName_568_;
v___y_387_ = v_a_576_;
v___y_388_ = v_binderType_569_;
v___y_389_ = v___x_590_;
v___y_390_ = v___y_562_;
v___y_391_ = v___y_563_;
v___y_392_ = v___y_564_;
v___y_393_ = v___y_565_;
v___y_394_ = v___y_566_;
v___y_395_ = v___y_567_;
goto v___jp_382_;
}
}
}
}
else
{
uint8_t v___x_595_; 
lean_dec_ref(v___x_588_);
v___x_595_ = l_Lean_Expr_hasLooseBVars(v_arg_586_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_del_object(v___x_580_);
lean_inc_ref(v_arg_587_);
lean_inc_ref(v_binderType_569_);
lean_inc(v_binderName_568_);
v___x_596_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_binderName_568_, v_binderInfo_571_, v_binderType_569_, v_arg_587_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
lean_inc_ref(v_arg_586_);
v___x_598_ = l_Lean_Meta_Sym_mkOrS(v_a_597_, v_arg_586_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_614_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_614_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_614_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_614_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_603_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__14));
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v_a_576_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_mkConst(v___x_603_, v___x_605_);
lean_inc_ref_n(v_binderType_569_, 2);
lean_inc(v_binderName_568_);
v___x_607_ = l_Lean_mkLambda(v_binderName_568_, v_binderInfo_571_, v_binderType_569_, v_arg_587_);
v___x_608_ = l_Lean_mkApp3(v___x_606_, v_binderType_569_, v___x_607_, v_arg_586_);
lean_inc(v_a_599_);
v___x_609_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_599_, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_610_, 0, v_a_599_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*2, v___x_595_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*2 + 1, v___x_595_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_610_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v_a_615_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_598_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_598_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v_a_623_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_596_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_596_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
uint8_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 0;
v___x_632_ = l_Lean_Expr_hasLooseBVars(v_arg_587_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_del_object(v___x_580_);
lean_inc_ref(v_arg_586_);
lean_inc_ref(v_binderType_569_);
lean_inc(v_binderName_568_);
v___x_633_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_binderName_568_, v_binderInfo_571_, v_binderType_569_, v_arg_586_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
lean_inc_ref(v_arg_587_);
v___x_635_ = l_Lean_Meta_Sym_mkOrS(v_arg_587_, v_a_634_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_651_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_651_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_651_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_651_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_640_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__16));
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_576_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_mkConst(v___x_640_, v___x_642_);
lean_inc_ref_n(v_binderType_569_, 2);
lean_inc(v_binderName_568_);
v___x_644_ = l_Lean_mkLambda(v_binderName_568_, v_binderInfo_571_, v_binderType_569_, v_arg_586_);
v___x_645_ = l_Lean_mkApp3(v___x_643_, v_binderType_569_, v_arg_587_, v___x_644_);
lean_inc(v_a_636_);
v___x_646_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_mkPropEqSymm(v_e_371_, v_a_636_, v___x_645_);
v___x_647_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_647_, 0, v_a_636_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*2, v___x_631_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*2 + 1, v___x_631_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_647_);
v___x_649_ = v___x_638_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v_a_652_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_635_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_635_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v_a_660_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_633_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_633_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_586_);
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_668_);
v___x_670_ = v___x_580_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
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
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_a_576_);
lean_dec_ref_known(v_e_371_, 3);
v_a_673_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_577_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_577_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref_known(v_e_371_, 3);
v_a_681_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_575_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_575_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_e_371_);
v___x_689_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_minscope___boxed(lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Meta_Sym_Simp_minscope(v_e_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg(lean_object* v_idx_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Lean_Expr_bvar___override(v_idx_988_);
v___x_992_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_991_, v___y_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg___boxed(lean_object* v_idx_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg(v_idx_993_, v___y_994_);
lean_dec(v___y_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0(lean_object* v_idx_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg(v_idx_997_, v___y_999_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___boxed(lean_object* v_idx_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0(v_idx_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(lean_object* v_e_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0_spec__0___redArg(v___x_1023_, v_a_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_mk_empty_array_with_capacity(v___x_1026_);
v___x_1028_ = lean_array_push(v___x_1027_, v_a_1025_);
v___x_1029_ = l_Lean_Meta_Sym_betaS(v_e_1015_, v___x_1028_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1029_;
}
else
{
lean_dec_ref(v_e_1015_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0___boxed(lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_e_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(lean_object* v_e_1039_){
_start:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = l_Lean_Expr_cleanupAnnotations(v_e_1039_);
v___x_1045_ = l_Lean_Expr_isApp(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec_ref(v___x_1044_);
goto v___jp_1041_;
}
else
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1044_);
v___x_1047_ = l_Lean_Expr_isApp(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___x_1044_);
goto v___jp_1041_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1046_);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__18));
v___x_1050_ = l_Lean_Expr_isConstOf(v___x_1048_, v___x_1049_);
lean_dec_ref(v___x_1048_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___x_1044_);
goto v___jp_1041_;
}
else
{
lean_object* v_arg_1051_; lean_object* v_arg_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_arg_1051_ = lean_ctor_get(v___x_1044_, 1);
lean_inc_ref(v_arg_1051_);
lean_dec_ref(v___x_1044_);
v_arg_1052_ = lean_ctor_get(v___x_1046_, 1);
lean_inc_ref(v_arg_1052_);
lean_dec_ref(v___x_1046_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_arg_1052_);
lean_ctor_set(v___x_1053_, 1, v_arg_1051_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg___boxed(lean_object* v_e_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_e_1056_);
lean_dec_ref(v_e_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f(lean_object* v_e_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_e_1059_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___boxed(lean_object* v_e_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f(v_e_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec_ref(v_e_1068_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(lean_object* v_x_1077_, uint8_t v_bi_1078_, lean_object* v_t_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___y_1089_; lean_object* v___x_1092_; uint8_t v_debug_1093_; 
v___x_1092_ = lean_st_ref_get(v___y_1082_);
v_debug_1093_ = lean_ctor_get_uint8(v___x_1092_, sizeof(void*)*13);
lean_dec(v___x_1092_);
if (v_debug_1093_ == 0)
{
v___y_1089_ = v___y_1082_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1079_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref_known(v___x_1094_, 1);
v___x_1095_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
v___y_1089_ = v___y_1082_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_b_1080_);
lean_dec_ref(v_t_1079_);
lean_dec(v_x_1077_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_b_1080_);
lean_dec_ref(v_t_1079_);
lean_dec(v_x_1077_);
v_a_1104_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1094_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1094_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l_Lean_Expr_lam___override(v_x_1077_, v_t_1079_, v_b_1080_, v_bi_1078_);
v___x_1091_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1090_, v___y_1089_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg___boxed(lean_object* v_x_1112_, lean_object* v_bi_1113_, lean_object* v_t_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_bi_boxed_1123_; lean_object* v_res_1124_; 
v_bi_boxed_1123_ = lean_unbox(v_bi_1113_);
v_res_1124_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(v_x_1112_, v_bi_boxed_1123_, v_t_1114_, v_b_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0(lean_object* v_x_1125_, uint8_t v_bi_1126_, lean_object* v_t_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(v_x_1125_, v_bi_1126_, v_t_1127_, v_b_1128_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___boxed(lean_object* v_x_1140_, lean_object* v_bi_1141_, lean_object* v_t_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v_bi_boxed_1154_; lean_object* v_res_1155_; 
v_bi_boxed_1154_ = lean_unbox(v_bi_1141_);
v_res_1155_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0(v_x_1140_, v_bi_boxed_1154_, v_t_1142_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___lam__0(lean_object* v_arg_1156_, lean_object* v_q_u03b1_1157_, lean_object* v_qb_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc_ref(v_q_u03b1_1157_);
v___x_1166_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_q_u03b1_1157_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1242_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1242_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1242_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
if (lean_obj_tag(v_a_1167_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1172_; 
lean_del_object(v___x_1169_);
v_val_1171_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v_a_1167_, 1);
lean_inc_ref(v_q_u03b1_1157_);
v___x_1172_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_u03b1_1157_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
lean_inc_ref(v_qb_1158_);
v___x_1174_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_qb_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
lean_inc_ref(v_arg_1156_);
v___x_1176_ = l_Lean_Meta_Sym_mkOrS(v_a_1175_, v_arg_1156_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_box(0);
v___x_1179_ = 0;
lean_inc_ref(v_q_u03b1_1157_);
v___x_1180_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(v___x_1178_, v___x_1179_, v_q_u03b1_1157_, v_a_1177_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
lean_inc_ref(v_q_u03b1_1157_);
lean_inc(v_a_1173_);
v___x_1182_ = l_Lean_Meta_Sym_mkExistsS(v_a_1173_, v_q_u03b1_1157_, v_a_1181_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1197_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1187_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__24));
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1173_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_mkConst(v___x_1187_, v___x_1189_);
v___x_1191_ = l_Lean_mkApp4(v___x_1190_, v_q_u03b1_1157_, v_val_1171_, v_qb_1158_, v_arg_1156_);
v___x_1192_ = 0;
v___x_1193_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1193_, 0, v_a_1183_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set_uint8(v___x_1193_, sizeof(void*)*2, v___x_1192_);
lean_ctor_set_uint8(v___x_1193_, sizeof(void*)*2 + 1, v___x_1192_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1193_);
v___x_1195_ = v___x_1185_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_a_1173_);
lean_dec(v_val_1171_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1198_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1182_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1182_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1173_);
lean_dec(v_val_1171_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1206_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1180_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1180_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1173_);
lean_dec(v_val_1171_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1214_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1176_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1176_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_a_1173_);
lean_dec(v_val_1171_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1222_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1174_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1174_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_val_1171_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1230_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1172_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1172_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_dec(v_a_1167_);
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1238_);
v___x_1240_ = v___x_1169_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_qb_1158_);
lean_dec_ref(v_q_u03b1_1157_);
lean_dec_ref(v_arg_1156_);
v_a_1243_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1166_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1166_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___lam__0___boxed(lean_object* v_arg_1251_, lean_object* v_q_u03b1_1252_, lean_object* v_qb_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_Sym_Simp_pullExists___lam__0(v_arg_1251_, v_q_u03b1_1252_, v_qb_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists(lean_object* v_e_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1262_, v_a_1269_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_Lean_Expr_cleanupAnnotations(v_a_1277_);
lean_dec(v_a_1277_);
v___x_1279_ = l_Lean_Expr_isApp(v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v___x_1278_);
goto v___jp_1273_;
}
else
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1278_);
v___x_1281_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v___x_1278_);
goto v___jp_1273_;
}
else
{
lean_object* v_arg_1282_; lean_object* v_arg_1283_; lean_object* v_r_u03b1_1285_; lean_object* v_rb_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_arg_1282_ = lean_ctor_get(v___x_1278_, 1);
lean_inc_ref(v_arg_1282_);
lean_dec_ref(v___x_1278_);
v_arg_1283_ = lean_ctor_get(v___x_1280_, 1);
lean_inc_ref(v_arg_1283_);
v___x_1378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
lean_dec_ref(v___x_1280_);
v___x_1379_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__10));
v___x_1380_ = l_Lean_Expr_isConstOf(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__12));
v___x_1382_ = l_Lean_Expr_isConstOf(v___x_1378_, v___x_1381_);
lean_dec_ref(v___x_1378_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_arg_1283_);
lean_dec_ref(v_arg_1282_);
goto v___jp_1273_;
}
else
{
lean_object* v___x_1383_; lean_object* v_a_1384_; 
v___x_1383_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_arg_1283_);
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
if (lean_obj_tag(v_a_1384_) == 1)
{
lean_object* v_val_1385_; lean_object* v_fst_1386_; lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_arg_1283_);
v_val_1385_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v_a_1384_, 1);
v_fst_1386_ = lean_ctor_get(v_val_1385_, 0);
v_snd_1387_ = lean_ctor_get(v_val_1385_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_val_1385_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1389_ = v_val_1385_;
v_isShared_1390_ = v_isSharedCheck_1458_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_inc(v_fst_1386_);
lean_dec(v_val_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1458_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; 
lean_inc(v_fst_1386_);
v___x_1391_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_1386_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
lean_inc(v_snd_1387_);
v___x_1393_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_snd_1387_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
lean_inc_ref(v_arg_1282_);
v___x_1395_ = l_Lean_Meta_Sym_mkAndS(v_a_1394_, v_arg_1282_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_box(0);
v___x_1398_ = 0;
lean_inc(v_fst_1386_);
v___x_1399_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(v___x_1397_, v___x_1398_, v_fst_1386_, v_a_1396_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
lean_inc(v_fst_1386_);
lean_inc(v_a_1392_);
v___x_1401_ = l_Lean_Meta_Sym_mkExistsS(v_a_1392_, v_fst_1386_, v_a_1400_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1417_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__26));
v___x_1407_ = lean_box(0);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 1);
lean_ctor_set(v___x_1389_, 1, v___x_1407_);
lean_ctor_set(v___x_1389_, 0, v_a_1392_);
v___x_1409_ = v___x_1389_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1392_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1410_ = l_Lean_mkConst(v___x_1406_, v___x_1409_);
v___x_1411_ = l_Lean_mkApp3(v___x_1410_, v_fst_1386_, v_snd_1387_, v_arg_1282_);
v___x_1412_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1412_, 0, v_a_1402_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*2, v___x_1380_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*2 + 1, v___x_1380_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1392_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_dec_ref(v_arg_1282_);
v_a_1418_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1401_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1401_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1392_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_dec_ref(v_arg_1282_);
v_a_1426_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1399_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1399_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1392_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_dec_ref(v_arg_1282_);
v_a_1434_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1395_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1395_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1392_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_dec_ref(v_arg_1282_);
v_a_1442_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1393_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1393_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v_fst_1386_);
lean_dec_ref(v_arg_1282_);
v_a_1450_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1391_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1391_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_object* v___x_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1384_);
v___x_1459_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_arg_1282_);
lean_dec_ref(v_arg_1282_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1542_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1542_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_a_1460_) == 1)
{
lean_object* v_val_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1537_; 
lean_del_object(v___x_1462_);
v_val_1464_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_a_1460_, 1);
v_fst_1465_ = lean_ctor_get(v_val_1464_, 0);
v_snd_1466_ = lean_ctor_get(v_val_1464_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_val_1464_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1468_ = v_val_1464_;
v_isShared_1469_ = v_isSharedCheck_1537_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snd_1466_);
lean_inc(v_fst_1465_);
lean_dec(v_val_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1537_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; 
lean_inc(v_fst_1465_);
v___x_1470_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_1465_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
lean_inc(v_snd_1466_);
v___x_1472_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_snd_1466_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
lean_inc_ref(v_arg_1283_);
v___x_1474_ = l_Lean_Meta_Sym_mkAndS(v_arg_1283_, v_a_1473_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = lean_box(0);
v___x_1477_ = 0;
lean_inc(v_fst_1465_);
v___x_1478_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(v___x_1476_, v___x_1477_, v_fst_1465_, v_a_1475_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
lean_inc(v_fst_1465_);
lean_inc(v_a_1471_);
v___x_1480_ = l_Lean_Meta_Sym_mkExistsS(v_a_1471_, v_fst_1465_, v_a_1479_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1496_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__28));
v___x_1486_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 1);
lean_ctor_set(v___x_1468_, 1, v___x_1486_);
lean_ctor_set(v___x_1468_, 0, v_a_1471_);
v___x_1488_ = v___x_1468_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1471_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1489_ = l_Lean_mkConst(v___x_1485_, v___x_1488_);
v___x_1490_ = l_Lean_mkApp3(v___x_1489_, v_fst_1465_, v_arg_1283_, v_snd_1466_);
v___x_1491_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1491_, 0, v_a_1481_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*2, v___x_1380_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*2 + 1, v___x_1380_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1491_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1468_);
lean_dec(v_snd_1466_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_arg_1283_);
v_a_1497_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1480_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1480_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1468_);
lean_dec(v_snd_1466_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_arg_1283_);
v_a_1505_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1478_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1478_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1468_);
lean_dec(v_snd_1466_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_arg_1283_);
v_a_1513_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1474_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1474_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1468_);
lean_dec(v_snd_1466_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_arg_1283_);
v_a_1521_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1472_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1472_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_del_object(v___x_1468_);
lean_dec(v_snd_1466_);
lean_dec(v_fst_1465_);
lean_dec_ref(v_arg_1283_);
v_a_1529_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1470_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1470_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec(v_a_1460_);
lean_dec_ref(v_arg_1283_);
v___x_1538_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1538_, 0, v___x_1380_);
lean_ctor_set_uint8(v___x_1538_, 1, v___x_1380_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1538_);
v___x_1540_ = v___x_1462_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
else
{
lean_object* v___x_1543_; lean_object* v_a_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v___x_1378_);
v___x_1543_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_arg_1283_);
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_matchExists_x3f___redArg(v_arg_1282_);
if (lean_obj_tag(v_a_1544_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v_arg_1282_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1557_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1557_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
if (lean_obj_tag(v_a_1546_) == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec_ref(v_arg_1283_);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
else
{
lean_object* v_val_1554_; lean_object* v_fst_1555_; lean_object* v_snd_1556_; 
lean_del_object(v___x_1548_);
v_val_1554_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v_a_1546_, 1);
v_fst_1555_ = lean_ctor_get(v_val_1554_, 0);
lean_inc(v_fst_1555_);
v_snd_1556_ = lean_ctor_get(v_val_1554_, 1);
lean_inc(v_snd_1556_);
lean_dec(v_val_1554_);
v_r_u03b1_1285_ = v_fst_1555_;
v_rb_1286_ = v_snd_1556_;
v___y_1287_ = v_a_1266_;
v___y_1288_ = v_a_1267_;
v___y_1289_ = v_a_1268_;
v___y_1290_ = v_a_1269_;
v___y_1291_ = v_a_1270_;
v___y_1292_ = v_a_1271_;
goto v___jp_1284_;
}
}
}
else
{
lean_object* v_val_1558_; lean_object* v_a_1559_; 
v_val_1558_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_a_1544_, 1);
v_a_1559_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1545_);
if (lean_obj_tag(v_a_1559_) == 0)
{
lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_arg_1283_);
v_fst_1560_ = lean_ctor_get(v_val_1558_, 0);
lean_inc(v_fst_1560_);
v_snd_1561_ = lean_ctor_get(v_val_1558_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_val_1558_);
v___x_1562_ = l_Lean_Meta_Sym_Simp_pullExists___lam__0(v_arg_1282_, v_fst_1560_, v_snd_1561_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1562_;
}
else
{
lean_object* v_val_1563_; lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1652_; 
v_val_1563_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v_a_1559_, 1);
v_fst_1564_ = lean_ctor_get(v_val_1558_, 0);
lean_inc(v_fst_1564_);
v_snd_1565_ = lean_ctor_get(v_val_1558_, 1);
lean_inc(v_snd_1565_);
lean_dec(v_val_1558_);
v_fst_1566_ = lean_ctor_get(v_val_1563_, 0);
v_snd_1567_ = lean_ctor_get(v_val_1563_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_val_1563_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1569_ = v_val_1563_;
v_isShared_1570_ = v_isSharedCheck_1652_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_inc(v_fst_1566_);
lean_dec(v_val_1563_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1652_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_expr_eqv(v_fst_1564_, v_fst_1566_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1569_);
v___x_1572_ = l_Lean_Meta_Sym_Simp_pullExists___lam__0(v_arg_1282_, v_fst_1564_, v_snd_1565_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
if (lean_obj_tag(v_a_1573_) == 0)
{
lean_dec_ref_known(v___x_1572_, 1);
v_r_u03b1_1285_ = v_fst_1566_;
v_rb_1286_ = v_snd_1567_;
v___y_1287_ = v_a_1266_;
v___y_1288_ = v_a_1267_;
v___y_1289_ = v_a_1268_;
v___y_1290_ = v_a_1269_;
v___y_1291_ = v_a_1270_;
v___y_1292_ = v_a_1271_;
goto v___jp_1284_;
}
else
{
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_arg_1283_);
return v___x_1572_;
}
}
else
{
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_arg_1283_);
return v___x_1572_;
}
}
else
{
uint8_t v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_fst_1566_);
lean_dec_ref(v_arg_1283_);
lean_dec_ref(v_arg_1282_);
v___x_1574_ = 0;
lean_inc(v_fst_1564_);
v___x_1575_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_1564_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
lean_inc(v_snd_1565_);
v___x_1577_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_snd_1565_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v_snd_1567_);
v___x_1579_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_snd_1567_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_Meta_Sym_mkOrS(v_a_1578_, v_a_1580_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_box(0);
v___x_1584_ = 0;
lean_inc(v_fst_1564_);
v___x_1585_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_pullExists_spec__0___redArg(v___x_1583_, v___x_1584_, v_fst_1564_, v_a_1582_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
lean_inc(v_fst_1564_);
lean_inc(v_a_1576_);
v___x_1587_ = l_Lean_Meta_Sym_mkExistsS(v_a_1576_, v_fst_1564_, v_a_1586_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1603_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1603_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1603_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1592_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__20));
v___x_1593_ = lean_box(0);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 1);
lean_ctor_set(v___x_1569_, 1, v___x_1593_);
lean_ctor_set(v___x_1569_, 0, v_a_1576_);
v___x_1595_ = v___x_1569_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1576_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1596_ = l_Lean_mkConst(v___x_1592_, v___x_1595_);
v___x_1597_ = l_Lean_mkApp3(v___x_1596_, v_fst_1564_, v_snd_1565_, v_snd_1567_);
v___x_1598_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1598_, 0, v_a_1588_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*2, v___x_1574_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*2 + 1, v___x_1574_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1598_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1576_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1604_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1587_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1587_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1576_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1612_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1585_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1585_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_a_1576_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1620_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1581_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1581_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1578_);
lean_dec(v_a_1576_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1628_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1579_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1579_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1576_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1636_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1577_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1577_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
v_a_1644_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1575_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1575_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
}
}
v___jp_1284_:
{
lean_object* v___x_1293_; 
lean_inc_ref(v_r_u03b1_1285_);
v___x_1293_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_r_u03b1_1285_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1369_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1369_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1369_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
if (lean_obj_tag(v_a_1294_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
lean_del_object(v___x_1296_);
v_val_1298_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_a_1294_, 1);
lean_inc_ref(v_r_u03b1_1285_);
v___x_1299_ = l_Lean_Meta_Sym_getLevel___redArg(v_r_u03b1_1285_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
lean_inc_ref(v_rb_1286_);
v___x_1301_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullExists_beta0(v_rb_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
lean_inc_ref(v_arg_1283_);
v___x_1303_ = l_Lean_Meta_Sym_mkOrS(v_arg_1283_, v_a_1302_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_box(0);
v___x_1306_ = 0;
lean_inc_ref(v_r_u03b1_1285_);
v___x_1307_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_Simp_minscope_spec__1(v___x_1305_, v___x_1306_, v_r_u03b1_1285_, v_a_1304_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
lean_inc_ref(v_r_u03b1_1285_);
lean_inc(v_a_1300_);
v___x_1309_ = l_Lean_Meta_Sym_mkExistsS(v_a_1300_, v_r_u03b1_1285_, v_a_1308_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1324_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__22));
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_a_1300_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_mkConst(v___x_1314_, v___x_1316_);
v___x_1318_ = l_Lean_mkApp4(v___x_1317_, v_r_u03b1_1285_, v_val_1298_, v_arg_1283_, v_rb_1286_);
v___x_1319_ = 0;
v___x_1320_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1320_, 0, v_a_1310_);
lean_ctor_set(v___x_1320_, 1, v___x_1318_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*2, v___x_1319_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*2 + 1, v___x_1319_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1320_);
v___x_1322_ = v___x_1312_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1300_);
lean_dec(v_val_1298_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1325_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1309_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1309_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1300_);
lean_dec(v_val_1298_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1333_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1307_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1307_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1300_);
lean_dec(v_val_1298_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1341_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1303_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1303_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1300_);
lean_dec(v_val_1298_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1349_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1301_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1301_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_val_1298_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1357_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1299_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1299_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v_a_1294_);
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v___x_1365_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1365_);
v___x_1367_ = v___x_1296_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_rb_1286_);
lean_dec_ref(v_r_u03b1_1285_);
lean_dec_ref(v_arg_1283_);
v_a_1370_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1293_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1293_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1276_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1276_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
v___jp_1273_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullExists___boxed(lean_object* v_e_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Sym_Simp_pullExists(v_e_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(lean_object* v_e_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
if (lean_obj_tag(v_e_1673_) == 7)
{
lean_object* v_binderName_1679_; lean_object* v_binderType_1680_; lean_object* v_body_1681_; uint8_t v_binderInfo_1682_; lean_object* v___x_1683_; 
v_binderName_1679_ = lean_ctor_get(v_e_1673_, 0);
lean_inc(v_binderName_1679_);
v_binderType_1680_ = lean_ctor_get(v_e_1673_, 1);
lean_inc_ref_n(v_binderType_1680_, 2);
v_body_1681_ = lean_ctor_get(v_e_1673_, 2);
lean_inc_ref(v_body_1681_);
v_binderInfo_1682_ = lean_ctor_get_uint8(v_e_1673_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1673_, 3);
v___x_1683_ = l_Lean_Meta_isProp(v_binderType_1680_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1701_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1701_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1701_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Lean_Expr_hasLooseBVars(v_body_1681_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_unbox(v_a_1684_);
lean_dec(v_a_1684_);
if (v___x_1698_ == 0)
{
goto v___jp_1688_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_del_object(v___x_1686_);
lean_dec_ref(v_body_1681_);
lean_dec_ref(v_binderType_1680_);
lean_dec(v_binderName_1679_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
return v___x_1700_;
}
}
else
{
lean_dec(v_a_1684_);
goto v___jp_1688_;
}
v___jp_1688_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1689_ = lean_box(v_binderInfo_1682_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_body_1681_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_binderType_1680_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_binderName_1679_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1693_);
v___x_1695_ = v___x_1686_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_body_1681_);
lean_dec_ref(v_binderType_1680_);
lean_dec(v_binderName_1679_);
v_a_1702_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1683_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1683_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref(v_e_1673_);
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg___boxed(lean_object* v_e_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_e_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f(lean_object* v_e_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_e_1719_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___boxed(lean_object* v_e_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f(v_e_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0(lean_object* v_x_1737_, uint8_t v_bi_1738_, lean_object* v_t_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___y_1749_; lean_object* v___x_1752_; uint8_t v_debug_1753_; 
v___x_1752_ = lean_st_ref_get(v___y_1742_);
v_debug_1753_ = lean_ctor_get_uint8(v___x_1752_, sizeof(void*)*13);
lean_dec(v___x_1752_);
if (v_debug_1753_ == 0)
{
v___y_1749_ = v___y_1742_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1739_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; 
lean_dec_ref_known(v___x_1754_, 1);
v___x_1755_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref_known(v___x_1755_, 1);
v___y_1749_ = v___y_1742_;
goto v___jp_1748_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_b_1740_);
lean_dec_ref(v_t_1739_);
lean_dec(v_x_1737_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_b_1740_);
lean_dec_ref(v_t_1739_);
lean_dec(v_x_1737_);
v_a_1764_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1754_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1754_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
v___jp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l_Lean_Expr_forallE___override(v_x_1737_, v_t_1739_, v_b_1740_, v_bi_1738_);
v___x_1751_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1750_, v___y_1749_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0___boxed(lean_object* v_x_1772_, lean_object* v_bi_1773_, lean_object* v_t_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v_bi_boxed_1783_; lean_object* v_res_1784_; 
v_bi_boxed_1783_ = lean_unbox(v_bi_1773_);
v_res_1784_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0(v_x_1772_, v_bi_boxed_1783_, v_t_1774_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0(lean_object* v_arg_1785_, uint8_t v___x_1786_, lean_object* v_qn_1787_, lean_object* v_q_u03b1_1788_, lean_object* v_qb_1789_, uint8_t v_qinfo_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
lean_inc_ref(v_q_u03b1_1788_);
v___x_1798_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_q_u03b1_1788_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1852_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1852_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1852_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
if (lean_obj_tag(v_a_1799_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; 
lean_del_object(v___x_1801_);
v_val_1803_ = lean_ctor_get(v_a_1799_, 0);
lean_inc(v_val_1803_);
lean_dec_ref_known(v_a_1799_, 1);
lean_inc_ref(v_q_u03b1_1788_);
v___x_1804_ = l_Lean_Meta_Sym_getLevel___redArg(v_q_u03b1_1788_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
lean_inc_ref(v_qb_1789_);
lean_inc_ref(v_q_u03b1_1788_);
lean_inc(v_qn_1787_);
v___x_1806_ = l_Lean_mkLambda(v_qn_1787_, v_qinfo_1790_, v_q_u03b1_1788_, v_qb_1789_);
lean_inc_ref(v_arg_1785_);
v___x_1807_ = l_Lean_Meta_Sym_mkAndS(v_qb_1789_, v_arg_1785_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
lean_inc_ref(v_q_u03b1_1788_);
v___x_1809_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0(v_qn_1787_, v_qinfo_1790_, v_q_u03b1_1788_, v_a_1808_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1823_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1814_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__7));
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_a_1805_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_mkConst(v___x_1814_, v___x_1816_);
v___x_1818_ = l_Lean_mkApp4(v___x_1817_, v_q_u03b1_1788_, v_val_1803_, v___x_1806_, v_arg_1785_);
v___x_1819_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1819_, 0, v_a_1810_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
lean_ctor_set_uint8(v___x_1819_, sizeof(void*)*2, v___x_1786_);
lean_ctor_set_uint8(v___x_1819_, sizeof(void*)*2 + 1, v___x_1786_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1819_);
v___x_1821_ = v___x_1812_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v___x_1806_);
lean_dec(v_a_1805_);
lean_dec(v_val_1803_);
lean_dec_ref(v_q_u03b1_1788_);
lean_dec_ref(v_arg_1785_);
v_a_1824_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1809_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1809_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v___x_1806_);
lean_dec(v_a_1805_);
lean_dec(v_val_1803_);
lean_dec_ref(v_q_u03b1_1788_);
lean_dec(v_qn_1787_);
lean_dec_ref(v_arg_1785_);
v_a_1832_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1807_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1807_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_val_1803_);
lean_dec_ref(v_qb_1789_);
lean_dec_ref(v_q_u03b1_1788_);
lean_dec(v_qn_1787_);
lean_dec_ref(v_arg_1785_);
v_a_1840_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1804_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1804_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_a_1799_);
lean_dec_ref(v_qb_1789_);
lean_dec_ref(v_q_u03b1_1788_);
lean_dec(v_qn_1787_);
lean_dec_ref(v_arg_1785_);
v___x_1848_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1848_, 0, v___x_1786_);
lean_ctor_set_uint8(v___x_1848_, 1, v___x_1786_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1848_);
v___x_1850_ = v___x_1801_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_qb_1789_);
lean_dec_ref(v_q_u03b1_1788_);
lean_dec(v_qn_1787_);
lean_dec_ref(v_arg_1785_);
v_a_1853_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1798_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1798_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0___boxed(lean_object* v_arg_1861_, lean_object* v___x_1862_, lean_object* v_qn_1863_, lean_object* v_q_u03b1_1864_, lean_object* v_qb_1865_, lean_object* v_qinfo_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
uint8_t v___x_31434__boxed_1874_; uint8_t v_qinfo_boxed_1875_; lean_object* v_res_1876_; 
v___x_31434__boxed_1874_ = lean_unbox(v___x_1862_);
v_qinfo_boxed_1875_ = lean_unbox(v_qinfo_1866_);
v_res_1876_ = l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0(v_arg_1861_, v___x_31434__boxed_1874_, v_qn_1863_, v_q_u03b1_1864_, v_qb_1865_, v_qinfo_boxed_1875_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg(lean_object* v_e_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1877_, v_a_1881_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = l_Lean_Expr_cleanupAnnotations(v_a_1889_);
lean_dec(v_a_1889_);
v___x_1891_ = l_Lean_Expr_isApp(v___x_1890_);
if (v___x_1891_ == 0)
{
lean_dec_ref(v___x_1890_);
goto v___jp_1885_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1890_);
v___x_1893_ = l_Lean_Expr_isApp(v___x_1892_);
if (v___x_1893_ == 0)
{
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1890_);
goto v___jp_1885_;
}
else
{
lean_object* v_arg_1894_; lean_object* v_arg_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; lean_object* v_rn_1900_; lean_object* v_r_u03b1_1901_; lean_object* v_rb_1902_; uint8_t v_rinfo_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; 
v_arg_1894_ = lean_ctor_get(v___x_1890_, 1);
lean_inc_ref(v_arg_1894_);
lean_dec_ref(v___x_1890_);
v_arg_1895_ = lean_ctor_get(v___x_1892_, 1);
lean_inc_ref(v_arg_1895_);
v___x_1896_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1892_);
lean_dec_ref(v___x_1892_);
v___x_1897_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__10));
v___x_1898_ = l_Lean_Expr_isConstOf(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__12));
v___x_1974_ = l_Lean_Expr_isConstOf(v___x_1896_, v___x_1973_);
lean_dec_ref(v___x_1896_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_arg_1895_);
lean_dec_ref(v_arg_1894_);
goto v___jp_1885_;
}
else
{
lean_object* v___x_1975_; 
lean_inc_ref(v_arg_1895_);
v___x_1975_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_arg_1895_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
lean_inc_ref(v_arg_1894_);
v___x_1977_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_arg_1894_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_1977_) == 0)
{
if (lean_obj_tag(v_a_1976_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_arg_1894_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1994_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1994_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
if (lean_obj_tag(v_a_1978_) == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_dec_ref(v_arg_1895_);
v___x_1982_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1982_, 0, v___x_1898_);
lean_ctor_set_uint8(v___x_1982_, 1, v___x_1898_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v_val_1986_; lean_object* v_snd_1987_; lean_object* v_snd_1988_; lean_object* v_fst_1989_; lean_object* v_fst_1990_; lean_object* v_fst_1991_; lean_object* v_snd_1992_; uint8_t v___x_1993_; 
lean_del_object(v___x_1980_);
v_val_1986_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_a_1978_, 1);
v_snd_1987_ = lean_ctor_get(v_val_1986_, 1);
lean_inc(v_snd_1987_);
v_snd_1988_ = lean_ctor_get(v_snd_1987_, 1);
lean_inc(v_snd_1988_);
v_fst_1989_ = lean_ctor_get(v_val_1986_, 0);
lean_inc(v_fst_1989_);
lean_dec(v_val_1986_);
v_fst_1990_ = lean_ctor_get(v_snd_1987_, 0);
lean_inc(v_fst_1990_);
lean_dec(v_snd_1987_);
v_fst_1991_ = lean_ctor_get(v_snd_1988_, 0);
lean_inc(v_fst_1991_);
v_snd_1992_ = lean_ctor_get(v_snd_1988_, 1);
lean_inc(v_snd_1992_);
lean_dec(v_snd_1988_);
v___x_1993_ = lean_unbox(v_snd_1992_);
lean_dec(v_snd_1992_);
v_rn_1900_ = v_fst_1989_;
v_r_u03b1_1901_ = v_fst_1990_;
v_rb_1902_ = v_fst_1991_;
v_rinfo_1903_ = v___x_1993_;
v___y_1904_ = v_a_1878_;
v___y_1905_ = v_a_1879_;
v___y_1906_ = v_a_1880_;
v___y_1907_ = v_a_1881_;
v___y_1908_ = v_a_1882_;
v___y_1909_ = v_a_1883_;
goto v___jp_1899_;
}
}
}
else
{
lean_object* v_val_1995_; lean_object* v_snd_1996_; lean_object* v_snd_1997_; lean_object* v_a_1998_; 
v_val_1995_ = lean_ctor_get(v_a_1976_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v_a_1976_, 1);
v_snd_1996_ = lean_ctor_get(v_val_1995_, 1);
lean_inc(v_snd_1996_);
v_snd_1997_ = lean_ctor_get(v_snd_1996_, 1);
lean_inc(v_snd_1997_);
v_a_1998_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1977_, 1);
if (lean_obj_tag(v_a_1998_) == 0)
{
lean_object* v_fst_1999_; lean_object* v_fst_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; 
lean_dec_ref(v_arg_1895_);
v_fst_1999_ = lean_ctor_get(v_val_1995_, 0);
lean_inc(v_fst_1999_);
lean_dec(v_val_1995_);
v_fst_2000_ = lean_ctor_get(v_snd_1996_, 0);
lean_inc(v_fst_2000_);
lean_dec(v_snd_1996_);
v_fst_2001_ = lean_ctor_get(v_snd_1997_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v_snd_1997_, 1);
lean_inc(v_snd_2002_);
lean_dec(v_snd_1997_);
v___x_2003_ = lean_unbox(v_snd_2002_);
lean_dec(v_snd_2002_);
v___x_2004_ = l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0(v_arg_1894_, v___x_1898_, v_fst_1999_, v_fst_2000_, v_fst_2001_, v___x_2003_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
return v___x_2004_;
}
else
{
lean_object* v_val_2005_; lean_object* v_snd_2006_; lean_object* v_snd_2007_; lean_object* v_fst_2008_; lean_object* v_fst_2009_; lean_object* v_fst_2010_; lean_object* v_snd_2011_; lean_object* v_fst_2012_; lean_object* v_fst_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2074_; 
v_val_2005_ = lean_ctor_get(v_a_1998_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v_a_1998_, 1);
v_snd_2006_ = lean_ctor_get(v_val_2005_, 1);
lean_inc(v_snd_2006_);
v_snd_2007_ = lean_ctor_get(v_snd_2006_, 1);
lean_inc(v_snd_2007_);
v_fst_2008_ = lean_ctor_get(v_val_1995_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_val_1995_);
v_fst_2009_ = lean_ctor_get(v_snd_1996_, 0);
lean_inc(v_fst_2009_);
lean_dec(v_snd_1996_);
v_fst_2010_ = lean_ctor_get(v_snd_1997_, 0);
lean_inc(v_fst_2010_);
v_snd_2011_ = lean_ctor_get(v_snd_1997_, 1);
lean_inc(v_snd_2011_);
lean_dec(v_snd_1997_);
v_fst_2012_ = lean_ctor_get(v_val_2005_, 0);
lean_inc(v_fst_2012_);
lean_dec(v_val_2005_);
v_fst_2013_ = lean_ctor_get(v_snd_2006_, 0);
lean_inc(v_fst_2013_);
lean_dec(v_snd_2006_);
v_fst_2014_ = lean_ctor_get(v_snd_2007_, 0);
v_snd_2015_ = lean_ctor_get(v_snd_2007_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_snd_2007_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2017_ = v_snd_2007_;
v_isShared_2018_ = v_isSharedCheck_2074_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v_snd_2007_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2074_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_expr_eqv(v_fst_2009_, v_fst_2013_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; lean_object* v___x_2021_; 
lean_del_object(v___x_2017_);
v___x_2020_ = lean_unbox(v_snd_2011_);
lean_dec(v_snd_2011_);
v___x_2021_ = l_Lean_Meta_Sym_Simp_pullForall___redArg___lam__0(v_arg_1894_, v___x_1898_, v_fst_2008_, v_fst_2009_, v_fst_2010_, v___x_2020_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
if (lean_obj_tag(v_a_2022_) == 0)
{
uint8_t v___x_2023_; 
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unbox(v_snd_2015_);
lean_dec(v_snd_2015_);
v_rn_1900_ = v_fst_2012_;
v_r_u03b1_1901_ = v_fst_2013_;
v_rb_1902_ = v_fst_2014_;
v_rinfo_1903_ = v___x_2023_;
v___y_1904_ = v_a_1878_;
v___y_1905_ = v_a_1879_;
v___y_1906_ = v_a_1880_;
v___y_1907_ = v_a_1881_;
v___y_1908_ = v_a_1882_;
v___y_1909_ = v_a_1883_;
goto v___jp_1899_;
}
else
{
lean_dec(v_snd_2015_);
lean_dec(v_fst_2014_);
lean_dec(v_fst_2013_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_arg_1895_);
return v___x_2021_;
}
}
else
{
lean_dec(v_snd_2015_);
lean_dec(v_fst_2014_);
lean_dec(v_fst_2013_);
lean_dec(v_fst_2012_);
lean_dec_ref(v_arg_1895_);
return v___x_2021_;
}
}
else
{
lean_object* v___x_2024_; 
lean_dec_ref(v_arg_1895_);
lean_dec_ref(v_arg_1894_);
lean_inc(v_fst_2009_);
v___x_2024_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_2009_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = lean_unbox(v_snd_2011_);
lean_inc(v_fst_2010_);
lean_inc(v_fst_2009_);
lean_inc(v_fst_2008_);
v___x_2027_ = l_Lean_mkLambda(v_fst_2008_, v___x_2026_, v_fst_2009_, v_fst_2010_);
v___x_2028_ = lean_unbox(v_snd_2015_);
lean_dec(v_snd_2015_);
lean_inc(v_fst_2014_);
v___x_2029_ = l_Lean_mkLambda(v_fst_2012_, v___x_2028_, v_fst_2013_, v_fst_2014_);
v___x_2030_ = l_Lean_Meta_Sym_mkAndS(v_fst_2010_, v_fst_2014_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = lean_unbox(v_snd_2011_);
lean_dec(v_snd_2011_);
lean_inc(v_fst_2009_);
v___x_2033_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_fst_2008_, v___x_2032_, v_fst_2009_, v_a_2031_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2049_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__3));
v___x_2039_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 1, v___x_2039_);
lean_ctor_set(v___x_2017_, 0, v_a_2025_);
v___x_2041_ = v___x_2017_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2025_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2042_ = l_Lean_mkConst(v___x_2038_, v___x_2041_);
v___x_2043_ = l_Lean_mkApp3(v___x_2042_, v_fst_2009_, v___x_2027_, v___x_2029_);
v___x_2044_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2044_, 0, v_a_2034_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*2, v___x_1898_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*2 + 1, v___x_1898_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2044_);
v___x_2046_ = v___x_2036_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2027_);
lean_dec(v_a_2025_);
lean_del_object(v___x_2017_);
lean_dec(v_fst_2009_);
v_a_2050_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2033_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2033_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2027_);
lean_dec(v_a_2025_);
lean_del_object(v___x_2017_);
lean_dec(v_snd_2011_);
lean_dec(v_fst_2009_);
lean_dec(v_fst_2008_);
v_a_2058_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2030_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2030_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
lean_dec(v_fst_2014_);
lean_dec(v_fst_2013_);
lean_dec(v_fst_2012_);
lean_dec(v_snd_2011_);
lean_dec(v_fst_2010_);
lean_dec(v_fst_2009_);
lean_dec(v_fst_2008_);
v_a_2066_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2024_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2024_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
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
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_1976_);
lean_dec_ref(v_arg_1895_);
lean_dec_ref(v_arg_1894_);
v_a_2075_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_1977_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_1977_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_arg_1895_);
lean_dec_ref(v_arg_1894_);
v_a_2083_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_1975_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_1975_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref(v___x_1896_);
lean_inc_ref(v_arg_1895_);
v___x_2091_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_arg_1895_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
if (lean_obj_tag(v_a_2092_) == 1)
{
lean_object* v_val_2093_; lean_object* v_snd_2094_; lean_object* v_snd_2095_; lean_object* v_fst_2096_; lean_object* v_fst_2097_; lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_arg_1895_);
v_val_2093_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_val_2093_);
lean_dec_ref_known(v_a_2092_, 1);
v_snd_2094_ = lean_ctor_get(v_val_2093_, 1);
lean_inc(v_snd_2094_);
v_snd_2095_ = lean_ctor_get(v_snd_2094_, 1);
lean_inc(v_snd_2095_);
v_fst_2096_ = lean_ctor_get(v_val_2093_, 0);
lean_inc(v_fst_2096_);
lean_dec(v_val_2093_);
v_fst_2097_ = lean_ctor_get(v_snd_2094_, 0);
lean_inc(v_fst_2097_);
lean_dec(v_snd_2094_);
v_fst_2098_ = lean_ctor_get(v_snd_2095_, 0);
v_snd_2099_ = lean_ctor_get(v_snd_2095_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_snd_2095_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2101_ = v_snd_2095_;
v_isShared_2102_ = v_isSharedCheck_2152_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_dec(v_snd_2095_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2152_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; 
lean_inc(v_fst_2097_);
v___x_2103_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_2097_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = lean_unbox(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_inc(v_fst_2097_);
lean_inc(v_fst_2096_);
v___x_2106_ = l_Lean_mkLambda(v_fst_2096_, v___x_2105_, v_fst_2097_, v_fst_2098_);
lean_inc_ref(v_arg_1894_);
v___x_2107_ = l_Lean_Meta_Sym_mkOrS(v_fst_2098_, v_arg_1894_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = lean_unbox(v_snd_2099_);
lean_dec(v_snd_2099_);
lean_inc(v_fst_2097_);
v___x_2110_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_fst_2096_, v___x_2109_, v_fst_2097_, v_a_2108_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2127_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2115_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__14));
v___x_2116_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
lean_ctor_set(v___x_2101_, 1, v___x_2116_);
lean_ctor_set(v___x_2101_, 0, v_a_2104_);
v___x_2118_ = v___x_2101_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2104_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2119_ = l_Lean_mkConst(v___x_2115_, v___x_2118_);
v___x_2120_ = l_Lean_mkApp3(v___x_2119_, v_fst_2097_, v___x_2106_, v_arg_1894_);
v___x_2121_ = 0;
v___x_2122_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2122_, 0, v_a_2111_);
lean_ctor_set(v___x_2122_, 1, v___x_2120_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*2, v___x_2121_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*2 + 1, v___x_2121_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2122_);
v___x_2124_ = v___x_2113_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2104_);
lean_del_object(v___x_2101_);
lean_dec(v_fst_2097_);
lean_dec_ref(v_arg_1894_);
v_a_2128_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2110_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2110_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2104_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2097_);
lean_dec(v_fst_2096_);
lean_dec_ref(v_arg_1894_);
v_a_2136_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2107_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2107_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec(v_fst_2097_);
lean_dec(v_fst_2096_);
lean_dec_ref(v_arg_1894_);
v_a_2144_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2103_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2103_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v___x_2153_; 
lean_dec(v_a_2092_);
v___x_2153_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_pullForall_matchForall_x3f___redArg(v_arg_1894_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2222_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2222_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2222_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
if (lean_obj_tag(v_a_2154_) == 1)
{
lean_object* v_val_2158_; lean_object* v_snd_2159_; lean_object* v_snd_2160_; lean_object* v_fst_2161_; lean_object* v_fst_2162_; lean_object* v_fst_2163_; lean_object* v_snd_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2217_; 
lean_del_object(v___x_2156_);
v_val_2158_ = lean_ctor_get(v_a_2154_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v_a_2154_, 1);
v_snd_2159_ = lean_ctor_get(v_val_2158_, 1);
lean_inc(v_snd_2159_);
v_snd_2160_ = lean_ctor_get(v_snd_2159_, 1);
lean_inc(v_snd_2160_);
v_fst_2161_ = lean_ctor_get(v_val_2158_, 0);
lean_inc(v_fst_2161_);
lean_dec(v_val_2158_);
v_fst_2162_ = lean_ctor_get(v_snd_2159_, 0);
lean_inc(v_fst_2162_);
lean_dec(v_snd_2159_);
v_fst_2163_ = lean_ctor_get(v_snd_2160_, 0);
v_snd_2164_ = lean_ctor_get(v_snd_2160_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_snd_2160_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2166_ = v_snd_2160_;
v_isShared_2167_ = v_isSharedCheck_2217_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snd_2164_);
lean_inc(v_fst_2163_);
lean_dec(v_snd_2160_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2217_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; 
lean_inc(v_fst_2162_);
v___x_2168_ = l_Lean_Meta_Sym_getLevel___redArg(v_fst_2162_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = lean_unbox(v_snd_2164_);
lean_inc(v_fst_2163_);
lean_inc(v_fst_2162_);
lean_inc(v_fst_2161_);
v___x_2171_ = l_Lean_mkLambda(v_fst_2161_, v___x_2170_, v_fst_2162_, v_fst_2163_);
lean_inc_ref(v_arg_1895_);
v___x_2172_ = l_Lean_Meta_Sym_mkOrS(v_arg_1895_, v_fst_2163_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_unbox(v_snd_2164_);
lean_dec(v_snd_2164_);
lean_inc(v_fst_2162_);
v___x_2175_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_minscope_spec__0___redArg(v_fst_2161_, v___x_2174_, v_fst_2162_, v_a_2173_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2192_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__16));
v___x_2181_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 1);
lean_ctor_set(v___x_2166_, 1, v___x_2181_);
lean_ctor_set(v___x_2166_, 0, v_a_2169_);
v___x_2183_ = v___x_2166_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2169_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2184_ = l_Lean_mkConst(v___x_2180_, v___x_2183_);
v___x_2185_ = l_Lean_mkApp3(v___x_2184_, v_fst_2162_, v_arg_1895_, v___x_2171_);
v___x_2186_ = 0;
v___x_2187_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2187_, 0, v_a_2176_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2, v___x_2186_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2 + 1, v___x_2186_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2187_);
v___x_2189_ = v___x_2178_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___x_2171_);
lean_dec(v_a_2169_);
lean_del_object(v___x_2166_);
lean_dec(v_fst_2162_);
lean_dec_ref(v_arg_1895_);
v_a_2193_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2175_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2175_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v___x_2171_);
lean_dec(v_a_2169_);
lean_del_object(v___x_2166_);
lean_dec(v_snd_2164_);
lean_dec(v_fst_2162_);
lean_dec(v_fst_2161_);
lean_dec_ref(v_arg_1895_);
v_a_2201_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2172_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2172_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_del_object(v___x_2166_);
lean_dec(v_snd_2164_);
lean_dec(v_fst_2163_);
lean_dec(v_fst_2162_);
lean_dec(v_fst_2161_);
lean_dec_ref(v_arg_1895_);
v_a_2209_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2168_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2168_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec(v_a_2154_);
lean_dec_ref(v_arg_1895_);
v___x_2218_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2218_);
v___x_2220_ = v___x_2156_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_arg_1895_);
v_a_2223_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2153_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2153_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_arg_1895_);
lean_dec_ref(v_arg_1894_);
v_a_2231_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2091_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2091_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
v___jp_1899_:
{
lean_object* v___x_1910_; 
lean_inc_ref(v_r_u03b1_1901_);
v___x_1910_ = l___private_Lean_Meta_Sym_Simp_Prenex_0__Lean_Meta_Sym_Simp_synthNonempty_x3f(v_r_u03b1_1901_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1964_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1964_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1964_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
if (lean_obj_tag(v_a_1911_) == 1)
{
lean_object* v_val_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1913_);
v_val_1915_ = lean_ctor_get(v_a_1911_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_a_1911_, 1);
lean_inc_ref(v_r_u03b1_1901_);
v___x_1916_ = l_Lean_Meta_Sym_getLevel___redArg(v_r_u03b1_1901_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
lean_inc_ref(v_rb_1902_);
lean_inc_ref(v_r_u03b1_1901_);
lean_inc(v_rn_1900_);
v___x_1918_ = l_Lean_mkLambda(v_rn_1900_, v_rinfo_1903_, v_r_u03b1_1901_, v_rb_1902_);
lean_inc_ref(v_arg_1895_);
v___x_1919_ = l_Lean_Meta_Sym_mkAndS(v_arg_1895_, v_rb_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
lean_inc_ref(v_r_u03b1_1901_);
v___x_1921_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_pullForall_spec__0(v_rn_1900_, v_rinfo_1903_, v_r_u03b1_1901_, v_a_1920_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1935_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1935_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1935_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__5));
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1917_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Lean_mkConst(v___x_1926_, v___x_1928_);
v___x_1930_ = l_Lean_mkApp4(v___x_1929_, v_r_u03b1_1901_, v_val_1915_, v_arg_1895_, v___x_1918_);
v___x_1931_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1931_, 0, v_a_1922_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*2, v___x_1898_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*2 + 1, v___x_1898_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1931_);
v___x_1933_ = v___x_1924_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1917_);
lean_dec(v_val_1915_);
lean_dec_ref(v_r_u03b1_1901_);
lean_dec_ref(v_arg_1895_);
v_a_1936_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1921_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1921_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v___x_1918_);
lean_dec(v_a_1917_);
lean_dec(v_val_1915_);
lean_dec_ref(v_r_u03b1_1901_);
lean_dec(v_rn_1900_);
lean_dec_ref(v_arg_1895_);
v_a_1944_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1919_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1919_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_val_1915_);
lean_dec_ref(v_rb_1902_);
lean_dec_ref(v_r_u03b1_1901_);
lean_dec(v_rn_1900_);
lean_dec_ref(v_arg_1895_);
v_a_1952_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1916_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1916_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_a_1911_);
lean_dec_ref(v_rb_1902_);
lean_dec_ref(v_r_u03b1_1901_);
lean_dec(v_rn_1900_);
lean_dec_ref(v_arg_1895_);
v___x_1960_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1960_, 0, v___x_1898_);
lean_ctor_set_uint8(v___x_1960_, 1, v___x_1898_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1960_);
v___x_1962_ = v___x_1913_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_rb_1902_);
lean_dec_ref(v_r_u03b1_1901_);
lean_dec(v_rn_1900_);
lean_dec_ref(v_arg_1895_);
v_a_1965_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1910_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1910_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_1888_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_1888_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
v___jp_1885_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_minscope___closed__8));
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___redArg___boxed(lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_Sym_Simp_pullForall___redArg(v_e_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall(lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Meta_Sym_Simp_pullForall___redArg(v_e_2256_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_pullForall___boxed(lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Meta_Sym_Simp_pullForall(v_e_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
return v_res_2279_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Prenex(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Prenex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Prenex(uint8_t builtin) {
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
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Prenex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Prenex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Prenex(builtin);
}
#ifdef __cplusplus
}
#endif
