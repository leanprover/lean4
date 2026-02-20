// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Propagate
// Imports: import Init.Grind import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Ext import Lean.Meta.Tactic.Grind.Diseq public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "and_eq_of_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 108, 85, 20, 119, 45, 62, 65)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__6;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "and_eq_of_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(42, 144, 170, 255, 103, 245, 81, 212)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "and_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(251, 27, 120, 129, 126, 49, 187, 13)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__12;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "and_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(230, 88, 90, 113, 195, 40, 138, 59)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__15;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateAndDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "eq_true_of_and_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 148, 180, 55, 174, 141, 160, 204)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value;
static lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateAndDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "eq_true_of_and_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 133, 90, 124, 15, 221, 47, 193)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__5;
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "or_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 166, 32, 31, 112, 92, 57, 243)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "or_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 77, 158, 9, 2, 239, 232, 91)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "or_eq_of_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(249, 16, 179, 228, 207, 170, 243, 86)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__10;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "or_eq_of_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(36, 196, 166, 85, 112, 30, 44, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateOrDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "eq_false_of_or_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 204, 80, 248, 17, 222, 207, 37)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value;
static lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateOrDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "eq_false_of_or_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(4, 189, 1, 60, 23, 208, 33, 127)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "false_of_not_eq_self"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 254, 86, 23, 186, 196, 13, 177)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not_eq_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(209, 136, 252, 63, 150, 209, 33, 198)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "not_eq_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(197, 159, 169, 125, 202, 111, 60, 105)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__10;
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateNotDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 178, 136, 115, 199, 101, 23, 5)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value;
static lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateNotDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_true_of_not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 226, 232, 29, 193, 151, 102, 169)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_false_of_not_eq_true'"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 183, 221, 210, 33, 132, 178, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_true_of_not_eq_false'"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 231, 120, 149, 98, 142, 70, 153)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__6;
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0;
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__1_value;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4_value;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_false_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "eq_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(109, 195, 236, 103, 135, 232, 42, 67)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "eq_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 111, 216, 64, 67, 213, 235, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__10;
lean_object* l_Lean_Meta_Grind_mkEqBoolFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqBoolTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8____boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__1_value;
lean_object* l_Lean_Meta_Grind_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_propagateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1_value;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "beq_eq_false_of_diseq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(172, 208, 214, 246, 134, 239, 180, 149)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "beq_eq_true_of_eq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(167, 171, 207, 135, 144, 97, 123, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 188, 189, 31, 103, 102, 90, 237)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_of_beq_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 117, 230, 167, 164, 196, 163, 155)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value;
lean_object* l_Lean_Meta_Grind_isEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value;
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateHEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateHEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8____boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateIte___closed__0;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__4_value;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dite_cond_eq_false'"};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 208, 133, 179, 87, 251, 158, 198)}};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_true'"};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 52, 77, 107, 134, 38, 67, 128)}};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__7_value),LEAN_SCALAR_PTR_LITERAL(182, 147, 228, 248, 61, 236, 36, 195)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value;
static lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__10_value),LEAN_SCALAR_PTR_LITERAL(244, 38, 211, 128, 18, 129, 201, 136)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value;
static lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDecideUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "decide_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 47, 57, 153, 34, 139, 245, 136)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value;
static lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "decide_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 82, 55, 141, 31, 164, 57, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 175, 130, 140, 152, 16, 186, 53)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(163, 211, 47, 64, 193, 141, 13, 161)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(34, 225, 220, 139, 38, 192, 9, 42)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__7;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(55, 49, 202, 191, 5, 220, 111, 69)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 119, 163, 136, 179, 150, 159, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 159, 33, 77, 90, 187, 137, 39)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 189, 183, 67, 38, 153, 146, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 186, 97, 237, 168, 207, 131, 131)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(128, 97, 38, 173, 77, 149, 251, 177)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__7;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(85, 94, 73, 24, 179, 253, 130, 70)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 8, 66, 25, 166, 142, 103, 182)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(181, 34, 184, 188, 120, 43, 145, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 46, 223, 118, 64, 152, 39, 57)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 77, 139, 157, 220, 88, 43, 11)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(244, 210, 8, 221, 13, 95, 8, 117)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 229, 82, 105, 115, 174, 156, 45)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(213, 82, 102, 124, 79, 254, 235, 150)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_19);
x_29 = l_Lean_Meta_Grind_isEqTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_inc_ref(x_22);
x_32 = l_Lean_Meta_Grind_isEqFalse___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc_ref(x_19);
x_35 = l_Lean_Meta_Grind_isEqFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; 
lean_free_object(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_40 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Grind_propagateAndUp___closed__6;
x_43 = l_Lean_mkApp3(x_42, x_22, x_19, x_41);
x_44 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_43, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_52 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_propagateAndUp___closed__6;
x_55 = l_Lean_mkApp3(x_54, x_22, x_19, x_53);
x_56 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_55, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_63 = l_Lean_Meta_Grind_mkEqFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_propagateAndUp___closed__9;
x_66 = l_Lean_mkApp3(x_65, x_22, x_19, x_64);
x_67 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_66, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_74 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_propagateAndUp___closed__12;
lean_inc_ref(x_22);
x_77 = l_Lean_mkApp3(x_76, x_22, x_19, x_75);
x_78 = lean_unbox(x_27);
lean_dec(x_27);
x_79 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_22, x_77, x_78, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
return x_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_27);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_86 = l_Lean_Meta_Grind_mkEqTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Grind_propagateAndUp___closed__15;
lean_inc_ref(x_19);
x_89 = l_Lean_mkApp3(x_88, x_22, x_19, x_87);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_19, x_89, x_90, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
return x_26;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
lean_dec(x_26);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateAndUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_31 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Grind_propagateAndDown___closed__2;
lean_inc(x_32);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_34 = l_Lean_mkApp3(x_33, x_27, x_24, x_32);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_27);
x_35 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_27, x_34, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_35);
x_36 = l_Lean_Meta_Grind_propagateAndDown___closed__5;
lean_inc_ref(x_24);
x_37 = l_Lean_mkApp3(x_36, x_27, x_24, x_32);
x_38 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_24, x_37, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_35;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Expr_cleanupAnnotations(x_1);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec_ref(x_52);
if (x_54 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_55; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_propagateAndDown___closed__2;
lean_inc(x_56);
lean_inc_ref(x_48);
lean_inc_ref(x_51);
x_58 = l_Lean_mkApp3(x_57, x_51, x_48, x_56);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_51);
x_59 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_51, x_58, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_59);
x_60 = l_Lean_Meta_Grind_propagateAndDown___closed__5;
lean_inc_ref(x_48);
x_61 = l_Lean_mkApp3(x_60, x_51, x_48, x_56);
x_62 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_48, x_61, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_62;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_17);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateAndDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_Grind_isEqFalse___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_19);
x_29 = l_Lean_Meta_Grind_isEqFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_inc_ref(x_22);
x_32 = l_Lean_Meta_Grind_isEqTrue___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc_ref(x_19);
x_35 = l_Lean_Meta_Grind_isEqTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; 
lean_free_object(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_40 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Grind_propagateOrUp___closed__4;
x_43 = l_Lean_mkApp3(x_42, x_22, x_19, x_41);
x_44 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_43, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_52 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_propagateOrUp___closed__4;
x_55 = l_Lean_mkApp3(x_54, x_22, x_19, x_53);
x_56 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_55, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_63 = l_Lean_Meta_Grind_mkEqTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_propagateOrUp___closed__7;
x_66 = l_Lean_mkApp3(x_65, x_22, x_19, x_64);
x_67 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_66, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_74 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_propagateOrUp___closed__10;
lean_inc_ref(x_22);
x_77 = l_Lean_mkApp3(x_76, x_22, x_19, x_75);
x_78 = lean_unbox(x_27);
lean_dec(x_27);
x_79 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_22, x_77, x_78, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
return x_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_27);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_86 = l_Lean_Meta_Grind_mkEqFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Grind_propagateOrUp___closed__13;
lean_inc_ref(x_19);
x_89 = l_Lean_mkApp3(x_88, x_22, x_19, x_87);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_19, x_89, x_90, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
return x_26;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
lean_dec(x_26);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateOrUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_31 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Grind_propagateOrDown___closed__2;
lean_inc(x_32);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_34 = l_Lean_mkApp3(x_33, x_27, x_24, x_32);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_27);
x_35 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_27, x_34, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_35);
x_36 = l_Lean_Meta_Grind_propagateOrDown___closed__5;
lean_inc_ref(x_24);
x_37 = l_Lean_mkApp3(x_36, x_27, x_24, x_32);
x_38 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_24, x_37, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_35;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Expr_cleanupAnnotations(x_1);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec_ref(x_52);
if (x_54 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_55; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_propagateOrDown___closed__2;
lean_inc(x_56);
lean_inc_ref(x_48);
lean_inc_ref(x_51);
x_58 = l_Lean_mkApp3(x_57, x_51, x_48, x_56);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_51);
x_59 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_51, x_58, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_59);
x_60 = l_Lean_Meta_Grind_propagateOrDown___closed__5;
lean_inc_ref(x_48);
x_61 = l_Lean_mkApp3(x_60, x_51, x_48, x_56);
x_62 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_48, x_61, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_62;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_17);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateOrDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_19);
x_23 = l_Lean_Meta_Grind_isEqFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_19);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
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
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_19, x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_34 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_propagateNotUp___closed__4;
x_37 = l_Lean_mkAppB(x_36, x_19, x_35);
x_38 = l_Lean_Meta_Grind_closeGoal(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_46 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Grind_propagateNotUp___closed__4;
x_49 = l_Lean_mkAppB(x_48, x_19, x_47);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_57 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Meta_Grind_propagateNotUp___closed__7;
x_60 = l_Lean_mkAppB(x_59, x_19, x_58);
x_61 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_60, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_26, 0);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_68 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_propagateNotUp___closed__10;
x_71 = l_Lean_mkAppB(x_70, x_19, x_69);
x_72 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_71, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_23);
if (x_76 == 0)
{
return x_23;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_23, 0);
lean_inc(x_77);
lean_dec(x_23);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateNotUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_1);
x_23 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
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
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_19, x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_34 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_propagateNotUp___closed__4;
x_37 = l_Lean_mkAppB(x_36, x_19, x_35);
x_38 = l_Lean_Meta_Grind_closeGoal(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_46 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Grind_propagateNotUp___closed__4;
x_49 = l_Lean_mkAppB(x_48, x_19, x_47);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_57 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Meta_Grind_propagateNotDown___closed__2;
lean_inc_ref(x_19);
x_60 = l_Lean_mkAppB(x_59, x_19, x_58);
x_61 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_19, x_60, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_26, 0);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_68 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_propagateNotDown___closed__5;
lean_inc_ref(x_19);
x_71 = l_Lean_mkAppB(x_70, x_19, x_69);
x_72 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_19, x_71, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_23);
if (x_76 == 0)
{
return x_23;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_23, 0);
lean_inc(x_77);
lean_dec(x_23);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateNotDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_isEqv___redArg(x_3, x_18, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_isEqv___redArg(x_3, x_16, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_18, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_18);
x_28 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_16, x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; 
lean_free_object(x_28);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_33 = l_Lean_Meta_Grind_mkDiseqProofUsing(x_3, x_16, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Grind_propagateBoolDiseq___closed__3;
lean_inc_ref(x_3);
x_36 = l_Lean_mkAppB(x_35, x_3, x_34);
x_37 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_3, x_36, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_45 = l_Lean_Meta_Grind_mkDiseqProofUsing(x_3, x_16, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Grind_propagateBoolDiseq___closed__3;
lean_inc_ref(x_3);
x_48 = l_Lean_mkAppB(x_47, x_3, x_46);
x_49 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_3, x_48, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_28, 0);
lean_inc(x_54);
lean_dec(x_28);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_16);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_56 = l_Lean_Meta_Grind_mkDiseqProofUsing(x_3, x_18, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_Meta_Grind_propagateBoolDiseq___closed__6;
lean_inc_ref(x_3);
x_59 = l_Lean_mkAppB(x_58, x_3, x_57);
x_60 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_3, x_59, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_25, 0);
lean_inc(x_65);
lean_dec(x_25);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_18);
lean_dec_ref(x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_67 = l_Lean_Meta_Grind_mkDiseqProofUsing(x_2, x_16, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_Meta_Grind_propagateBoolDiseq___closed__3;
lean_inc_ref(x_2);
x_70 = l_Lean_mkAppB(x_69, x_2, x_68);
x_71 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_2, x_70, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_16);
lean_dec_ref(x_3);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_78 = l_Lean_Meta_Grind_mkDiseqProofUsing(x_2, x_18, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l_Lean_Meta_Grind_propagateBoolDiseq___closed__6;
lean_inc_ref(x_2);
x_81 = l_Lean_mkAppB(x_80, x_2, x_79);
x_82 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_2, x_81, x_4, x_6, x_8, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
return x_19;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_19, 0);
lean_inc(x_87);
lean_dec(x_19);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_17);
if (x_89 == 0)
{
return x_17;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_17, 0);
lean_inc(x_90);
lean_dec(x_17);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_15, 0);
lean_inc(x_93);
lean_dec(x_15);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_propagateBoolDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Grind_hasSameType(x_1, x_2, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_37 = l_Lean_Meta_Grind_hasSameType(x_3, x_4, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_62; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_62 = lean_unbox(x_36);
lean_dec(x_36);
if (x_62 == 1)
{
uint8_t x_63; 
x_63 = lean_unbox(x_38);
lean_dec(x_38);
if (x_63 == 1)
{
lean_object* x_64; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_64 = lean_grind_mk_eq_proof(x_2, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_7);
x_66 = l_Lean_Meta_mkEqTrans(x_65, x_7, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_12);
x_68 = lean_grind_mk_eq_proof(x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_70 = l_Lean_Meta_mkEqTrans(x_67, x_69, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_19 = x_71;
x_20 = x_12;
x_21 = x_14;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_70;
}
}
else
{
lean_dec(x_67);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_68;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_66;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_64;
}
}
else
{
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = x_17;
goto block_61;
}
}
else
{
lean_dec(x_38);
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = x_17;
goto block_61;
}
block_61:
{
lean_object* x_49; 
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_49 = lean_grind_mk_heq_proof(x_2, x_1, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc_ref(x_7);
x_51 = l_Lean_Meta_mkHEqOfEq(x_7, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_53 = l_Lean_Meta_mkHEqTrans(x_50, x_52, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc_ref(x_43);
x_55 = lean_grind_mk_heq_proof(x_3, x_4, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_57 = l_Lean_Meta_mkHEqTrans(x_54, x_56, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_59 = l_Lean_Meta_mkEqOfHEq(x_58, x_6, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_19 = x_60;
x_20 = x_43;
x_21 = x_45;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_59;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_57;
}
}
else
{
lean_dec(x_54);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_55;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_53;
}
}
else
{
lean_dec(x_50);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_51;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_49;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_36);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_37);
if (x_72 == 0)
{
return x_37;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_37, 0);
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_35);
if (x_75 == 0)
{
return x_35;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_35, 0);
lean_inc(x_76);
lean_dec(x_35);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
block_34:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_28 = l_Lean_Meta_mkNoConfusion(x_27, x_19, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0;
x_31 = lean_array_push(x_30, x_7);
x_32 = 1;
x_33 = l_Lean_Meta_mkLambdaFVars(x_31, x_29, x_5, x_6, x_5, x_6, x_32, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_31);
return x_33;
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
return x_28;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l_Lean_Meta_Grind_propagateEqUp___lam__0(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_12(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_9);
lean_closure_set(x_17, 5, x_10);
lean_closure_set(x_17, 6, x_11);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_17, x_5, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_2);
x_18 = lean_unbox(x_5);
x_19 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(x_1, x_17, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(x_1, x_15, x_2, x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Grind_hasSameType(x_1, x_2, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_37 = l_Lean_Meta_Grind_hasSameType(x_3, x_4, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_62; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_62 = lean_unbox(x_36);
lean_dec(x_36);
if (x_62 == 1)
{
uint8_t x_63; 
x_63 = lean_unbox(x_38);
lean_dec(x_38);
if (x_63 == 1)
{
lean_object* x_64; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_64 = lean_grind_mk_eq_proof(x_2, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_7);
x_66 = l_Lean_Meta_mkEqTrans(x_65, x_7, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_12);
x_68 = lean_grind_mk_eq_proof(x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_70 = l_Lean_Meta_mkEqTrans(x_67, x_69, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_19 = x_71;
x_20 = x_12;
x_21 = x_14;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_70;
}
}
else
{
lean_dec(x_67);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_68;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_66;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_64;
}
}
else
{
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = x_17;
goto block_61;
}
}
else
{
lean_dec(x_38);
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = x_17;
goto block_61;
}
block_61:
{
lean_object* x_49; 
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_49 = lean_grind_mk_heq_proof(x_2, x_1, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc_ref(x_7);
x_51 = l_Lean_Meta_mkHEqOfEq(x_7, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_53 = l_Lean_Meta_mkHEqTrans(x_50, x_52, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc_ref(x_43);
x_55 = lean_grind_mk_heq_proof(x_3, x_4, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_57 = l_Lean_Meta_mkHEqTrans(x_54, x_56, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_59 = l_Lean_Meta_mkEqOfHEq(x_58, x_6, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_19 = x_60;
x_20 = x_43;
x_21 = x_45;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_59;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_57;
}
}
else
{
lean_dec(x_54);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_7);
return x_55;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_53;
}
}
else
{
lean_dec(x_50);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_51;
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_49;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_36);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_37);
if (x_72 == 0)
{
return x_37;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_37, 0);
lean_inc(x_73);
lean_dec(x_37);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_35);
if (x_75 == 0)
{
return x_35;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_35, 0);
lean_inc(x_76);
lean_dec(x_35);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
block_34:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_28 = l_Lean_Meta_mkNoConfusion(x_27, x_19, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0;
x_31 = lean_array_push(x_30, x_7);
x_32 = 1;
x_33 = l_Lean_Meta_mkLambdaFVars(x_31, x_29, x_5, x_6, x_5, x_6, x_32, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_31);
return x_33;
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_7);
return x_28;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_29; lean_object* x_41; 
x_19 = lean_st_ref_get(x_8);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
lean_inc(x_20);
x_41 = l_Lean_Meta_Grind_Goal_getENode(x_19, x_20, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get_uint8(x_42, sizeof(void*)*11 + 2);
lean_dec(x_42);
x_47 = lean_box(0);
if (x_46 == 0)
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = l_Lean_Expr_getAppFn(x_55);
x_57 = l_Lean_Expr_getAppFn(x_44);
x_58 = lean_expr_eqv(x_56, x_57);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_44);
lean_inc_ref(x_55);
x_59 = l_Lean_Meta_Grind_hasSameType(x_55, x_44, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_62; 
lean_inc_ref(x_55);
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec_ref(x_2);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_1);
lean_inc_ref(x_6);
x_62 = l_Lean_Meta_mkEq(x_6, x_1, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_box(x_5);
x_65 = lean_box(x_4);
x_66 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0___boxed), 18, 6);
lean_closure_set(x_66, 0, x_6);
lean_closure_set(x_66, 1, x_55);
lean_closure_set(x_66, 2, x_1);
lean_closure_set(x_66, 3, x_44);
lean_closure_set(x_66, 4, x_64);
lean_closure_set(x_66, 5, x_65);
x_67 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4));
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_inc(x_8);
x_68 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_67, x_63, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_29 = x_68;
goto block_40;
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_44);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_29 = x_62;
goto block_40;
}
}
}
else
{
lean_dec_ref(x_44);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec_ref(x_59);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_dec(x_69);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
uint8_t x_71; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_22 = x_71;
x_23 = lean_box(0);
goto block_28;
}
}
else
{
uint8_t x_72; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
return x_59;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
}
block_54:
{
uint8_t x_49; 
x_49 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_45, x_1);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_45);
x_7 = x_50;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_45);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_20);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_41);
if (x_75 == 0)
{
return x_41;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_40:
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2;
lean_inc_ref(x_3);
x_32 = l_Lean_mkAppB(x_31, x_3, x_30);
x_33 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_3, x_32, x_8, x_10, x_12, x_14, x_15, x_16, x_17);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_22 = x_4;
x_23 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_20);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(x_1, x_2, x_3, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_29; lean_object* x_41; 
x_19 = lean_st_ref_get(x_8);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
lean_inc(x_20);
x_41 = l_Lean_Meta_Grind_Goal_getENode(x_19, x_20, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get_uint8(x_42, sizeof(void*)*11 + 2);
lean_dec(x_42);
x_47 = lean_box(0);
if (x_46 == 0)
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = l_Lean_Expr_getAppFn(x_55);
x_57 = l_Lean_Expr_getAppFn(x_44);
x_58 = lean_expr_eqv(x_56, x_57);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_44);
lean_inc_ref(x_55);
x_59 = l_Lean_Meta_Grind_hasSameType(x_55, x_44, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_62; 
lean_inc_ref(x_55);
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec_ref(x_2);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_62 = l_Lean_Meta_mkEq(x_5, x_1, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_box(x_3);
x_65 = lean_box(x_4);
x_66 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___lam__0___boxed), 18, 6);
lean_closure_set(x_66, 0, x_5);
lean_closure_set(x_66, 1, x_55);
lean_closure_set(x_66, 2, x_1);
lean_closure_set(x_66, 3, x_44);
lean_closure_set(x_66, 4, x_64);
lean_closure_set(x_66, 5, x_65);
x_67 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4));
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_inc(x_8);
x_68 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_67, x_63, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_29 = x_68;
goto block_40;
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_44);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_29 = x_62;
goto block_40;
}
}
}
else
{
lean_dec_ref(x_44);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec_ref(x_59);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_dec(x_69);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
else
{
uint8_t x_71; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_22 = x_71;
x_23 = lean_box(0);
goto block_28;
}
}
else
{
uint8_t x_72; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
return x_59;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
lean_dec_ref(x_44);
lean_dec(x_21);
x_48 = lean_box(0);
goto block_54;
}
}
block_54:
{
uint8_t x_49; 
x_49 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_45, x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_45);
x_51 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(x_1, x_2, x_6, x_4, x_3, x_5, x_50, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_45);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_20);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_41);
if (x_75 == 0)
{
return x_41;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_40:
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2;
lean_inc_ref(x_6);
x_32 = l_Lean_mkAppB(x_31, x_6, x_30);
x_33 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_6, x_32, x_8, x_10, x_12, x_14, x_15, x_16, x_17);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_22 = x_4;
x_23 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_20);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_6);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_3);
x_20 = lean_unbox(x_4);
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_st_ref_get(x_7);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
lean_inc(x_19);
x_21 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_19, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*11 + 2);
x_26 = lean_box(0);
if (x_25 == 0)
{
lean_dec(x_22);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_2);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_35 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1(x_2, x_22, x_3, x_4, x_1, x_5, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_dec(x_40);
if (lean_obj_tag(x_39) == 0)
{
lean_free_object(x_37);
lean_free_object(x_35);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_dec_ref(x_39);
lean_free_object(x_37);
lean_free_object(x_35);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_37, 1, x_19);
return x_35;
}
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_free_object(x_35);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_dec_ref(x_43);
lean_free_object(x_35);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_19);
lean_ctor_set(x_35, 0, x_46);
return x_35;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_49);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_dec_ref(x_48);
lean_dec(x_49);
x_27 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_19);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
block_33:
{
uint8_t x_28; 
x_28 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_24, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_19);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_24);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_19);
if (lean_is_scalar(x_23)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_23;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_21, 0);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_4);
x_20 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_33; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_1);
x_37 = l_Lean_Expr_cleanupAnnotations(x_1);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_39);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_77; uint8_t x_78; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_42);
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_79);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_81 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
lean_dec_ref(x_80);
if (x_82 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_83; 
lean_inc_ref(x_42);
x_83 = l_Lean_Meta_Grind_getRootENode___redArg(x_42, x_2, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc_ref(x_39);
x_85 = l_Lean_Meta_Grind_getRootENode___redArg(x_39, x_2, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_227; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get_uint8(x_84, sizeof(void*)*11 + 2);
lean_dec(x_84);
x_91 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get_uint8(x_86, sizeof(void*)*11 + 2);
lean_dec(x_86);
x_227 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_89, x_88);
if (x_227 == 0)
{
uint8_t x_228; 
x_228 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_91, x_88);
if (x_228 == 0)
{
uint8_t x_229; 
x_229 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_89, x_91);
if (x_229 == 0)
{
lean_dec(x_88);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_st_ref_get(x_2);
lean_inc_ref(x_1);
x_231 = l_Lean_Meta_Grind_Goal_getRoot(x_230, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_232, x_88);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_234 = lean_grind_mk_eq_proof(x_42, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
lean_inc_ref(x_1);
x_236 = l_Lean_Meta_mkEqTrueCore(x_1, x_235);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_237 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_88, x_236, x_233, x_2, x_4, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_237) == 0)
{
lean_dec_ref(x_237);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
else
{
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_237;
}
}
else
{
uint8_t x_238; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_238 = !lean_is_exclusive(x_234);
if (x_238 == 0)
{
return x_234;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_234, 0);
lean_inc(x_239);
lean_dec(x_234);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
}
}
else
{
lean_dec(x_88);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
}
else
{
uint8_t x_241; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_241 = !lean_is_exclusive(x_231);
if (x_241 == 0)
{
return x_231;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_231, 0);
lean_inc(x_242);
lean_dec(x_231);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_st_ref_get(x_2);
lean_inc_ref(x_1);
x_245 = l_Lean_Meta_Grind_Goal_getRoot(x_244, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_246, x_89);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_39);
x_248 = lean_grind_mk_eq_proof(x_39, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l_Lean_Meta_Grind_propagateEqUp___closed__7;
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_251 = l_Lean_mkApp3(x_250, x_42, x_39, x_249);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_42);
lean_inc_ref(x_1);
x_252 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_42, x_251, x_247, x_2, x_4, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_252) == 0)
{
lean_dec_ref(x_252);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
else
{
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_253 = !lean_is_exclusive(x_248);
if (x_253 == 0)
{
return x_248;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_248, 0);
lean_inc(x_254);
lean_dec(x_248);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
}
else
{
lean_dec(x_88);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
}
else
{
uint8_t x_256; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_256 = !lean_is_exclusive(x_245);
if (x_256 == 0)
{
return x_245;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_245, 0);
lean_inc(x_257);
lean_dec(x_245);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_st_ref_get(x_2);
lean_inc_ref(x_1);
x_260 = l_Lean_Meta_Grind_Goal_getRoot(x_259, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec_ref(x_260);
x_262 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_261, x_91);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_42);
x_263 = lean_grind_mk_eq_proof(x_42, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = l_Lean_Meta_Grind_propagateEqUp___closed__10;
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_266 = l_Lean_mkApp3(x_265, x_42, x_39, x_264);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_39);
lean_inc_ref(x_1);
x_267 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_39, x_266, x_262, x_2, x_4, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_267) == 0)
{
lean_dec_ref(x_267);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
else
{
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_267;
}
}
else
{
uint8_t x_268; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_268 = !lean_is_exclusive(x_263);
if (x_268 == 0)
{
return x_263;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_263, 0);
lean_inc(x_269);
lean_dec(x_263);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_269);
return x_270;
}
}
}
else
{
lean_dec(x_88);
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
x_132 = x_5;
x_133 = x_6;
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = lean_box(0);
goto block_226;
}
}
else
{
uint8_t x_271; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_271 = !lean_is_exclusive(x_260);
if (x_271 == 0)
{
return x_260;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_260, 0);
lean_inc(x_272);
lean_dec(x_260);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
block_128:
{
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_89, x_98);
lean_dec_ref(x_98);
lean_dec_ref(x_89);
if (x_108 == 0)
{
lean_dec_ref(x_97);
lean_dec_ref(x_91);
x_43 = x_99;
x_44 = x_100;
x_45 = x_93;
x_46 = x_94;
x_47 = x_101;
x_48 = x_102;
x_49 = x_95;
x_50 = x_96;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = lean_box(0);
x_55 = x_108;
goto block_76;
}
else
{
uint8_t x_109; 
x_109 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_91, x_97);
lean_dec_ref(x_97);
lean_dec_ref(x_91);
x_43 = x_99;
x_44 = x_100;
x_45 = x_93;
x_46 = x_94;
x_47 = x_101;
x_48 = x_102;
x_49 = x_95;
x_50 = x_96;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = lean_box(0);
x_55 = x_109;
goto block_76;
}
}
else
{
lean_object* x_110; 
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_inc(x_101);
lean_inc_ref(x_94);
lean_inc(x_95);
lean_inc_ref(x_99);
lean_inc(x_100);
lean_inc_ref(x_104);
lean_inc(x_93);
lean_inc_ref(x_105);
lean_inc(x_103);
lean_inc(x_102);
lean_inc_ref(x_42);
x_110 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_42, x_102, x_103, x_105, x_93, x_104, x_100, x_99, x_95, x_94, x_101);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_101);
lean_inc_ref(x_94);
lean_inc(x_95);
lean_inc_ref(x_99);
lean_inc_ref(x_104);
lean_inc_ref(x_105);
lean_inc(x_102);
lean_inc_ref(x_39);
x_112 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_39, x_102, x_103, x_105, x_93, x_104, x_100, x_99, x_95, x_94, x_101);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
x_115 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
x_116 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
x_117 = l_Lean_Name_mkStr4(x_114, x_115, x_96, x_116);
x_118 = lean_box(0);
x_119 = l_Lean_mkConst(x_117, x_118);
x_120 = l_Lean_mkApp4(x_119, x_42, x_39, x_111, x_113);
x_121 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_120, x_102, x_105, x_104, x_99, x_95, x_94, x_101);
lean_dec_ref(x_104);
lean_dec_ref(x_105);
lean_dec(x_102);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_111);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_112);
if (x_122 == 0)
{
return x_112;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
lean_dec(x_112);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_110);
if (x_125 == 0)
{
return x_110;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_110, 0);
lean_inc(x_126);
lean_dec(x_110);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
}
block_226:
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__0));
x_141 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
x_142 = l_Lean_Expr_isConstOf(x_79, x_141);
lean_dec_ref(x_79);
if (x_142 == 0)
{
lean_object* x_143; 
lean_inc_ref(x_1);
x_143 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_129, x_133, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_unbox(x_145);
if (x_146 == 0)
{
lean_free_object(x_143);
if (x_90 == 0)
{
lean_dec(x_145);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
else
{
if (x_92 == 0)
{
lean_dec(x_145);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Expr_getAppFn(x_89);
x_148 = l_Lean_Expr_getAppFn(x_91);
x_149 = lean_expr_eqv(x_147, x_148);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_91);
lean_inc_ref(x_89);
x_150 = l_Lean_Meta_Grind_hasSameType(x_89, x_91, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
x_153 = lean_box(0);
lean_inc_ref(x_42);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_42);
x_155 = lean_unbox(x_145);
lean_dec(x_145);
x_156 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2(x_42, x_39, x_155, x_82, x_1, x_154, x_129, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
lean_dec(x_158);
x_159 = lean_box(0);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_156);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_156);
if (x_162 == 0)
{
return x_156;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
lean_dec(x_156);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; 
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_165 = l_Lean_Meta_mkEq(x_42, x_39, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = lean_box(x_82);
x_168 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(x_168, 0, x_42);
lean_closure_set(x_168, 1, x_89);
lean_closure_set(x_168, 2, x_39);
lean_closure_set(x_168, 3, x_91);
lean_closure_set(x_168, 4, x_145);
lean_closure_set(x_168, 5, x_167);
x_169 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4));
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_133);
lean_inc_ref(x_131);
lean_inc(x_129);
x_170 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_169, x_166, x_168, x_129, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
x_17 = x_135;
x_18 = x_137;
x_19 = x_138;
x_20 = x_129;
x_21 = x_136;
x_22 = x_133;
x_23 = x_131;
x_24 = x_170;
goto block_32;
}
else
{
lean_dec(x_145);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
x_17 = x_135;
x_18 = x_137;
x_19 = x_138;
x_20 = x_129;
x_21 = x_136;
x_22 = x_133;
x_23 = x_131;
x_24 = x_165;
goto block_32;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_145);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_171 = !lean_is_exclusive(x_150);
if (x_171 == 0)
{
return x_150;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_150, 0);
lean_inc(x_172);
lean_dec(x_150);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
else
{
lean_dec(x_145);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_145);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_174 = lean_box(0);
lean_ctor_set(x_143, 0, x_174);
return x_143;
}
}
else
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_143, 0);
lean_inc(x_175);
lean_dec(x_143);
x_176 = lean_unbox(x_175);
if (x_176 == 0)
{
if (x_90 == 0)
{
lean_dec(x_175);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
else
{
if (x_92 == 0)
{
lean_dec(x_175);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = l_Lean_Expr_getAppFn(x_89);
x_178 = l_Lean_Expr_getAppFn(x_91);
x_179 = lean_expr_eqv(x_177, x_178);
lean_dec_ref(x_178);
lean_dec_ref(x_177);
if (x_179 == 0)
{
lean_object* x_180; 
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_91);
lean_inc_ref(x_89);
x_180 = l_Lean_Meta_Grind_hasSameType(x_89, x_91, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
x_183 = lean_box(0);
lean_inc_ref(x_42);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_42);
x_185 = lean_unbox(x_175);
lean_dec(x_175);
x_186 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__2(x_42, x_39, x_185, x_82, x_1, x_184, x_129, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_187 = x_186;
} else {
 lean_dec_ref(x_186);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 1, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
else
{
lean_object* x_193; 
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_193 = l_Lean_Meta_mkEq(x_42, x_39, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_box(x_82);
x_196 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(x_196, 0, x_42);
lean_closure_set(x_196, 1, x_89);
lean_closure_set(x_196, 2, x_39);
lean_closure_set(x_196, 3, x_91);
lean_closure_set(x_196, 4, x_175);
lean_closure_set(x_196, 5, x_195);
x_197 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__4));
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_133);
lean_inc_ref(x_131);
lean_inc(x_129);
x_198 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_197, x_194, x_196, x_129, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
x_17 = x_135;
x_18 = x_137;
x_19 = x_138;
x_20 = x_129;
x_21 = x_136;
x_22 = x_133;
x_23 = x_131;
x_24 = x_198;
goto block_32;
}
else
{
lean_dec(x_175);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
x_17 = x_135;
x_18 = x_137;
x_19 = x_138;
x_20 = x_129;
x_21 = x_136;
x_22 = x_133;
x_23 = x_131;
x_24 = x_193;
goto block_32;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_175);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_180, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_200 = x_180;
} else {
 lean_dec_ref(x_180);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
else
{
lean_dec(x_175);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_33 = lean_box(0);
goto block_36;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_175);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_143);
if (x_204 == 0)
{
return x_143;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_143, 0);
lean_inc(x_205);
lean_dec(x_143);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; 
lean_inc_ref(x_1);
x_207 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_129, x_133, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(x_133);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_133);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_89, x_211);
if (x_214 == 0)
{
x_93 = x_132;
x_94 = x_137;
x_95 = x_136;
x_96 = x_140;
x_97 = x_211;
x_98 = x_213;
x_99 = x_135;
x_100 = x_134;
x_101 = x_138;
x_102 = x_129;
x_103 = x_130;
x_104 = x_133;
x_105 = x_131;
x_106 = lean_box(0);
x_107 = x_214;
goto block_128;
}
else
{
uint8_t x_215; 
x_215 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_91, x_213);
x_93 = x_132;
x_94 = x_137;
x_95 = x_136;
x_96 = x_140;
x_97 = x_211;
x_98 = x_213;
x_99 = x_135;
x_100 = x_134;
x_101 = x_138;
x_102 = x_129;
x_103 = x_130;
x_104 = x_133;
x_105 = x_131;
x_106 = lean_box(0);
x_107 = x_215;
goto block_128;
}
}
else
{
uint8_t x_216; 
lean_dec(x_211);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_216 = !lean_is_exclusive(x_212);
if (x_216 == 0)
{
return x_212;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
lean_dec(x_212);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_219 = !lean_is_exclusive(x_210);
if (x_219 == 0)
{
return x_210;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_210, 0);
lean_inc(x_220);
lean_dec(x_210);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; 
lean_dec_ref(x_91);
lean_dec_ref(x_89);
x_222 = l_Lean_Meta_Grind_propagateBoolDiseq(x_1, x_42, x_39, x_129, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
return x_222;
}
}
else
{
uint8_t x_223; 
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec_ref(x_91);
lean_dec_ref(x_89);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_223 = !lean_is_exclusive(x_207);
if (x_223 == 0)
{
return x_207;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_207, 0);
lean_inc(x_224);
lean_dec(x_207);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
return x_225;
}
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_274 = !lean_is_exclusive(x_87);
if (x_274 == 0)
{
return x_87;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_87, 0);
lean_inc(x_275);
lean_dec(x_87);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_84);
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_277 = !lean_is_exclusive(x_85);
if (x_277 == 0)
{
return x_85;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_85, 0);
lean_inc(x_278);
lean_dec(x_85);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec_ref(x_79);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_280 = !lean_is_exclusive(x_83);
if (x_280 == 0)
{
return x_83;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_83, 0);
lean_inc(x_281);
lean_dec(x_83);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
}
block_76:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; 
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_49);
lean_inc_ref(x_43);
lean_inc(x_44);
lean_inc_ref(x_52);
lean_inc(x_45);
lean_inc_ref(x_53);
lean_inc(x_51);
lean_inc(x_48);
lean_inc_ref(x_42);
x_58 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_42, x_48, x_51, x_53, x_45, x_52, x_44, x_43, x_49, x_46, x_47);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_49);
lean_inc_ref(x_43);
lean_inc_ref(x_52);
lean_inc_ref(x_53);
lean_inc(x_48);
lean_inc_ref(x_39);
x_60 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_39, x_48, x_51, x_53, x_45, x_52, x_44, x_43, x_49, x_46, x_47);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
x_63 = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
x_64 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__0));
x_65 = l_Lean_Name_mkStr4(x_62, x_63, x_50, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_mkConst(x_65, x_66);
x_68 = l_Lean_mkApp4(x_67, x_42, x_39, x_59, x_61);
x_69 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_68, x_48, x_53, x_52, x_43, x_49, x_46, x_47);
lean_dec_ref(x_52);
lean_dec_ref(x_53);
lean_dec(x_48);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_59);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_60);
if (x_70 == 0)
{
return x_60;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_58);
if (x_73 == 0)
{
return x_58;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_58, 0);
lean_inc(x_74);
lean_dec(x_58);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_32:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2;
lean_inc_ref(x_1);
x_27 = l_Lean_mkAppB(x_26, x_1, x_25);
x_28 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_1, x_27, x_20, x_23, x_22, x_17, x_21, x_18, x_19);
lean_dec_ref(x_22);
lean_dec_ref(x_23);
lean_dec(x_20);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateEqUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_6);
x_20 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(x_1, x_2, x_18, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_2, x_4);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_instantiateExtTheorem(x_19, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_4, x_22);
x_4 = x_23;
x_5 = x_21;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_21; lean_object* x_25; lean_object* x_29; 
lean_inc_ref(x_1);
x_29 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc_ref(x_1);
x_32 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_free_object(x_32);
lean_inc_ref(x_1);
x_37 = l_Lean_Expr_cleanupAnnotations(x_1);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_39);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_42);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_45);
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_72 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_73 = l_Lean_Expr_isConstOf(x_71, x_72);
lean_dec_ref(x_71);
if (x_73 == 0)
{
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
x_108 = l_Lean_Expr_isConstOf(x_45, x_107);
if (x_108 == 0)
{
x_74 = x_2;
x_75 = x_3;
x_76 = x_4;
x_77 = x_5;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_10;
x_83 = x_11;
x_84 = lean_box(0);
goto block_106;
}
else
{
lean_object* x_109; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_39);
lean_inc_ref(x_42);
lean_inc_ref(x_1);
x_109 = l_Lean_Meta_Grind_propagateBoolDiseq(x_1, x_42, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_109);
x_74 = x_2;
x_75 = x_3;
x_76 = x_4;
x_77 = x_5;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_10;
x_83 = x_11;
x_84 = lean_box(0);
goto block_106;
}
else
{
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_109;
}
}
}
block_70:
{
if (x_57 == 0)
{
lean_object* x_58; 
lean_inc(x_51);
lean_inc_ref(x_52);
lean_inc(x_46);
lean_inc_ref(x_56);
x_58 = l_Lean_Meta_Grind_getExtTheorems(x_45, x_48, x_47, x_55, x_53, x_50, x_49, x_56, x_46, x_52, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
x_61 = lean_array_size(x_59);
x_62 = 0;
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(x_1, x_59, x_61, x_62, x_60, x_48, x_47, x_55, x_53, x_50, x_49, x_56, x_46, x_52, x_51);
lean_dec(x_59);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_60);
return x_63;
}
else
{
lean_object* x_66; 
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_60);
return x_66;
}
}
else
{
return x_63;
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
return x_58;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_1);
x_21 = lean_box(0);
goto block_24;
}
}
block_106:
{
lean_object* x_85; 
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc_ref(x_80);
lean_inc(x_79);
lean_inc_ref(x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc_ref(x_39);
lean_inc_ref(x_42);
x_85 = l_Lean_Meta_Grind_Solvers_propagateDiseqs(x_42, x_39, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec_ref(x_85);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc_ref(x_80);
lean_inc_ref(x_45);
x_86 = l_Lean_Meta_Grind_getExtTheorems(x_45, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Array_isEmpty___redArg(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
if (x_73 == 0)
{
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_getRootENode___redArg(x_42, x_74, x_80, x_81, x_82, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Meta_Grind_getRootENode___redArg(x_39, x_74, x_80, x_81, x_82, x_83);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
x_94 = l_Lean_Expr_isAppOf(x_45, x_93);
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec(x_90);
x_46 = x_81;
x_47 = x_75;
x_48 = x_74;
x_49 = x_79;
x_50 = x_78;
x_51 = x_83;
x_52 = x_82;
x_53 = x_77;
x_54 = lean_box(0);
x_55 = x_76;
x_56 = x_80;
x_57 = x_94;
goto block_70;
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_90, sizeof(void*)*11 + 2);
lean_dec(x_90);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_ctor_get_uint8(x_92, sizeof(void*)*11 + 2);
lean_dec(x_92);
x_46 = x_81;
x_47 = x_75;
x_48 = x_74;
x_49 = x_79;
x_50 = x_78;
x_51 = x_83;
x_52 = x_82;
x_53 = x_77;
x_54 = lean_box(0);
x_55 = x_76;
x_56 = x_80;
x_57 = x_96;
goto block_70;
}
else
{
lean_dec(x_92);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_1);
x_21 = lean_box(0);
goto block_24;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_90);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_1);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
return x_91;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_100 = !lean_is_exclusive(x_89);
if (x_100 == 0)
{
return x_89;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_89, 0);
lean_inc(x_101);
lean_dec(x_89);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
else
{
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
}
else
{
uint8_t x_103; 
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_86);
if (x_103 == 0)
{
return x_86;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
lean_dec(x_86);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_45);
lean_dec_ref(x_42);
lean_dec_ref(x_39);
lean_dec_ref(x_1);
return x_85;
}
}
}
}
}
}
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_32, 0);
lean_inc(x_110);
lean_dec(x_32);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_114; uint8_t x_115; 
lean_inc_ref(x_1);
x_114 = l_Lean_Expr_cleanupAnnotations(x_1);
x_115 = l_Lean_Expr_isApp(x_114);
if (x_115 == 0)
{
lean_dec_ref(x_114);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_116);
x_117 = l_Lean_Expr_appFnCleanup___redArg(x_114);
x_118 = l_Lean_Expr_isApp(x_117);
if (x_118 == 0)
{
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_119);
x_120 = l_Lean_Expr_appFnCleanup___redArg(x_117);
x_121 = l_Lean_Expr_isApp(x_120);
if (x_121 == 0)
{
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_122 = lean_ctor_get(x_120, 1);
lean_inc_ref(x_122);
x_147 = l_Lean_Expr_appFnCleanup___redArg(x_120);
x_148 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_149 = l_Lean_Expr_isConstOf(x_147, x_148);
lean_dec_ref(x_147);
if (x_149 == 0)
{
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
x_184 = l_Lean_Expr_isConstOf(x_122, x_183);
if (x_184 == 0)
{
x_150 = x_2;
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_10;
x_159 = x_11;
x_160 = lean_box(0);
goto block_182;
}
else
{
lean_object* x_185; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_116);
lean_inc_ref(x_119);
lean_inc_ref(x_1);
x_185 = l_Lean_Meta_Grind_propagateBoolDiseq(x_1, x_119, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_185);
x_150 = x_2;
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_10;
x_159 = x_11;
x_160 = lean_box(0);
goto block_182;
}
else
{
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_185;
}
}
}
block_146:
{
if (x_134 == 0)
{
lean_object* x_135; 
lean_inc(x_128);
lean_inc_ref(x_129);
lean_inc(x_123);
lean_inc_ref(x_133);
x_135 = l_Lean_Meta_Grind_getExtTheorems(x_122, x_125, x_124, x_132, x_130, x_127, x_126, x_133, x_123, x_129, x_128);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_box(0);
x_138 = lean_array_size(x_136);
x_139 = 0;
x_140 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(x_1, x_136, x_138, x_139, x_137, x_125, x_124, x_132, x_130, x_127, x_126, x_133, x_123, x_129, x_128);
lean_dec(x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_141 = x_140;
} else {
 lean_dec_ref(x_140);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_137);
return x_142;
}
else
{
return x_140;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_1);
x_21 = lean_box(0);
goto block_24;
}
}
block_182:
{
lean_object* x_161; 
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc_ref(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc_ref(x_116);
lean_inc_ref(x_119);
x_161 = l_Lean_Meta_Grind_Solvers_propagateDiseqs(x_119, x_116, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
lean_dec_ref(x_161);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc_ref(x_156);
lean_inc_ref(x_122);
x_162 = l_Lean_Meta_Grind_getExtTheorems(x_122, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = l_Array_isEmpty___redArg(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
if (x_149 == 0)
{
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_165; 
x_165 = l_Lean_Meta_Grind_getRootENode___redArg(x_119, x_150, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = l_Lean_Meta_Grind_getRootENode___redArg(x_116, x_150, x_156, x_157, x_158, x_159);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
x_170 = l_Lean_Expr_isAppOf(x_122, x_169);
if (x_170 == 0)
{
lean_dec(x_168);
lean_dec(x_166);
x_123 = x_157;
x_124 = x_151;
x_125 = x_150;
x_126 = x_155;
x_127 = x_154;
x_128 = x_159;
x_129 = x_158;
x_130 = x_153;
x_131 = lean_box(0);
x_132 = x_152;
x_133 = x_156;
x_134 = x_170;
goto block_146;
}
else
{
uint8_t x_171; 
x_171 = lean_ctor_get_uint8(x_166, sizeof(void*)*11 + 2);
lean_dec(x_166);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = lean_ctor_get_uint8(x_168, sizeof(void*)*11 + 2);
lean_dec(x_168);
x_123 = x_157;
x_124 = x_151;
x_125 = x_150;
x_126 = x_155;
x_127 = x_154;
x_128 = x_159;
x_129 = x_158;
x_130 = x_153;
x_131 = lean_box(0);
x_132 = x_152;
x_133 = x_156;
x_134 = x_172;
goto block_146;
}
else
{
lean_dec(x_168);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_1);
x_21 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_166);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_1);
x_173 = lean_ctor_get(x_167, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec_ref(x_1);
x_176 = lean_ctor_get(x_165, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_177 = x_165;
} else {
 lean_dec_ref(x_165);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
}
else
{
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec_ref(x_1);
x_17 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_162, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_180 = x_162;
} else {
 lean_dec_ref(x_162);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_122);
lean_dec_ref(x_119);
lean_dec_ref(x_116);
lean_dec_ref(x_1);
return x_161;
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
uint8_t x_186; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_186 = !lean_is_exclusive(x_32);
if (x_186 == 0)
{
return x_32;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_32, 0);
lean_inc(x_187);
lean_dec(x_32);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; uint8_t x_190; 
lean_inc_ref(x_1);
x_189 = l_Lean_Expr_cleanupAnnotations(x_1);
x_190 = l_Lean_Expr_isApp(x_189);
if (x_190 == 0)
{
lean_dec_ref(x_189);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_191);
x_192 = l_Lean_Expr_appFnCleanup___redArg(x_189);
x_193 = l_Lean_Expr_isApp(x_192);
if (x_193 == 0)
{
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_192, 1);
lean_inc_ref(x_194);
x_195 = l_Lean_Expr_appFnCleanup___redArg(x_192);
x_196 = l_Lean_Expr_isApp(x_195);
if (x_196 == 0)
{
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = l_Lean_Expr_appFnCleanup___redArg(x_195);
x_198 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_199 = l_Lean_Expr_isConstOf(x_197, x_198);
lean_dec_ref(x_197);
if (x_199 == 0)
{
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_200; 
x_200 = l_Lean_Meta_Grind_isEqv___redArg(x_194, x_191, x_2);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_unbox(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_free_object(x_200);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_204 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_205);
x_207 = lean_unbox(x_202);
lean_dec(x_202);
x_208 = l_Lean_Meta_Grind_pushEqCore___redArg(x_194, x_191, x_206, x_207, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_208;
}
else
{
uint8_t x_209; 
lean_dec(x_202);
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_209 = !lean_is_exclusive(x_204);
if (x_209 == 0)
{
return x_204;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
lean_dec(x_204);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; 
lean_dec(x_202);
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_212 = lean_box(0);
lean_ctor_set(x_200, 0, x_212);
return x_200;
}
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_200, 0);
lean_inc(x_213);
lean_dec(x_200);
x_214 = lean_unbox(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_215 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_216);
x_218 = lean_unbox(x_213);
lean_dec(x_213);
x_219 = l_Lean_Meta_Grind_pushEqCore___redArg(x_194, x_191, x_217, x_218, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_213);
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_221 = x_215;
} else {
 lean_dec_ref(x_215);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_213);
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec_ref(x_194);
lean_dec_ref(x_191);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_200);
if (x_225 == 0)
{
return x_200;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_200, 0);
lean_inc(x_226);
lean_dec(x_200);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
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
uint8_t x_228; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_228 = !lean_is_exclusive(x_29);
if (x_228 == 0)
{
return x_29;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_29, 0);
lean_inc(x_229);
lean_dec(x_29);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateEqDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1));
x_10 = l_Lean_mkConst(x_9, x_1);
x_11 = l_Lean_mkAppB(x_10, x_2, x_3);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_synthInstance_x3f(x_11, x_12, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Grind_isEqv___redArg(x_22, x_19, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_36 = l_Lean_Meta_Grind_mkDiseqProof_x3f(x_22, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_40 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
x_45 = l_Lean_mkConst(x_44, x_34);
x_46 = l_Lean_mkApp6(x_45, x_28, x_25, x_43, x_22, x_19, x_39);
x_47 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_46, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
x_52 = l_Lean_mkConst(x_51, x_34);
x_53 = l_Lean_mkApp6(x_52, x_28, x_25, x_50, x_22, x_19, x_39);
x_54 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_53, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_40);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = lean_box(0);
lean_ctor_set(x_36, 0, x_60);
return x_36;
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
lean_dec(x_36);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_63 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
x_68 = l_Lean_mkConst(x_67, x_34);
x_69 = l_Lean_mkApp6(x_68, x_28, x_25, x_66, x_22, x_19, x_62);
x_70 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_69, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_62);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_61);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_36);
if (x_78 == 0)
{
return x_36;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_36, 0);
lean_inc(x_79);
lean_dec(x_36);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_81 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_84; lean_object* x_85; 
lean_free_object(x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_85 = lean_grind_mk_eq_proof(x_22, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
x_88 = l_Lean_mkConst(x_87, x_34);
x_89 = l_Lean_mkApp6(x_88, x_28, x_25, x_84, x_22, x_19, x_86);
x_90 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_89, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_84);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
return x_85;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
lean_dec(x_85);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_83);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_94 = lean_box(0);
lean_ctor_set(x_81, 0, x_94);
return x_81;
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_81, 0);
lean_inc(x_95);
lean_dec(x_81);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_97 = lean_grind_mk_eq_proof(x_22, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
x_100 = l_Lean_mkConst(x_99, x_34);
x_101 = l_Lean_mkApp6(x_100, x_28, x_25, x_96, x_22, x_19, x_98);
x_102 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_101, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_95);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_108 = !lean_is_exclusive(x_81);
if (x_108 == 0)
{
return x_81;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_81, 0);
lean_inc(x_109);
lean_dec(x_81);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_111 = !lean_is_exclusive(x_32);
if (x_111 == 0)
{
return x_32;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_32, 0);
lean_inc(x_112);
lean_dec(x_32);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBEqUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; 
lean_inc_ref(x_1);
x_32 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc_ref(x_1);
x_36 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; 
lean_free_object(x_36);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_41 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_46 = lean_box(0);
x_47 = l_List_head_x21___redArg(x_46, x_34);
x_48 = l_Lean_Level_succ___override(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_mkConst(x_45, x_50);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
lean_inc_ref(x_28);
x_52 = l_Lean_mkApp3(x_51, x_28, x_22, x_19);
x_53 = l_Lean_Meta_Sym_shareCommon___redArg(x_52, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Meta_Grind_getGeneration___redArg(x_22, x_2);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_54);
x_58 = lean_grind_internalize(x_54, x_56, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec_ref(x_58);
x_59 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_61 = lean_grind_mk_eq_proof(x_1, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
x_64 = l_Lean_mkConst(x_63, x_34);
x_65 = l_Lean_mkApp6(x_64, x_28, x_25, x_44, x_22, x_19, x_62);
x_66 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_54, x_65, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_54);
lean_dec(x_44);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_54);
lean_dec(x_44);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_59);
if (x_70 == 0)
{
return x_59;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
lean_dec(x_59);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_44);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_58;
}
}
else
{
uint8_t x_73; 
lean_dec(x_54);
lean_dec(x_44);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
lean_dec(x_55);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_44);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_53);
if (x_76 == 0)
{
return x_53;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_53, 0);
lean_inc(x_77);
lean_dec(x_53);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_43);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_79 = lean_box(0);
lean_ctor_set(x_41, 0, x_79);
return x_41;
}
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_41, 0);
lean_inc(x_80);
lean_dec(x_41);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_83 = lean_box(0);
x_84 = l_List_head_x21___redArg(x_83, x_34);
x_85 = l_Lean_Level_succ___override(x_84);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_mkConst(x_82, x_87);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
lean_inc_ref(x_28);
x_89 = l_Lean_mkApp3(x_88, x_28, x_22, x_19);
x_90 = l_Lean_Meta_Sym_shareCommon___redArg(x_89, x_7);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l_Lean_Meta_Grind_getGeneration___redArg(x_22, x_2);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_91);
x_95 = lean_grind_internalize(x_91, x_93, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_dec_ref(x_95);
x_96 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_6);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_98 = lean_grind_mk_eq_proof(x_1, x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
x_101 = l_Lean_mkConst(x_100, x_34);
x_102 = l_Lean_mkApp6(x_101, x_28, x_25, x_81, x_22, x_19, x_99);
x_103 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_91, x_102, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_96, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_108 = x_96;
} else {
 lean_dec_ref(x_96);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
else
{
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_95;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_92, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_111 = x_92;
} else {
 lean_dec_ref(x_92);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_81);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_113 = lean_ctor_get(x_90, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_114 = x_90;
} else {
 lean_dec_ref(x_90);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_80);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_41);
if (x_118 == 0)
{
return x_41;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_41, 0);
lean_inc(x_119);
lean_dec(x_41);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_36, 0);
lean_inc(x_121);
lean_dec(x_36);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_125 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
x_130 = lean_box(0);
x_131 = l_List_head_x21___redArg(x_130, x_34);
x_132 = l_Lean_Level_succ___override(x_131);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_mkConst(x_129, x_134);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
lean_inc_ref(x_28);
x_136 = l_Lean_mkApp3(x_135, x_28, x_22, x_19);
x_137 = l_Lean_Meta_Sym_shareCommon___redArg(x_136, x_7);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Meta_Grind_getGeneration___redArg(x_22, x_2);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_138);
x_142 = lean_grind_internalize(x_138, x_140, x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec_ref(x_142);
x_143 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_6);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_145 = lean_grind_mk_eq_proof(x_1, x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
x_148 = l_Lean_mkConst(x_147, x_34);
x_149 = l_Lean_mkApp6(x_148, x_28, x_25, x_128, x_22, x_19, x_146);
x_150 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_138, x_149, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_138);
lean_dec(x_128);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_138);
lean_dec(x_128);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_154 = lean_ctor_get(x_143, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_155 = x_143;
} else {
 lean_dec_ref(x_143);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
return x_156;
}
}
else
{
lean_dec(x_138);
lean_dec(x_128);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_142;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_138);
lean_dec(x_128);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_139, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_158 = x_139;
} else {
 lean_dec_ref(x_139);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_128);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_160 = lean_ctor_get(x_137, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_161 = x_137;
} else {
 lean_dec_ref(x_137);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_126);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_163 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_127;
}
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_125, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_166 = x_125;
} else {
 lean_dec_ref(x_125);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
return x_167;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_168 = !lean_is_exclusive(x_36);
if (x_168 == 0)
{
return x_36;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_36, 0);
lean_inc(x_169);
lean_dec(x_36);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_25);
lean_inc_ref(x_28);
lean_inc(x_34);
x_171 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(x_34, x_28, x_25, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_171, 0);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; lean_object* x_175; 
lean_free_object(x_171);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(x_6);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
x_177 = lean_grind_mk_eq_proof(x_1, x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
x_180 = l_Lean_mkConst(x_179, x_34);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_181 = l_Lean_mkApp6(x_180, x_28, x_25, x_174, x_22, x_19, x_178);
x_182 = 0;
x_183 = l_Lean_Meta_Grind_pushEqCore___redArg(x_22, x_19, x_181, x_182, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_183;
}
else
{
uint8_t x_184; 
lean_dec(x_174);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_177);
if (x_184 == 0)
{
return x_177;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_177, 0);
lean_inc(x_185);
lean_dec(x_177);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_174);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_187 = !lean_is_exclusive(x_175);
if (x_187 == 0)
{
return x_175;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_175, 0);
lean_inc(x_188);
lean_dec(x_175);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; 
lean_dec(x_173);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_190 = lean_box(0);
lean_ctor_set(x_171, 0, x_190);
return x_171;
}
}
else
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_171, 0);
lean_inc(x_191);
lean_dec(x_171);
if (lean_obj_tag(x_191) == 1)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(x_6);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
x_195 = lean_grind_mk_eq_proof(x_1, x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
x_197 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
x_198 = l_Lean_mkConst(x_197, x_34);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_199 = l_Lean_mkApp6(x_198, x_28, x_25, x_192, x_22, x_19, x_196);
x_200 = 0;
x_201 = l_Lean_Meta_Grind_pushEqCore___redArg(x_22, x_19, x_199, x_200, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_192);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_203 = x_195;
} else {
 lean_dec_ref(x_195);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_192);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_193, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_206 = x_193;
} else {
 lean_dec_ref(x_193);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_191);
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_34);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_210 = !lean_is_exclusive(x_171);
if (x_210 == 0)
{
return x_171;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_171, 0);
lean_inc(x_211);
lean_dec(x_171);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_32);
if (x_213 == 0)
{
return x_32;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_32, 0);
lean_inc(x_214);
lean_dec(x_32);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBEqDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_38);
x_40 = 0;
x_41 = l_Lean_Meta_Grind_pushEqCore___redArg(x_30, x_27, x_39, x_40, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_36;
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
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_inc_ref(x_1);
x_49 = l_Lean_Expr_cleanupAnnotations(x_1);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_51);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_57);
x_58 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_54);
lean_dec_ref(x_51);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_61 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
x_62 = l_Lean_Expr_isConstOf(x_60, x_61);
lean_dec_ref(x_60);
if (x_62 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_54);
lean_dec_ref(x_51);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_64 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_65);
x_67 = 0;
x_68 = l_Lean_Meta_Grind_pushEqCore___redArg(x_57, x_54, x_66, x_67, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_57);
lean_dec_ref(x_54);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
else
{
lean_dec_ref(x_57);
lean_dec_ref(x_54);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_63;
}
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
uint8_t x_72; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_17);
if (x_72 == 0)
{
return x_17;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_17, 0);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateEqMatchDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_35; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_36);
x_38 = l_Lean_Meta_Grind_pushEqCore___redArg(x_29, x_24, x_37, x_34, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_29);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
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
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Expr_cleanupAnnotations(x_1);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_52 = l_Lean_Expr_isApp(x_51);
if (x_52 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_53);
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_55 = l_Lean_Expr_isApp(x_54);
if (x_55 == 0)
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_Expr_appFnCleanup___redArg(x_54);
x_57 = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
x_58 = l_Lean_Expr_isConstOf(x_56, x_57);
lean_dec_ref(x_56);
if (x_58 == 0)
{
lean_dec_ref(x_53);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_59; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_59 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_60);
x_62 = l_Lean_Meta_Grind_pushEqCore___redArg(x_53, x_48, x_61, x_58, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_53);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
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
uint8_t x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_17);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateHEqDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_isEqv___redArg(x_24, x_19, x_2);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; 
lean_free_object(x_30);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_35 = lean_grind_mk_heq_proof(x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_mkEqTrueCore(x_1, x_36);
x_38 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_37, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_46 = lean_grind_mk_heq_proof(x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc_ref(x_1);
x_48 = l_Lean_Meta_mkEqTrueCore(x_1, x_47);
x_49 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_48, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateHEqUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_2);
x_18 = lean_nat_dec_lt(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_5);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_Grind_preprocessLight(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc(x_20);
x_24 = lean_grind_internalize(x_20, x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_20, x_4, x_18, x_6, x_8, x_12, x_13, x_14, x_15);
lean_dec_ref(x_8);
lean_dec(x_6);
return x_25;
}
else
{
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_24;
}
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fget_borrowed(x_2, x_5);
lean_inc(x_32);
x_33 = l_Lean_Expr_app___override(x_3, x_32);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_32);
x_34 = l_Lean_Meta_mkCongrFun(x_4, x_32, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_5, x_36);
lean_dec(x_5);
x_3 = x_33;
x_4 = x_35;
x_5 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_33);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_4);
x_20 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_2);
x_23 = lean_grind_internalize(x_2, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = 0;
x_25 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_2, x_3, x_24, x_6, x_8, x_12, x_13, x_14, x_15);
lean_dec_ref(x_8);
lean_dec(x_6);
return x_25;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_5);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateIte___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
x_18 = lean_nat_sub(x_17, x_16);
x_19 = l_Lean_Expr_getRevArg_x21(x_1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_Meta_Grind_isEqTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc_ref(x_19);
x_23 = l_Lean_Meta_Grind_isEqFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; 
lean_free_object(x_23);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_getAppFn(x_1);
x_31 = l_Lean_instInhabitedExpr;
x_32 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_33 = lean_mk_array(x_13, x_32);
lean_inc_ref(x_1);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_17);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_array_get(x_31, x_34, x_35);
x_37 = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
x_38 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_39 = l_Lean_mkConst(x_37, x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_mkAppRange(x_39, x_40, x_14, x_34);
x_42 = l_Lean_Expr_app___override(x_41, x_29);
x_43 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_36, x_42, x_14, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_34);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Expr_getAppFn(x_1);
x_54 = l_Lean_instInhabitedExpr;
x_55 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_56 = lean_mk_array(x_13, x_55);
lean_inc_ref(x_1);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_56, x_17);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_array_get(x_54, x_57, x_58);
x_60 = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
x_61 = l_Lean_Expr_constLevels_x21(x_53);
lean_dec_ref(x_53);
x_62 = l_Lean_mkConst(x_60, x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_mkAppRange(x_62, x_63, x_14, x_57);
x_65 = l_Lean_Expr_app___override(x_64, x_52);
x_66 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_59, x_65, x_14, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_57);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_68 = x_51;
} else {
 lean_dec_ref(x_51);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_23);
if (x_70 == 0)
{
return x_23;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_23, 0);
lean_inc(x_71);
lean_dec(x_23);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Expr_getAppFn(x_1);
x_76 = l_Lean_instInhabitedExpr;
x_77 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_78 = lean_mk_array(x_13, x_77);
lean_inc_ref(x_1);
x_79 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_78, x_17);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_array_get(x_76, x_79, x_80);
x_82 = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__4));
x_83 = l_Lean_Expr_constLevels_x21(x_75);
lean_dec_ref(x_75);
x_84 = l_Lean_mkConst(x_82, x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_mkAppRange(x_84, x_85, x_14, x_79);
x_87 = l_Lean_Expr_app___override(x_86, x_74);
x_88 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_81, x_87, x_14, x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_79);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_73);
if (x_89 == 0)
{
return x_73;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
lean_dec(x_73);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_20);
if (x_92 == 0)
{
return x_20;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
lean_dec(x_20);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
x_18 = lean_nat_sub(x_17, x_16);
x_19 = l_Lean_Expr_getRevArg_x21(x_1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_Meta_Grind_isEqTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc_ref(x_19);
x_23 = l_Lean_Meta_Grind_isEqFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; 
lean_free_object(x_23);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_28 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_getAppFn(x_1);
x_31 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_32 = lean_mk_array(x_13, x_31);
lean_inc_ref(x_1);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_32, x_17);
x_34 = l_Lean_instInhabitedExpr;
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_array_get(x_34, x_33, x_35);
lean_inc(x_29);
x_37 = l_Lean_Meta_mkOfEqFalseCore(x_19, x_29);
x_38 = l_Lean_Expr_app___override(x_36, x_37);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = lean_grind_preprocess(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_42 = l_Lean_Meta_Simp_Result_getProof(x_40, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
x_45 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_46 = l_Lean_mkConst(x_44, x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_mkAppRange(x_46, x_47, x_14, x_33);
lean_inc_ref(x_41);
x_49 = l_Lean_mkApp3(x_48, x_41, x_29, x_43);
x_50 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_41, x_49, x_14, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_33);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec_ref(x_41);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_39, 0);
lean_inc(x_55);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_28);
if (x_57 == 0)
{
return x_28;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_28, 0);
lean_inc(x_58);
lean_dec(x_28);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_23, 0);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_64 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Expr_getAppFn(x_1);
x_67 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_68 = lean_mk_array(x_13, x_67);
lean_inc_ref(x_1);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_68, x_17);
x_70 = l_Lean_instInhabitedExpr;
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_array_get(x_70, x_69, x_71);
lean_inc(x_65);
x_73 = l_Lean_Meta_mkOfEqFalseCore(x_19, x_65);
x_74 = l_Lean_Expr_app___override(x_72, x_73);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_75 = lean_grind_preprocess(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_77);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_78 = l_Lean_Meta_Simp_Result_getProof(x_76, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
x_81 = l_Lean_Expr_constLevels_x21(x_66);
lean_dec_ref(x_66);
x_82 = l_Lean_mkConst(x_80, x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_mkAppRange(x_82, x_83, x_14, x_69);
lean_inc_ref(x_77);
x_85 = l_Lean_mkApp3(x_84, x_77, x_65, x_79);
x_86 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_77, x_85, x_14, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_69);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_77);
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_75, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_91 = x_75;
} else {
 lean_dec_ref(x_75);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_64, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_94 = x_64;
} else {
 lean_dec_ref(x_64);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_23, 0);
lean_inc(x_97);
lean_dec(x_23);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_99 = l_Lean_Meta_Grind_mkEqTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l_Lean_Expr_getAppFn(x_1);
x_102 = l_Lean_Meta_Grind_propagateIte___closed__0;
x_103 = lean_mk_array(x_13, x_102);
lean_inc_ref(x_1);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_17);
x_105 = l_Lean_instInhabitedExpr;
x_106 = lean_unsigned_to_nat(3u);
x_107 = lean_array_get(x_105, x_104, x_106);
lean_inc(x_100);
x_108 = l_Lean_Meta_mkOfEqTrueCore(x_19, x_100);
x_109 = l_Lean_Expr_app___override(x_107, x_108);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_110 = lean_grind_preprocess(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_112);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_113 = l_Lean_Meta_Simp_Result_getProof(x_111, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__3));
x_116 = l_Lean_Expr_constLevels_x21(x_101);
lean_dec_ref(x_101);
x_117 = l_Lean_mkConst(x_115, x_116);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_mkAppRange(x_117, x_118, x_14, x_104);
lean_inc_ref(x_112);
x_120 = l_Lean_mkApp3(x_119, x_112, x_100, x_114);
x_121 = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(x_1, x_112, x_120, x_14, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_104);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec_ref(x_112);
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_113);
if (x_122 == 0)
{
return x_113;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
lean_dec(x_113);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_110);
if (x_125 == 0)
{
return x_110;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_110, 0);
lean_inc(x_126);
lean_dec(x_110);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_99);
if (x_128 == 0)
{
return x_99;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_99, 0);
lean_inc(x_129);
lean_dec(x_99);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_131 = !lean_is_exclusive(x_20);
if (x_131 == 0)
{
return x_20;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_20, 0);
lean_inc(x_132);
lean_dec(x_20);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_22);
lean_dec(x_19);
lean_inc_ref(x_1);
x_23 = l_Lean_Expr_cleanupAnnotations(x_1);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_free_object(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_free_object(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
lean_dec_ref(x_29);
if (x_31 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_free_object(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
x_33 = l_Lean_Expr_isConstOf(x_22, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
x_35 = l_Lean_Expr_isConstOf(x_22, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = lean_box(0);
lean_ctor_set(x_17, 0, x_36);
return x_17;
}
else
{
lean_object* x_37; 
lean_free_object(x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_37 = lean_grind_mk_eq_proof(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Meta_Grind_propagateDecideDown___closed__9;
lean_inc_ref(x_28);
x_40 = l_Lean_mkApp3(x_39, x_28, x_25, x_38);
x_41 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_28, x_40, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
lean_free_object(x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_45 = lean_grind_mk_eq_proof(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Grind_propagateDecideDown___closed__12;
lean_inc_ref(x_28);
x_48 = l_Lean_mkApp3(x_47, x_28, x_25, x_46);
x_49 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_28, x_48, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
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
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_17, 0);
lean_inc(x_53);
lean_dec(x_17);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*11 + 2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_57);
lean_dec(x_53);
lean_inc_ref(x_1);
x_58 = l_Lean_Expr_cleanupAnnotations(x_1);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_57);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_65 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
x_66 = l_Lean_Expr_isConstOf(x_64, x_65);
lean_dec_ref(x_64);
if (x_66 == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_dec_ref(x_57);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
x_68 = l_Lean_Expr_isConstOf(x_57, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
x_70 = l_Lean_Expr_isConstOf(x_57, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_dec_ref(x_57);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_73 = lean_grind_mk_eq_proof(x_1, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Meta_Grind_propagateDecideDown___closed__9;
lean_inc_ref(x_63);
x_76 = l_Lean_mkApp3(x_75, x_63, x_60, x_74);
x_77 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_63, x_76, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_81 = lean_grind_mk_eq_proof(x_1, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Meta_Grind_propagateDecideDown___closed__12;
lean_inc_ref(x_63);
x_84 = l_Lean_mkApp3(x_83, x_63, x_60, x_82);
x_85 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_63, x_84, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
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
uint8_t x_89; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_17);
if (x_89 == 0)
{
return x_17;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_17, 0);
lean_inc(x_90);
lean_dec(x_17);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateDecideDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_22);
x_29 = l_Lean_Meta_Grind_isEqFalse___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
x_34 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_36 = l_Lean_Meta_Grind_mkEqFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_Meta_Grind_propagateDecideUp___closed__2;
x_39 = l_Lean_mkApp3(x_38, x_22, x_19, x_37);
x_40 = lean_unbox(x_27);
lean_dec(x_27);
x_41 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_35, x_39, x_40, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_35);
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_54 = l_Lean_Meta_Grind_mkEqFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_Meta_Grind_propagateDecideUp___closed__2;
x_57 = l_Lean_mkApp3(x_56, x_22, x_19, x_55);
x_58 = lean_unbox(x_27);
lean_dec(x_27);
x_59 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_53, x_57, x_58, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
return x_29;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_29, 0);
lean_inc(x_67);
lean_dec(x_29);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_27);
x_69 = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_71 = l_Lean_Meta_Grind_mkEqTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Meta_Grind_propagateDecideUp___closed__5;
x_74 = l_Lean_mkApp3(x_73, x_22, x_19, x_72);
x_75 = 0;
x_76 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_70, x_74, x_75, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_70);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
return x_26;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_26, 0);
lean_inc(x_84);
lean_dec(x_26);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateDecideUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_19);
x_29 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_inc_ref(x_22);
x_32 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc_ref(x_19);
x_35 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; 
lean_free_object(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_40 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Grind_propagateBoolAndUp___closed__3;
x_43 = l_Lean_mkApp3(x_42, x_22, x_19, x_41);
x_44 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_43, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_52 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_propagateBoolAndUp___closed__3;
x_55 = l_Lean_mkApp3(x_54, x_22, x_19, x_53);
x_56 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_55, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_63 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_propagateBoolAndUp___closed__5;
x_66 = l_Lean_mkApp3(x_65, x_22, x_19, x_64);
x_67 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_66, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_74 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_propagateBoolAndUp___closed__7;
lean_inc_ref(x_22);
x_77 = l_Lean_mkApp3(x_76, x_22, x_19, x_75);
x_78 = lean_unbox(x_27);
lean_dec(x_27);
x_79 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_22, x_77, x_78, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
return x_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_27);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_86 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Grind_propagateBoolAndUp___closed__9;
lean_inc_ref(x_19);
x_89 = l_Lean_mkApp3(x_88, x_22, x_19, x_87);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_19, x_89, x_90, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
return x_26;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
lean_dec(x_26);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolAndUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_31 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Grind_propagateBoolAndDown___closed__1;
lean_inc(x_32);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_34 = l_Lean_mkApp3(x_33, x_27, x_24, x_32);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_27);
x_35 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_27, x_34, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_35);
x_36 = l_Lean_Meta_Grind_propagateBoolAndDown___closed__3;
lean_inc_ref(x_24);
x_37 = l_Lean_mkApp3(x_36, x_27, x_24, x_32);
x_38 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_24, x_37, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_35;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Expr_cleanupAnnotations(x_1);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec_ref(x_52);
if (x_54 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_55; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_propagateBoolAndDown___closed__1;
lean_inc(x_56);
lean_inc_ref(x_48);
lean_inc_ref(x_51);
x_58 = l_Lean_mkApp3(x_57, x_51, x_48, x_56);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_51);
x_59 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_51, x_58, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_59);
x_60 = l_Lean_Meta_Grind_propagateBoolAndDown___closed__3;
lean_inc_ref(x_48);
x_61 = l_Lean_mkApp3(x_60, x_51, x_48, x_56);
x_62 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_48, x_61, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_62;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_17);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolAndDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_22);
x_26 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_19);
x_29 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_inc_ref(x_22);
x_32 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_22, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc_ref(x_19);
x_35 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; 
lean_free_object(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_40 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Meta_Grind_propagateBoolOrUp___closed__3;
x_43 = l_Lean_mkApp3(x_42, x_22, x_19, x_41);
x_44 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_43, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_52 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_propagateBoolOrUp___closed__3;
x_55 = l_Lean_mkApp3(x_54, x_22, x_19, x_53);
x_56 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_55, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_63 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_propagateBoolOrUp___closed__5;
x_66 = l_Lean_mkApp3(x_65, x_22, x_19, x_64);
x_67 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_66, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_74 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_propagateBoolOrUp___closed__7;
lean_inc_ref(x_22);
x_77 = l_Lean_mkApp3(x_76, x_22, x_19, x_75);
x_78 = lean_unbox(x_27);
lean_dec(x_27);
x_79 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_22, x_77, x_78, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
return x_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_29);
if (x_83 == 0)
{
return x_29;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_29, 0);
lean_inc(x_84);
lean_dec(x_29);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_27);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_22);
x_86 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Grind_propagateBoolOrUp___closed__9;
lean_inc_ref(x_19);
x_89 = l_Lean_mkApp3(x_88, x_22, x_19, x_87);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_19, x_89, x_90, x_2, x_4, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
return x_26;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
lean_dec(x_26);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolOrUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_inc_ref(x_1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_1);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_31 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Grind_propagateBoolOrDown___closed__1;
lean_inc(x_32);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_34 = l_Lean_mkApp3(x_33, x_27, x_24, x_32);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_27);
x_35 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_27, x_34, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_35);
x_36 = l_Lean_Meta_Grind_propagateBoolOrDown___closed__3;
lean_inc_ref(x_24);
x_37 = l_Lean_mkApp3(x_36, x_27, x_24, x_32);
x_38 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_24, x_37, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_38;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_35;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Expr_cleanupAnnotations(x_1);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_51);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec_ref(x_52);
if (x_54 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_55; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Meta_Grind_propagateBoolOrDown___closed__1;
lean_inc(x_56);
lean_inc_ref(x_48);
lean_inc_ref(x_51);
x_58 = l_Lean_mkApp3(x_57, x_51, x_48, x_56);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_51);
x_59 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_51, x_58, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_59);
x_60 = l_Lean_Meta_Grind_propagateBoolOrDown___closed__3;
lean_inc_ref(x_48);
x_61 = l_Lean_mkApp3(x_60, x_51, x_48, x_56);
x_62 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_48, x_61, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_62;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_17);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolOrDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_19);
x_23 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_19);
x_26 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_19, x_2, x_6, x_8, x_9, x_10, x_11);
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
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_19, x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_34 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
x_37 = l_Lean_mkAppB(x_36, x_19, x_35);
x_38 = l_Lean_Meta_Grind_closeGoal(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_46 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
x_49 = l_Lean_mkAppB(x_48, x_19, x_47);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_57 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__5;
x_60 = l_Lean_mkAppB(x_59, x_19, x_58);
x_61 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_1, x_60, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_26, 0);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_19);
x_68 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__7;
x_71 = l_Lean_mkAppB(x_70, x_19, x_69);
x_72 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_1, x_71, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_23);
if (x_76 == 0)
{
return x_23;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_23, 0);
lean_inc(x_77);
lean_dec(x_23);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolNotUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_1);
x_23 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
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
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_19, x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_34 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
x_37 = l_Lean_mkAppB(x_36, x_19, x_35);
x_38 = l_Lean_Meta_Grind_closeGoal(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_19);
x_46 = lean_grind_mk_eq_proof(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
x_49 = l_Lean_mkAppB(x_48, x_19, x_47);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_57 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Meta_Grind_propagateBoolNotDown___closed__1;
lean_inc_ref(x_19);
x_60 = l_Lean_mkAppB(x_59, x_19, x_58);
x_61 = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(x_19, x_60, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_26, 0);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_68 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_propagateBoolNotDown___closed__3;
lean_inc_ref(x_19);
x_71 = l_Lean_mkAppB(x_70, x_19, x_69);
x_72 = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(x_19, x_71, x_2, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_23);
if (x_76 == 0)
{
return x_23;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_23, 0);
lean_inc(x_77);
lean_dec(x_23);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateBoolNotDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_propagateAndUp___closed__6 = _init_l_Lean_Meta_Grind_propagateAndUp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndUp___closed__6);
l_Lean_Meta_Grind_propagateAndUp___closed__9 = _init_l_Lean_Meta_Grind_propagateAndUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndUp___closed__9);
l_Lean_Meta_Grind_propagateAndUp___closed__12 = _init_l_Lean_Meta_Grind_propagateAndUp___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndUp___closed__12);
l_Lean_Meta_Grind_propagateAndUp___closed__15 = _init_l_Lean_Meta_Grind_propagateAndUp___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndUp___closed__15);
if (builtin) {res = l_Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateAndDown___closed__2 = _init_l_Lean_Meta_Grind_propagateAndDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndDown___closed__2);
l_Lean_Meta_Grind_propagateAndDown___closed__5 = _init_l_Lean_Meta_Grind_propagateAndDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateAndDown___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateOrUp___closed__4 = _init_l_Lean_Meta_Grind_propagateOrUp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrUp___closed__4);
l_Lean_Meta_Grind_propagateOrUp___closed__7 = _init_l_Lean_Meta_Grind_propagateOrUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrUp___closed__7);
l_Lean_Meta_Grind_propagateOrUp___closed__10 = _init_l_Lean_Meta_Grind_propagateOrUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrUp___closed__10);
l_Lean_Meta_Grind_propagateOrUp___closed__13 = _init_l_Lean_Meta_Grind_propagateOrUp___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrUp___closed__13);
if (builtin) {res = l_Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateOrDown___closed__2 = _init_l_Lean_Meta_Grind_propagateOrDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrDown___closed__2);
l_Lean_Meta_Grind_propagateOrDown___closed__5 = _init_l_Lean_Meta_Grind_propagateOrDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateOrDown___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNotUp___closed__4 = _init_l_Lean_Meta_Grind_propagateNotUp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNotUp___closed__4);
l_Lean_Meta_Grind_propagateNotUp___closed__7 = _init_l_Lean_Meta_Grind_propagateNotUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNotUp___closed__7);
l_Lean_Meta_Grind_propagateNotUp___closed__10 = _init_l_Lean_Meta_Grind_propagateNotUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNotUp___closed__10);
if (builtin) {res = l_Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNotDown___closed__2 = _init_l_Lean_Meta_Grind_propagateNotDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNotDown___closed__2);
l_Lean_Meta_Grind_propagateNotDown___closed__5 = _init_l_Lean_Meta_Grind_propagateNotDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNotDown___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolDiseq___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolDiseq___closed__3);
l_Lean_Meta_Grind_propagateBoolDiseq___closed__6 = _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolDiseq___closed__6);
l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0 = _init_l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateEqUp___lam__0___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___closed__2);
l_Lean_Meta_Grind_propagateEqUp___closed__7 = _init_l_Lean_Meta_Grind_propagateEqUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateEqUp___closed__7);
l_Lean_Meta_Grind_propagateEqUp___closed__10 = _init_l_Lean_Meta_Grind_propagateEqUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateEqUp___closed__10);
if (builtin) {res = l_Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateIte___closed__0 = _init_l_Lean_Meta_Grind_propagateIte___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateIte___closed__0);
if (builtin) {res = l_Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2258103887____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1134176131____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateDecideDown___closed__9 = _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateDecideDown___closed__9);
l_Lean_Meta_Grind_propagateDecideDown___closed__12 = _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateDecideDown___closed__12);
if (builtin) {res = l_Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateDecideUp___closed__2 = _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateDecideUp___closed__2);
l_Lean_Meta_Grind_propagateDecideUp___closed__5 = _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateDecideUp___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolAndUp___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndUp___closed__3);
l_Lean_Meta_Grind_propagateBoolAndUp___closed__5 = _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndUp___closed__5);
l_Lean_Meta_Grind_propagateBoolAndUp___closed__7 = _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndUp___closed__7);
l_Lean_Meta_Grind_propagateBoolAndUp___closed__9 = _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndUp___closed__9);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolAndDown___closed__1 = _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndDown___closed__1);
l_Lean_Meta_Grind_propagateBoolAndDown___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolAndDown___closed__3);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolOrUp___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrUp___closed__3);
l_Lean_Meta_Grind_propagateBoolOrUp___closed__5 = _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrUp___closed__5);
l_Lean_Meta_Grind_propagateBoolOrUp___closed__7 = _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrUp___closed__7);
l_Lean_Meta_Grind_propagateBoolOrUp___closed__9 = _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrUp___closed__9);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolOrDown___closed__1 = _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrDown___closed__1);
l_Lean_Meta_Grind_propagateBoolOrDown___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolOrDown___closed__3);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolNotUp___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
l_Lean_Meta_Grind_propagateBoolNotUp___closed__5 = _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolNotUp___closed__5);
l_Lean_Meta_Grind_propagateBoolNotUp___closed__7 = _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolNotUp___closed__7);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateBoolNotDown___closed__1 = _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolNotDown___closed__1);
l_Lean_Meta_Grind_propagateBoolNotDown___closed__3 = _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBoolNotDown___closed__3);
if (builtin) {res = l_Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
