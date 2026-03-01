// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Types
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.CongrTheorems public import Lean.Meta.Eqns public import Lean.Meta.Tactic.Simp.SimpTheorems public import Lean.Meta.Tactic.Simp.SimpCongrTheorems import Lean.Meta.Tactic.Replace import Init.Data.Nat.Linear
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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 139, 45, 202, 100, 206, 9, 156)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(151, 147, 192, 37, 128, 176, 85, 99)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Let `dsimp` and `simp` simplify instance terms"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 201, 88, 225, 179, 142, 250, 98)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(12, 23, 81, 20, 29, 89, 104, 27)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 59, 134, 114, 78, 146, 120, 4)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_backward_dsimp_instances;
static const lean_string_object l_Lean_Meta_Simp_instInhabitedResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Simp_instInhabitedResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedResult_default___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_instInhabitedResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_instInhabitedResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedResult_default___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedResult_default___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedResult_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Meta_Simp_instInhabitedContext_default___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Meta_Simp_instInhabitedContext_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedContext_default___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedContext_default___closed__1_value;
extern lean_object* l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
extern lean_object* l_Lean_Meta_Simp_instInhabitedConfig_default;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExprCnstr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "eq_of_toNormPoly_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 13, 52, 42, 204, 20, 168, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4_value;
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_UsedSimps_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedStats_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedStats_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStats_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStats;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed;
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_visit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_visit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedStep_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedStep_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
static const lean_ctor_object l_Lean_TransformStep_toStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TransformStep_toStep___closed__0 = (const lean_object*)&l_Lean_TransformStep_toStep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instAndThenSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instAndThenSimproc___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instAndThenSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instAndThenSimproc = (const lean_object*)&l_Lean_Meta_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instAndThenDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instAndThenDSimproc___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instAndThenDSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instAndThenDSimproc = (const lean_object*)&l_Lean_Meta_Simp_instAndThenDSimproc___closed__0_value;
static const lean_array_object l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry_default___closed__1_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedTransformStep_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instInhabitedMethods_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedMethods_default___closed__0_value;
static const lean_closure_object l_Lean_Meta_Simp_instInhabitedMethods_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedMethods_default___closed__1_value;
static const lean_closure_object l_Lean_Meta_Simp_instInhabitedMethods_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedMethods_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_withFreshCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_withFreshCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_withFreshCache___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Result_mkCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Simp_Result_mkCast___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Result_mkCast___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Result_mkCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Result_mkCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 194, 82, 68, 109, 146, 236, 67)}};
static const lean_object* l_Lean_Meta_Simp_Result_mkCast___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Result_mkCast___closed__1_value;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_mkImpCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkImpCongr___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_mkImpCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallE!"};
static const lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_mkImpCongr___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_mkImpCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_mkImpCongr___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_mkImpCongr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__3;
lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6_value;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "app ["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " hasFwdDeps: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to build congruence proof, function expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateApp!Impl"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__1_value;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Tactic.Simp.Types"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Meta.Tactic.Simp.Types.0.Lean.Meta.Simp.simpAppUsingCongr.visit"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAppUsingCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAppUsingCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 141, 208, 58, 7, 230, 107, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "argKind mismatch while generating congr_simp theorem for `"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "used global `"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7;
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_mkCongrSimp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "congr simp thm"};
static const lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkCongrSimp_x3f___closed__0_value;
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Simp.tryAutoCongrTheorem\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 160, 244, 6, 151, 149, 13, 175)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to synthesize instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__1_value)}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__2_value)}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0_value),((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__3_value)}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0_value),((lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__4_value)}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numSteps"};
static const lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 202, 121, 219, 52, 103, 253, 190)}};
static const lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1_value;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_33; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_7 = x_2;
x_8 = x_33;
goto block_32;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(1, 0, 1);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 0, x_10);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_6);
lean_inc(x_1);
x_12 = lean_register_option(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_13 = x_12;
x_14 = x_22;
goto block_21;
}
else
{
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_1);
x_15 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_ctor_get(x_12, 0);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
x_25 = x_12;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult_default___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_instInhabitedResult_default___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult_default___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedResult_default___closed__2, &l_Lean_Meta_Simp_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedResult_default___closed__2);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedResult_default___closed__3, &l_Lean_Meta_Simp_instInhabitedResult_default___closed__3_once, _init_l_Lean_Meta_Simp_instInhabitedResult_default___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (x_2 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_11 = x_3;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
x_13 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_14; 
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_68; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_68 = !lean_is_exclusive(x_3);
if (x_68 == 0)
{
x_24 = x_3;
x_25 = x_68;
goto block_67;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_68;
goto block_67;
}
block_67:
{
uint8_t x_26; 
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (x_2 == 0)
{
x_26 = x_2;
goto block_38;
}
else
{
x_26 = x_23;
goto block_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_66; 
lean_inc(x_20);
lean_del_object(x_24);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_22, 0);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
x_40 = x_22;
x_41 = x_66;
goto block_65;
}
else
{
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_box(0);
x_41 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_42; 
x_42 = l_Lean_Meta_mkEqTrans(x_20, x_39, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_56; 
x_43 = lean_ctor_get(x_42, 0);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
x_44 = x_42;
x_45 = x_56;
goto block_55;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_46; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_43);
x_46 = x_40;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_43);
x_46 = x_54;
goto block_53;
}
block_53:
{
uint8_t x_47; 
if (x_2 == 0)
{
x_47 = x_2;
goto block_52;
}
else
{
x_47 = x_23;
goto block_52;
}
block_52:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_48);
x_49 = x_44;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_del_object(x_40);
lean_dec_ref(x_21);
x_57 = lean_ctor_get(x_42, 0);
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
x_58 = x_42;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
block_38:
{
lean_object* x_27; 
lean_inc_ref(x_1);
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_1);
x_27 = x_24;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_1);
x_27 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_28 = x_1;
x_29 = x_34;
goto block_33;
}
else
{
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_27);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_mkEqTrans(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_10 = x_2;
x_11 = x_17;
goto block_16;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_1);
x_12 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
x_12 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_52; 
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_2, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_2, 0);
lean_dec(x_54);
x_21 = x_2;
x_22 = x_52;
goto block_51;
}
else
{
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_50; 
x_23 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_24 = x_8;
x_25 = x_50;
goto block_49;
}
else
{
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_mkEqSymm(x_23, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_40; 
x_27 = lean_ctor_get(x_26, 0);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
x_28 = x_26;
x_29 = x_40;
goto block_39;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_30 = x_24;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_27);
x_30 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_31; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_1);
x_31 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_20);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_31);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_24);
lean_del_object(x_21);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_26, 0);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
x_42 = x_26;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_mkEqSymm(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static uint32_t _init_l_Lean_Meta_Simp_instInhabitedContext_default___closed__0(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext_default___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
x_5 = ((lean_object*)(l_Lean_Meta_Simp_instInhabitedContext_default___closed__1));
x_6 = lean_uint32_once(&l_Lean_Meta_Simp_instInhabitedContext_default___closed__0, &l_Lean_Meta_Simp_instInhabitedContext_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedContext_default___closed__0);
x_7 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_8 = lean_box(1);
x_9 = l_Lean_Meta_Simp_instInhabitedConfig_default;
x_10 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set(x_10, 5, x_5);
lean_ctor_set(x_10, 6, x_4);
lean_ctor_set(x_10, 7, x_3);
lean_ctor_set(x_10, 8, x_2);
lean_ctor_set_uint32(x_10, sizeof(void*)*9, x_6);
lean_ctor_set_uint32(x_10, sizeof(void*)*9 + 4, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*9 + 8, x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedContext_default___closed__2, &l_Lean_Meta_Simp_instInhabitedContext_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedContext_default___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 10);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 5);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 7);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 9);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 11);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 12);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 13);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 14);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 15);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 16);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 17);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 18);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 19);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 20);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 21);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 22);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 23);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 24);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 25);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 26);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 27);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 28);
x_37 = lean_st_ref_get(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___closed__4));
x_40 = l_Lean_Environment_contains(x_38, x_39, x_4);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_48; 
lean_inc(x_34);
lean_inc(x_7);
lean_inc(x_6);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_1, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_41 = x_1;
x_42 = x_48;
goto block_47;
}
else
{
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_7);
lean_ctor_set(x_46, 2, x_34);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 2, x_10);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 3, x_11);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 4, x_12);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 5, x_13);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 6, x_14);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 7, x_15);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 8, x_16);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 9, x_17);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 11, x_18);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 12, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 13, x_20);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 14, x_21);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 15, x_22);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 16, x_23);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 17, x_24);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 18, x_25);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 19, x_26);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 20, x_27);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 21, x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 22, x_29);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 23, x_30);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 24, x_31);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 25, x_32);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 26, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 27, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 28, x_36);
x_43 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_44; 
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 10, x_40);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getConfig___redArg(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_39; 
x_5 = lean_ctor_get(x_4, 0);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
x_6 = x_4;
x_7 = x_39;
goto block_38;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_39;
goto block_38;
}
block_38:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_37; 
x_8 = lean_ctor_get_uint8(x_5, 0);
x_9 = lean_ctor_get_uint8(x_5, 1);
x_10 = lean_ctor_get_uint8(x_5, 2);
x_11 = lean_ctor_get_uint8(x_5, 3);
x_12 = lean_ctor_get_uint8(x_5, 4);
x_13 = lean_ctor_get_uint8(x_5, 5);
x_14 = lean_ctor_get_uint8(x_5, 6);
x_15 = lean_ctor_get_uint8(x_5, 7);
x_16 = lean_ctor_get_uint8(x_5, 8);
x_17 = lean_ctor_get_uint8(x_5, 11);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
x_18 = x_5;
x_19 = x_37;
goto block_36;
}
else
{
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_37;
goto block_36;
}
block_36:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 7);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 16);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 19);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 21);
x_27 = 2;
x_28 = 0;
if (x_19 == 0)
{
x_29 = x_18;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_35, 0, x_8);
lean_ctor_set_uint8(x_35, 1, x_9);
lean_ctor_set_uint8(x_35, 2, x_10);
lean_ctor_set_uint8(x_35, 3, x_11);
lean_ctor_set_uint8(x_35, 4, x_12);
lean_ctor_set_uint8(x_35, 5, x_13);
lean_ctor_set_uint8(x_35, 6, x_14);
lean_ctor_set_uint8(x_35, 7, x_15);
lean_ctor_set_uint8(x_35, 8, x_16);
lean_ctor_set_uint8(x_35, 11, x_17);
x_29 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; 
lean_ctor_set_uint8(x_29, 9, x_27);
lean_ctor_set_uint8(x_29, 10, x_22);
lean_ctor_set_uint8(x_29, 12, x_23);
lean_ctor_set_uint8(x_29, 13, x_21);
lean_ctor_set_uint8(x_29, 14, x_28);
lean_ctor_set_uint8(x_29, 15, x_20);
lean_ctor_set_uint8(x_29, 16, x_24);
lean_ctor_set_uint8(x_29, 17, x_25);
lean_ctor_set_uint8(x_29, 18, x_26);
x_30 = l_Lean_Meta_Config_toConfigWithKey(x_29);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_30);
x_31 = x_6;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_40 = lean_ctor_get(x_4, 0);
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
x_41 = x_4;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getConfig___redArg(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_43; 
x_5 = lean_ctor_get(x_4, 0);
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
x_6 = x_4;
x_7 = x_43;
goto block_42;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_41; 
x_8 = lean_ctor_get_uint8(x_5, 0);
x_9 = lean_ctor_get_uint8(x_5, 1);
x_10 = lean_ctor_get_uint8(x_5, 2);
x_11 = lean_ctor_get_uint8(x_5, 3);
x_12 = lean_ctor_get_uint8(x_5, 4);
x_13 = lean_ctor_get_uint8(x_5, 5);
x_14 = lean_ctor_get_uint8(x_5, 6);
x_15 = lean_ctor_get_uint8(x_5, 7);
x_16 = lean_ctor_get_uint8(x_5, 8);
x_17 = lean_ctor_get_uint8(x_5, 11);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
x_18 = x_5;
x_19 = x_41;
goto block_40;
}
else
{
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 7);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 16);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 19);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 21);
x_28 = 2;
if (x_24 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_29 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = 2;
x_29 = x_39;
goto block_37;
}
block_37:
{
lean_object* x_30; 
if (x_19 == 0)
{
x_30 = x_18;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_36, 0, x_8);
lean_ctor_set_uint8(x_36, 1, x_9);
lean_ctor_set_uint8(x_36, 2, x_10);
lean_ctor_set_uint8(x_36, 3, x_11);
lean_ctor_set_uint8(x_36, 4, x_12);
lean_ctor_set_uint8(x_36, 5, x_13);
lean_ctor_set_uint8(x_36, 6, x_14);
lean_ctor_set_uint8(x_36, 7, x_15);
lean_ctor_set_uint8(x_36, 8, x_16);
lean_ctor_set_uint8(x_36, 11, x_17);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
lean_ctor_set_uint8(x_30, 9, x_28);
lean_ctor_set_uint8(x_30, 10, x_22);
lean_ctor_set_uint8(x_30, 12, x_23);
lean_ctor_set_uint8(x_30, 13, x_21);
lean_ctor_set_uint8(x_30, 14, x_29);
lean_ctor_set_uint8(x_30, 15, x_20);
lean_ctor_set_uint8(x_30, 16, x_25);
lean_ctor_set_uint8(x_30, 17, x_26);
lean_ctor_set_uint8(x_30, 18, x_27);
x_31 = l_Lean_Meta_Config_toConfigWithKey(x_30);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_31);
x_32 = x_6;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_44 = lean_ctor_get(x_4, 0);
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
x_45 = x_4;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_50; uint8_t x_51; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_box(1);
x_50 = l_Lean_Meta_Simp_backward_dsimp_instances;
x_51 = l_Lean_Option_get___at___00Lean_Meta_Simp_mkContext_spec__0(x_10, x_50);
if (x_51 == 0)
{
x_12 = x_9;
x_13 = x_4;
x_14 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_55 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_56 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 2);
x_57 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 3);
x_58 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 4);
x_59 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 5);
x_60 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 6);
x_61 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 7);
x_62 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
x_63 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 9);
x_64 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 10);
x_65 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 11);
x_66 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 12);
x_67 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 13);
x_68 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 14);
x_69 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 15);
x_70 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 16);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 17);
x_72 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 18);
x_73 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 19);
x_74 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 20);
x_75 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 21);
x_76 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 22);
x_77 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 23);
x_78 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 24);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 25);
x_80 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 26);
x_81 = lean_ctor_get(x_9, 2);
x_82 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 27);
x_89 = !lean_is_exclusive(x_9);
if (x_89 == 0)
{
x_83 = x_9;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_81);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_87, 0, x_52);
lean_ctor_set(x_87, 1, x_53);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_54);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 1, x_55);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 2, x_56);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 3, x_57);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 4, x_58);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 5, x_59);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 6, x_60);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 7, x_61);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 8, x_62);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 9, x_63);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 10, x_64);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 11, x_65);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 12, x_66);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 13, x_67);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 14, x_68);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 15, x_69);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 16, x_70);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 17, x_71);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 18, x_72);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 19, x_73);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 20, x_74);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 21, x_75);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 22, x_76);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 23, x_77);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 24, x_78);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 25, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 26, x_80);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 27, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
lean_ctor_set_uint8(x_85, sizeof(void*)*3 + 28, x_51);
x_12 = x_85;
x_13 = x_4;
x_14 = lean_box(0);
goto block_49;
}
}
}
block_49:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_19 = x_17;
x_20 = x_32;
goto block_31;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 1);
x_22 = l_UInt32_ofNatTruncate(x_21);
x_23 = lean_box(0);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 0;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_11);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_18);
lean_ctor_set(x_27, 5, x_2);
lean_ctor_set(x_27, 6, x_3);
lean_ctor_set(x_27, 7, x_23);
lean_ctor_set(x_27, 8, x_24);
lean_ctor_set_uint32(x_27, sizeof(void*)*9, x_22);
lean_ctor_set_uint32(x_27, sizeof(void*)*9 + 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*9 + 8, x_26);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_27);
x_28 = x_19;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_16);
lean_dec_ref(x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_33 = lean_ctor_get(x_17, 0);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
x_34 = x_17;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_41 = lean_ctor_get(x_15, 0);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
x_42 = x_15;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_15);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_mkContext___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_mkContext___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___redArg(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_34; 
x_8 = lean_ctor_get(x_7, 0);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_9 = x_7;
x_10 = x_34;
goto block_33;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_29; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_18 = lean_ctor_get(x_1, 8);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_20 = x_1;
x_21 = x_29;
goto block_28;
}
else
{
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_8);
lean_ctor_set(x_20, 3, x_6);
lean_ctor_set(x_20, 0, x_2);
x_22 = x_20;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_6);
lean_ctor_set(x_27, 4, x_8);
lean_ctor_set(x_27, 5, x_14);
lean_ctor_set(x_27, 6, x_15);
lean_ctor_set(x_27, 7, x_16);
lean_ctor_set(x_27, 8, x_18);
lean_ctor_set_uint32(x_27, sizeof(void*)*9, x_13);
lean_ctor_set_uint32(x_27, sizeof(void*)*9 + 4, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*9 + 8, x_19);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_22);
x_23 = x_9;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_7, 0);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_36 = x_7;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_5, 0);
x_50 = !lean_is_exclusive(x_5);
if (x_50 == 0)
{
x_44 = x_5;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_Context_setConfig___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Context_setConfig___redArg(x_1, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Context_setConfig(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 5);
lean_dec(x_21);
x_14 = x_1;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 5, x_2);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set(x_18, 3, x_6);
lean_ctor_set(x_18, 4, x_7);
lean_ctor_set(x_18, 5, x_2);
lean_ctor_set(x_18, 6, x_9);
lean_ctor_set(x_18, 7, x_10);
lean_ctor_set(x_18, 8, x_12);
lean_ctor_set_uint32(x_18, sizeof(void*)*9, x_8);
lean_ctor_set_uint32(x_18, sizeof(void*)*9 + 4, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*9 + 8, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_1, 7);
x_14 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 8);
lean_dec(x_25);
x_16 = x_1;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_local_ctx_num_indices(x_4);
if (x_17 == 0)
{
lean_ctor_set(x_16, 8, x_18);
x_19 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_9);
lean_ctor_set(x_22, 5, x_11);
lean_ctor_set(x_22, 6, x_12);
lean_ctor_set(x_22, 7, x_13);
lean_ctor_set(x_22, 8, x_18);
lean_ctor_set_uint32(x_22, sizeof(void*)*9, x_10);
lean_ctor_set_uint32(x_22, sizeof(void*)*9 + 4, x_14);
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 8, x_15);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Context_setLctxInitIndices(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_59; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
x_14 = x_1;
x_15 = x_59;
goto block_58;
}
else
{
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint8_t x_57; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 7);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 9);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 10);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 12);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 13);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 14);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 15);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 16);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 17);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 18);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 19);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 20);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 21);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 22);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 23);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 24);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 25);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 26);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 27);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 28);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
x_47 = x_2;
x_48 = x_57;
goto block_56;
}
else
{
lean_inc(x_44);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = x_57;
goto block_56;
}
block_56:
{
uint8_t x_49; lean_object* x_50; 
x_49 = 1;
if (x_48 == 0)
{
x_50 = x_47;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_55, 0, x_16);
lean_ctor_set(x_55, 1, x_17);
lean_ctor_set(x_55, 2, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_20);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 3, x_21);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 4, x_22);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 5, x_23);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 6, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 7, x_25);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 8, x_26);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 9, x_27);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 10, x_28);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 12, x_29);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 13, x_30);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 14, x_31);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 15, x_32);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 16, x_33);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 17, x_34);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 18, x_35);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 19, x_36);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 20, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 21, x_38);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 22, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 23, x_40);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 24, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 25, x_42);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 26, x_43);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 27, x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 28, x_46);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 11, x_49);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_50);
x_51 = x_14;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set(x_53, 3, x_5);
lean_ctor_set(x_53, 4, x_6);
lean_ctor_set(x_53, 5, x_8);
lean_ctor_set(x_53, 6, x_9);
lean_ctor_set(x_53, 7, x_10);
lean_ctor_set(x_53, 8, x_12);
lean_ctor_set_uint32(x_53, sizeof(void*)*9, x_7);
lean_ctor_set_uint32(x_53, sizeof(void*)*9 + 4, x_11);
lean_ctor_set_uint8(x_53, sizeof(void*)*9 + 8, x_13);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_59; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_13 = lean_ctor_get(x_1, 8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
x_15 = x_1;
x_16 = x_59;
goto block_58;
}
else
{
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 6);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 7);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 9);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 10);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 11);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 12);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 14);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 15);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 16);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 17);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 18);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 19);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 20);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 21);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 22);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 23);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 24);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 25);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 26);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 27);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 28);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
x_48 = x_3;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_45);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_18);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_21);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 3, x_22);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 4, x_23);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 5, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 6, x_25);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 7, x_26);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 8, x_27);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 9, x_28);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 10, x_29);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 11, x_30);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 12, x_31);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 14, x_32);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 15, x_33);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 16, x_34);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 17, x_35);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 18, x_36);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 19, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 20, x_38);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 21, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 22, x_40);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 23, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 24, x_42);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 25, x_43);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 26, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 27, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 28, x_47);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 13, x_2);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_50);
x_51 = x_15;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_5);
lean_ctor_set(x_53, 3, x_6);
lean_ctor_set(x_53, 4, x_7);
lean_ctor_set(x_53, 5, x_9);
lean_ctor_set(x_53, 6, x_10);
lean_ctor_set(x_53, 7, x_11);
lean_ctor_set(x_53, 8, x_13);
lean_ctor_set_uint32(x_53, sizeof(void*)*9, x_8);
lean_ctor_set_uint32(x_53, sizeof(void*)*9 + 4, x_12);
lean_ctor_set_uint8(x_53, sizeof(void*)*9 + 8, x_14);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_59; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_12 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_13 = lean_ctor_get(x_1, 8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
x_15 = x_1;
x_16 = x_59;
goto block_58;
}
else
{
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 6);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 7);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 9);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 10);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 11);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 12);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 13);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 14);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 15);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 16);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 17);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 18);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 19);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 20);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 21);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 22);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 23);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 24);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 25);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 26);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 27);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 28);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
x_48 = x_3;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_45);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_18);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_20);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 3, x_21);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 4, x_22);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 5, x_23);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 6, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 7, x_25);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 8, x_26);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 9, x_27);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 10, x_28);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 11, x_29);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 12, x_30);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 13, x_31);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 14, x_32);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 15, x_33);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 16, x_34);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 17, x_35);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 18, x_36);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 19, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 20, x_38);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 21, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 22, x_40);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 23, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 24, x_42);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 25, x_43);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 26, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 27, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 28, x_47);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 1, x_2);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_50);
x_51 = x_15;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_5);
lean_ctor_set(x_53, 3, x_6);
lean_ctor_set(x_53, 4, x_7);
lean_ctor_set(x_53, 5, x_9);
lean_ctor_set(x_53, 6, x_10);
lean_ctor_set(x_53, 7, x_11);
lean_ctor_set(x_53, 8, x_13);
lean_ctor_set_uint32(x_53, sizeof(void*)*9, x_8);
lean_ctor_set_uint32(x_53, sizeof(void*)*9 + 4, x_12);
lean_ctor_set_uint8(x_53, sizeof(void*)*9 + 8, x_14);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Meta_Simp_Context_setMemoize(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_14 = x_1;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 1, x_2);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_5);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set(x_18, 5, x_8);
lean_ctor_set(x_18, 6, x_9);
lean_ctor_set(x_18, 7, x_10);
lean_ctor_set(x_18, 8, x_12);
lean_ctor_set_uint32(x_18, sizeof(void*)*9, x_7);
lean_ctor_set_uint32(x_18, sizeof(void*)*9 + 4, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*9 + 8, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_Context_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0, &l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1, &l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2, &l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedUsedSimps_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_8; lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget_borrowed(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
x_17 = lean_name_eq(x_13, x_15);
if (x_17 == 0)
{
x_8 = x_17;
goto block_9;
}
else
{
if (x_14 == 0)
{
if (x_16 == 0)
{
x_8 = x_17;
goto block_9;
}
else
{
goto block_7;
}
}
else
{
x_8 = x_16;
goto block_9;
}
}
}
else
{
goto block_7;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
goto block_7;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Meta_Origin_key(x_3);
x_19 = l_Lean_Meta_Origin_key(x_12);
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_8 = x_20;
goto block_9;
}
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
block_9:
{
if (x_8 == 0)
{
goto block_7;
}
else
{
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 1);
lean_dec_ref(x_11);
x_16 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
return x_16;
}
else
{
if (x_13 == 0)
{
if (x_15 == 0)
{
return x_16;
}
else
{
return x_13;
}
}
else
{
return x_15;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_11);
x_17 = 0;
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec_ref(x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec_ref(x_18);
x_19 = 0;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Meta_Origin_key(x_3);
x_21 = l_Lean_Meta_Origin_key(x_18);
lean_dec(x_18);
x_22 = lean_name_eq(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
}
}
case 1:
{
lean_object* x_23; size_t x_24; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec_ref(x_10);
x_24 = lean_usize_shift_right(x_2, x_6);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
default: 
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg(x_27, x_28, x_3);
lean_dec_ref(x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_7; uint64_t x_11; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_16) == 0)
{
uint64_t x_17; 
x_17 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_7 = x_17;
goto block_10;
}
else
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_16, sizeof(void*)*2);
x_7 = x_18;
goto block_10;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_19) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_11 = x_20;
goto block_14;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_19, sizeof(void*)*2);
x_11 = x_21;
goto block_14;
}
}
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Origin_key(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint64_t x_23; 
x_23 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_3 = x_23;
goto block_6;
}
else
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_22, sizeof(void*)*2);
lean_dec(x_22);
x_3 = x_24;
goto block_6;
}
}
block_6:
{
size_t x_4; uint8_t x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
block_10:
{
uint64_t x_8; uint64_t x_9; 
x_8 = 13;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_3 = x_9;
goto block_6;
}
block_14:
{
uint64_t x_12; uint64_t x_13; 
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_3 = x_13;
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_UsedSimps_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_UsedSimps_contains(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_36; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
x_7 = x_1;
x_8 = x_36;
goto block_35;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_16; lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_7);
lean_dec(x_2);
x_23 = lean_array_push(x_5, x_3);
x_24 = lean_array_push(x_6, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_array_fget_borrowed(x_5, x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get_uint8(x_26, sizeof(void*)*1 + 1);
x_31 = lean_name_eq(x_27, x_29);
if (x_31 == 0)
{
x_16 = x_31;
goto block_20;
}
else
{
if (x_28 == 0)
{
if (x_30 == 0)
{
x_16 = x_31;
goto block_20;
}
else
{
goto block_15;
}
}
else
{
x_16 = x_30;
goto block_20;
}
}
}
else
{
goto block_15;
}
}
else
{
if (lean_obj_tag(x_26) == 0)
{
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Meta_Origin_key(x_3);
x_33 = l_Lean_Meta_Origin_key(x_26);
x_34 = lean_name_eq(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
x_16 = x_34;
goto block_20;
}
}
}
block_15:
{
lean_object* x_9; 
if (x_8 == 0)
{
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
block_20:
{
if (x_16 == 0)
{
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_del_object(x_7);
x_17 = lean_array_fset(x_5, x_2, x_3);
x_18 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_60; 
lean_inc_ref(x_6);
x_60 = !lean_is_exclusive(x_1);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_1, 0);
lean_dec(x_61);
x_14 = x_1;
x_15 = x_60;
goto block_59;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_46; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
x_27 = x_16;
x_28 = x_46;
goto block_45;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_46;
goto block_45;
}
block_45:
{
uint8_t x_32; 
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get_uint8(x_25, sizeof(void*)*1 + 1);
x_41 = lean_name_eq(x_37, x_39);
if (x_41 == 0)
{
x_32 = x_41;
goto block_36;
}
else
{
if (x_38 == 0)
{
if (x_40 == 0)
{
x_32 = x_41;
goto block_36;
}
else
{
lean_del_object(x_27);
goto block_31;
}
}
else
{
x_32 = x_40;
goto block_36;
}
}
}
else
{
lean_del_object(x_27);
goto block_31;
}
}
else
{
if (lean_obj_tag(x_25) == 0)
{
lean_del_object(x_27);
goto block_31;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Meta_Origin_key(x_4);
x_43 = l_Lean_Meta_Origin_key(x_25);
x_44 = lean_name_eq(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
x_32 = x_44;
goto block_36;
}
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_19 = x_30;
goto block_24;
}
block_36:
{
if (x_32 == 0)
{
lean_del_object(x_27);
goto block_31;
}
else
{
lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_33 = x_27;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_5);
x_33 = x_35;
goto block_34;
}
block_34:
{
x_19 = x_33;
goto block_24;
}
}
}
}
}
case 1:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
x_47 = lean_ctor_get(x_16, 0);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
x_48 = x_16;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_usize_shift_right(x_2, x_7);
x_51 = lean_usize_add(x_3, x_8);
x_52 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(x_47, x_50, x_51, x_4, x_5);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_52);
x_53 = x_48;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_19 = x_53;
goto block_24;
}
}
}
default: 
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_5);
x_19 = x_58;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_83; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_83 = !lean_is_exclusive(x_1);
if (x_83 == 0)
{
x_64 = x_1;
x_65 = x_83;
goto block_82;
}
else
{
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_1);
x_64 = lean_box(0);
x_65 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_63);
x_66 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_67; uint8_t x_68; size_t x_75; uint8_t x_76; 
x_67 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1___redArg(x_66, x_4, x_5);
x_75 = 7;
x_76 = lean_usize_dec_le(x_75, x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_67);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_dec_lt(x_77, x_78);
lean_dec(x_77);
x_68 = x_79;
goto block_74;
}
else
{
x_68 = x_76;
goto block_74;
}
block_74:
{
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_67);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___closed__0);
x_73 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg(x_3, x_69, x_70, x_71, x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
return x_73;
}
else
{
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_22; uint64_t x_26; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_31) == 0)
{
uint64_t x_32; 
x_32 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_22 = x_32;
goto block_25;
}
else
{
uint64_t x_33; 
x_33 = lean_ctor_get_uint64(x_31, sizeof(void*)*2);
x_22 = x_33;
goto block_25;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_34) == 0)
{
uint64_t x_35; 
x_35 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_26 = x_35;
goto block_29;
}
else
{
uint64_t x_36; 
x_36 = lean_ctor_get_uint64(x_34, sizeof(void*)*2);
x_26 = x_36;
goto block_29;
}
}
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Origin_key(x_8);
if (lean_obj_tag(x_37) == 0)
{
uint64_t x_38; 
x_38 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_10 = x_38;
goto block_21;
}
else
{
uint64_t x_39; 
x_39 = lean_ctor_get_uint64(x_37, sizeof(void*)*2);
lean_dec(x_37);
x_10 = x_39;
goto block_21;
}
}
block_21:
{
size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
block_25:
{
uint64_t x_23; uint64_t x_24; 
x_23 = 13;
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_10 = x_24;
goto block_21;
}
block_29:
{
uint64_t x_27; uint64_t x_28; 
x_27 = 11;
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_10 = x_28;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_9; uint64_t x_13; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_18) == 0)
{
uint64_t x_19; 
x_19 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_9 = x_19;
goto block_12;
}
else
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_18, sizeof(void*)*2);
x_9 = x_20;
goto block_12;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_21) == 0)
{
uint64_t x_22; 
x_22 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_13 = x_22;
goto block_16;
}
else
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_21, sizeof(void*)*2);
x_13 = x_23;
goto block_16;
}
}
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Origin_key(x_2);
if (lean_obj_tag(x_24) == 0)
{
uint64_t x_25; 
x_25 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_4 = x_25;
goto block_8;
}
else
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_24, sizeof(void*)*2);
lean_dec(x_24);
x_4 = x_26;
goto block_8;
}
}
block_8:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
block_12:
{
uint64_t x_10; uint64_t x_11; 
x_10 = 13;
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_4 = x_11;
goto block_8;
}
block_16:
{
uint64_t x_14; uint64_t x_15; 
x_14 = 11;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_4 = x_15;
goto block_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_5 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_15; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_6 = x_1;
x_7 = x_15;
goto block_14;
}
else
{
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
x_8 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(x_3, x_2, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
lean_ctor_set(x_6, 0, x_8);
x_11 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_apply_3(x_1, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
if (x_7 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(x_1, x_4, x_12, x_13, x_3);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_15, x_16, x_17, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget_borrowed(x_2, x_3);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
x_15 = lean_apply_3(x_1, x_5, x_13, x_14);
x_6 = x_15;
goto block_10;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_1);
x_17 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_1, x_16, x_5);
x_6 = x_17;
goto block_10;
}
default: 
{
x_6 = x_5;
goto block_10;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__0));
x_3 = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___closed__1));
x_4 = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_7);
x_13 = lean_array_get_size(x_8);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
x_21 = lean_nat_dec_le(x_14, x_17);
if (x_21 == 0)
{
lean_inc(x_17);
x_18 = x_17;
goto block_20;
}
else
{
x_18 = x_14;
goto block_20;
}
block_20:
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_18, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_inc(x_18);
x_9 = x_18;
x_10 = x_18;
goto block_12;
}
else
{
x_9 = x_18;
x_10 = x_17;
goto block_12;
}
}
}
else
{
x_2 = x_8;
goto block_6;
}
block_6:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__0(x_3, x_4, x_2);
return x_5;
}
block_12:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_8, x_9, x_10);
lean_dec(x_10);
x_2 = x_11;
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_UsedSimps_toArray(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Meta_Simp_UsedSimps_toArray_spec__1_spec__1_spec__2_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0, &l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__0);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1, &l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default___closed__1);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1, &l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedDiagnostics_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedDiagnostics_default;
x_2 = l_Lean_Meta_Simp_instInhabitedUsedSimps_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedStats_default___closed__0, &l_Lean_Meta_Simp_instInhabitedStats_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedStats_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedStats_default;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed(void) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_31; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get_uint32(x_3, sizeof(void*)*9);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get(x_3, 7);
x_19 = lean_ctor_get_uint32(x_3, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*9 + 8);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
x_22 = x_3;
x_23 = x_31;
goto block_30;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = x_31;
goto block_30;
}
block_30:
{
uint32_t x_24; uint32_t x_25; lean_object* x_26; 
x_24 = 1;
x_25 = lean_uint32_add(x_19, x_24);
if (x_23 == 0)
{
x_26 = x_22;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_13);
lean_ctor_set(x_29, 4, x_14);
lean_ctor_set(x_29, 5, x_16);
lean_ctor_set(x_29, 6, x_17);
lean_ctor_set(x_29, 7, x_18);
lean_ctor_set(x_29, 8, x_20);
lean_ctor_set_uint32(x_29, sizeof(void*)*9, x_15);
lean_ctor_set_uint8(x_29, sizeof(void*)*9 + 8, x_21);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
lean_ctor_set_uint32(x_26, sizeof(void*)*9 + 4, x_25);
x_27 = lean_apply_8(x_1, x_2, x_26, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withIncDischargeDepth___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_4, 8);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
x_23 = x_4;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
uint32_t x_25; uint32_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_uint32_add(x_20, x_25);
if (x_24 == 0)
{
x_27 = x_23;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_13);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_15);
lean_ctor_set(x_30, 5, x_17);
lean_ctor_set(x_30, 6, x_18);
lean_ctor_set(x_30, 7, x_19);
lean_ctor_set(x_30, 8, x_21);
lean_ctor_set_uint32(x_30, sizeof(void*)*9, x_16);
lean_ctor_set_uint8(x_30, sizeof(void*)*9 + 8, x_22);
x_27 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_28; 
lean_ctor_set_uint32(x_27, sizeof(void*)*9 + 4, x_26);
x_28 = lean_apply_8(x_2, x_3, x_27, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withIncDischargeDepth(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_4, 8);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_4, 5);
lean_dec(x_30);
x_22 = x_4;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 5, x_1);
x_24 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set(x_27, 5, x_1);
lean_ctor_set(x_27, 6, x_17);
lean_ctor_set(x_27, 7, x_18);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set_uint32(x_27, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_27, sizeof(void*)*9 + 4, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*9 + 8, x_21);
x_24 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_apply_8(x_2, x_3, x_24, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpTheorems___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get_uint32(x_5, sizeof(void*)*9);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get_uint32(x_5, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_5, 8);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_5, 5);
lean_dec(x_31);
x_23 = x_5;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 5, x_2);
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set(x_28, 5, x_2);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_21);
lean_ctor_set_uint32(x_28, sizeof(void*)*9, x_17);
lean_ctor_set_uint32(x_28, sizeof(void*)*9 + 4, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*9 + 8, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_apply_8(x_3, x_4, x_25, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_withSimpTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get_uint32(x_3, sizeof(void*)*9);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get(x_3, 7);
x_19 = lean_ctor_get_uint32(x_3, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_3, 8);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
x_21 = x_3;
x_22 = x_29;
goto block_28;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_29;
goto block_28;
}
block_28:
{
uint8_t x_23; lean_object* x_24; 
x_23 = 1;
if (x_22 == 0)
{
x_24 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_14);
lean_ctor_set(x_27, 5, x_16);
lean_ctor_set(x_27, 6, x_17);
lean_ctor_set(x_27, 7, x_18);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set_uint32(x_27, sizeof(void*)*9, x_15);
lean_ctor_set_uint32(x_27, sizeof(void*)*9 + 4, x_19);
x_24 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_25; 
lean_ctor_set_uint8(x_24, sizeof(void*)*9 + 8, x_23);
x_25 = lean_apply_8(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withInDSimp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_30; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_4, 8);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
x_22 = x_4;
x_23 = x_30;
goto block_29;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_24; lean_object* x_25; 
x_24 = 1;
if (x_23 == 0)
{
x_25 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_13);
lean_ctor_set(x_28, 3, x_14);
lean_ctor_set(x_28, 4, x_15);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_21);
lean_ctor_set_uint32(x_28, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_28, sizeof(void*)*9 + 4, x_20);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
lean_ctor_set_uint8(x_25, sizeof(void*)*9 + 8, x_24);
x_26 = lean_apply_8(x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withInDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0, &l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_78; 
x_10 = lean_st_ref_take(x_4);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_ctor_get(x_10, 3);
x_15 = lean_ctor_get(x_10, 4);
x_16 = lean_ctor_get(x_10, 5);
x_78 = !lean_is_exclusive(x_10);
if (x_78 == 0)
{
x_17 = x_10;
x_18 = x_78;
goto block_77;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_obj_once(&l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1, &l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1);
if (x_18 == 0)
{
lean_ctor_set(x_17, 2, x_19);
x_20 = x_17;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_11);
lean_ctor_set(x_76, 1, x_12);
lean_ctor_set(x_76, 2, x_19);
lean_ctor_set(x_76, 3, x_14);
lean_ctor_set(x_76, 4, x_15);
lean_ctor_set(x_76, 5, x_16);
x_20 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_74; 
x_21 = lean_st_ref_set(x_4, x_20);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get_uint32(x_3, sizeof(void*)*9);
x_28 = lean_ctor_get(x_3, 5);
x_29 = lean_ctor_get(x_3, 6);
x_30 = lean_ctor_get(x_3, 7);
x_31 = lean_ctor_get_uint32(x_3, sizeof(void*)*9 + 4);
x_32 = lean_ctor_get(x_3, 8);
x_74 = !lean_is_exclusive(x_3);
if (x_74 == 0)
{
x_33 = x_3;
x_34 = x_74;
goto block_73;
}
else
{
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = x_74;
goto block_73;
}
block_73:
{
uint8_t x_35; lean_object* x_36; 
x_35 = 1;
if (x_34 == 0)
{
x_36 = x_33;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_72, 0, x_22);
lean_ctor_set(x_72, 1, x_23);
lean_ctor_set(x_72, 2, x_24);
lean_ctor_set(x_72, 3, x_25);
lean_ctor_set(x_72, 4, x_26);
lean_ctor_set(x_72, 5, x_28);
lean_ctor_set(x_72, 6, x_29);
lean_ctor_set(x_72, 7, x_30);
lean_ctor_set(x_72, 8, x_32);
lean_ctor_set_uint32(x_72, sizeof(void*)*9, x_27);
lean_ctor_set_uint32(x_72, sizeof(void*)*9 + 4, x_31);
x_36 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_37; 
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 8, x_35);
lean_inc(x_4);
x_37 = lean_apply_9(x_1, x_13, x_2, x_36, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_62; 
x_38 = lean_ctor_get(x_37, 0);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
x_39 = x_37;
x_40 = x_62;
goto block_61;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_59; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_st_ref_take(x_4);
x_44 = lean_ctor_get(x_43, 0);
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 3);
x_47 = lean_ctor_get(x_43, 4);
x_48 = lean_ctor_get(x_43, 5);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_43, 2);
lean_dec(x_60);
x_49 = x_43;
x_50 = x_59;
goto block_58;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_43);
x_49 = lean_box(0);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 2, x_42);
x_51 = x_49;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_45);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_46);
lean_ctor_set(x_57, 4, x_47);
lean_ctor_set(x_57, 5, x_48);
x_51 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_st_ref_set(x_4, x_51);
lean_dec(x_4);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_41);
x_53 = x_39;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_41);
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
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_4);
x_63 = lean_ctor_get(x_37, 0);
x_70 = !lean_is_exclusive(x_37);
if (x_70 == 0)
{
x_64 = x_37;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_37);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withInDSimpWithCache___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_79; 
x_11 = lean_st_ref_take(x_5);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 2);
x_15 = lean_ctor_get(x_11, 3);
x_16 = lean_ctor_get(x_11, 4);
x_17 = lean_ctor_get(x_11, 5);
x_79 = !lean_is_exclusive(x_11);
if (x_79 == 0)
{
x_18 = x_11;
x_19 = x_79;
goto block_78;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_obj_once(&l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1, &l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1);
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_20);
x_21 = x_18;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_13);
lean_ctor_set(x_77, 2, x_20);
lean_ctor_set(x_77, 3, x_15);
lean_ctor_set(x_77, 4, x_16);
lean_ctor_set(x_77, 5, x_17);
x_21 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_75; 
x_22 = lean_st_ref_set(x_5, x_21);
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_ctor_get(x_4, 3);
x_27 = lean_ctor_get(x_4, 4);
x_28 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_29 = lean_ctor_get(x_4, 5);
x_30 = lean_ctor_get(x_4, 6);
x_31 = lean_ctor_get(x_4, 7);
x_32 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_33 = lean_ctor_get(x_4, 8);
x_75 = !lean_is_exclusive(x_4);
if (x_75 == 0)
{
x_34 = x_4;
x_35 = x_75;
goto block_74;
}
else
{
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = x_75;
goto block_74;
}
block_74:
{
uint8_t x_36; lean_object* x_37; 
x_36 = 1;
if (x_35 == 0)
{
x_37 = x_34;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_24);
lean_ctor_set(x_73, 2, x_25);
lean_ctor_set(x_73, 3, x_26);
lean_ctor_set(x_73, 4, x_27);
lean_ctor_set(x_73, 5, x_29);
lean_ctor_set(x_73, 6, x_30);
lean_ctor_set(x_73, 7, x_31);
lean_ctor_set(x_73, 8, x_33);
lean_ctor_set_uint32(x_73, sizeof(void*)*9, x_28);
lean_ctor_set_uint32(x_73, sizeof(void*)*9 + 4, x_32);
x_37 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_38; 
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 8, x_36);
lean_inc(x_5);
x_38 = lean_apply_9(x_2, x_14, x_3, x_37, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_63; 
x_39 = lean_ctor_get(x_38, 0);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
x_40 = x_38;
x_41 = x_63;
goto block_62;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_60; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_st_ref_take(x_5);
x_45 = lean_ctor_get(x_44, 0);
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 3);
x_48 = lean_ctor_get(x_44, 4);
x_49 = lean_ctor_get(x_44, 5);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_44, 2);
lean_dec(x_61);
x_50 = x_44;
x_51 = x_60;
goto block_59;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_44);
x_50 = lean_box(0);
x_51 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 2, x_43);
x_52 = x_50;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 3, x_47);
lean_ctor_set(x_58, 4, x_48);
lean_ctor_set(x_58, 5, x_49);
x_52 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_st_ref_set(x_5, x_52);
lean_dec(x_5);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_54 = x_40;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_42);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_5);
x_64 = lean_ctor_get(x_38, 0);
x_71 = !lean_is_exclusive(x_38);
if (x_71 == 0)
{
x_65 = x_38;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_38);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimpWithCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withInDSimpWithCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_46; 
x_10 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 0);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
x_12 = x_10;
x_13 = x_46;
goto block_45;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_46;
goto block_45;
}
block_45:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_43; 
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 5);
x_20 = lean_ctor_get(x_5, 6);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_5, 0);
lean_dec(x_44);
x_24 = x_5;
x_25 = x_43;
goto block_42;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_43;
goto block_42;
}
block_42:
{
uint64_t x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_11);
if (x_13 == 0)
{
x_27 = x_12;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_41, 0, x_11);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; 
lean_ctor_set_uint64(x_27, sizeof(void*)*1, x_26);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_28 = x_24;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_16);
lean_ctor_set(x_39, 3, x_17);
lean_ctor_set(x_39, 4, x_18);
lean_ctor_set(x_39, 5, x_19);
lean_ctor_set(x_39, 6, x_20);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 2, x_22);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 3, x_23);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; 
x_29 = lean_apply_8(x_1, x_2, x_3, x_4, x_28, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_30 = lean_ctor_get(x_29, 0);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
x_31 = x_29;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
return x_29;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withSimpIndexConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_47; 
x_11 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 0);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
x_13 = x_11;
x_14 = x_47;
goto block_46;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_47;
goto block_46;
}
block_46:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_44; 
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 5);
x_21 = lean_ctor_get(x_6, 6);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_25 = x_6;
x_26 = x_44;
goto block_43;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = x_44;
goto block_43;
}
block_43:
{
uint64_t x_27; lean_object* x_28; 
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_12);
if (x_14 == 0)
{
x_28 = x_13;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_12);
x_28 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_29; 
lean_ctor_set_uint64(x_28, sizeof(void*)*1, x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_18);
lean_ctor_set(x_40, 4, x_19);
lean_ctor_set(x_40, 5, x_20);
lean_ctor_set(x_40, 6, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*7, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 1, x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 2, x_23);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 3, x_24);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; 
x_30 = lean_apply_8(x_2, x_3, x_4, x_5, x_29, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_30, 0);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
x_32 = x_30;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
return x_30;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpIndexConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_46; 
x_10 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 0);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
x_12 = x_10;
x_13 = x_46;
goto block_45;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_46;
goto block_45;
}
block_45:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_43; 
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 5);
x_20 = lean_ctor_get(x_5, 6);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_5, 0);
lean_dec(x_44);
x_24 = x_5;
x_25 = x_43;
goto block_42;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_43;
goto block_42;
}
block_42:
{
uint64_t x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_11);
if (x_13 == 0)
{
x_27 = x_12;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_41, 0, x_11);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; 
lean_ctor_set_uint64(x_27, sizeof(void*)*1, x_26);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_28 = x_24;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_16);
lean_ctor_set(x_39, 3, x_17);
lean_ctor_set(x_39, 4, x_18);
lean_ctor_set(x_39, 5, x_19);
lean_ctor_set(x_39, 6, x_20);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 2, x_22);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 3, x_23);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; 
x_29 = lean_apply_8(x_1, x_2, x_3, x_4, x_28, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_30 = lean_ctor_get(x_29, 0);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
x_31 = x_29;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
return x_29;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withSimpMetaConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_47; 
x_11 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 0);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
x_13 = x_11;
x_14 = x_47;
goto block_46;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_47;
goto block_46;
}
block_46:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_44; 
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 5);
x_21 = lean_ctor_get(x_6, 6);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_25 = x_6;
x_26 = x_44;
goto block_43;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = x_44;
goto block_43;
}
block_43:
{
uint64_t x_27; lean_object* x_28; 
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_12);
if (x_14 == 0)
{
x_28 = x_13;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_12);
x_28 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_29; 
lean_ctor_set_uint64(x_28, sizeof(void*)*1, x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_18);
lean_ctor_set(x_40, 4, x_19);
lean_ctor_set(x_40, 5, x_20);
lean_ctor_set(x_40, 6, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*7, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 1, x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 2, x_23);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 3, x_24);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; 
x_30 = lean_apply_8(x_2, x_3, x_4, x_5, x_29, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_30, 0);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
x_32 = x_30;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
return x_30;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpMetaConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_dsimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_6 = lean_ctor_get(x_5, 0);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
x_7 = x_5;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_ctor_get(x_14, 3);
x_19 = lean_ctor_get(x_14, 4);
x_20 = lean_ctor_get(x_14, 5);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_21 = x_14;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_apply_1(x_1, x_20);
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_23);
x_24 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_18);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_23);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_st_ref_set(x_2, x_24);
x_26 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_26);
x_27 = x_7;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_5, 0);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
x_37 = x_5;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_modifyDiag___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isDiagnosticsEnabled___redArg(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_40; 
x_11 = lean_ctor_get(x_10, 0);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
x_12 = x_10;
x_13 = x_40;
goto block_39;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_14; 
x_14 = lean_unbox(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_38; 
x_19 = lean_st_ref_take(x_4);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 2);
x_23 = lean_ctor_get(x_19, 3);
x_24 = lean_ctor_get(x_19, 4);
x_25 = lean_ctor_get(x_19, 5);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
x_26 = x_19;
x_27 = x_38;
goto block_37;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_apply_1(x_1, x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_28);
x_29 = x_26;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_22);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
lean_ctor_set(x_36, 5, x_28);
x_29 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_st_ref_set(x_4, x_29);
x_31 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_31);
x_32 = x_12;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_10, 0);
x_48 = !lean_is_exclusive(x_10);
if (x_48 == 0)
{
x_42 = x_10;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_10);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_modifyDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Step_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_Step_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_done_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_done_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_visit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_visit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_continue_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_continue_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_Step_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult_default;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedStep_default___closed__0, &l_Lean_Meta_Simp_instInhabitedStep_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedStep_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedStep_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
x_3 = x_1;
x_4 = x_12;
goto block_11;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = 1;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_6);
if (x_4 == 0)
{
lean_ctor_set(x_3, 0, x_7);
x_8 = x_3;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_13 = lean_ctor_get(x_1, 0);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
x_14 = x_1;
x_15 = x_23;
goto block_22;
}
else
{
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
default: 
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_43; 
x_24 = lean_ctor_get(x_1, 0);
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
x_25 = x_1;
x_26 = x_43;
goto block_42;
}
else
{
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = x_43;
goto block_42;
}
block_42:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_27; 
lean_del_object(x_25);
x_27 = ((lean_object*)(l_Lean_TransformStep_toStep___closed__0));
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_41; 
x_28 = lean_ctor_get(x_24, 0);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
x_29 = x_24;
x_30 = x_41;
goto block_40;
}
else
{
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_33);
x_34 = x_29;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_34);
x_35 = x_25;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_34; 
x_8 = lean_ctor_get(x_2, 0);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
x_9 = x_2;
x_10 = x_34;
goto block_33;
}
else
{
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_13 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_11, x_12, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
x_15 = x_13;
x_16 = x_24;
goto block_23;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_17; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_14);
x_17 = x_9;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_del_object(x_9);
x_25 = lean_ctor_get(x_13, 0);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_26 = x_13;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_61; 
x_35 = lean_ctor_get(x_2, 0);
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
x_36 = x_2;
x_37 = x_61;
goto block_60;
}
else
{
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_40 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_38, x_39, x_35, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_51; 
x_41 = lean_ctor_get(x_40, 0);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
x_42 = x_40;
x_43 = x_51;
goto block_50;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_44; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_41);
x_44 = x_36;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_41);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_44);
x_45 = x_42;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
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
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_36);
x_52 = lean_ctor_get(x_40, 0);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
x_53 = x_40;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_101; 
x_62 = lean_ctor_get(x_2, 0);
x_101 = !lean_is_exclusive(x_2);
if (x_101 == 0)
{
x_63 = x_2;
x_64 = x_101;
goto block_100;
}
else
{
lean_inc(x_62);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = x_101;
goto block_100;
}
block_100:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_65);
x_66 = x_63;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_65);
x_66 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_99; 
x_70 = lean_ctor_get(x_62, 0);
x_99 = !lean_is_exclusive(x_62);
if (x_99 == 0)
{
x_71 = x_62;
x_72 = x_99;
goto block_98;
}
else
{
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_box(0);
x_72 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_75 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_73, x_74, x_70, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_89; 
x_76 = lean_ctor_get(x_75, 0);
x_89 = !lean_is_exclusive(x_75);
if (x_89 == 0)
{
x_77 = x_75;
x_78 = x_89;
goto block_88;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_79; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_76);
x_79 = x_71;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_76);
x_79 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_80; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_79);
x_80 = x_63;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_79);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_80);
x_81 = x_77;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_del_object(x_71);
lean_del_object(x_63);
x_90 = lean_ctor_get(x_75, 0);
x_97 = !lean_is_exclusive(x_75);
if (x_97 == 0)
{
x_91 = x_75;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_75);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_mkEqTransResultStep(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
x_18 = lean_apply_9(x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Simp_mkEqTransResultStep(x_16, x_19, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_18;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_andThen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; 
x_16 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_3);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_18);
x_19 = lean_apply_10(x_2, x_15, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Simp_mkEqTransResultStep(x_17, x_20, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_19;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_instAndThenSimproc___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_apply_9(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_17;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_dandThen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; 
x_16 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_3);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_apply_10(x_2, x_15, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_18;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_instAndThenDSimproc___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0___closed__1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0, &l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_instInhabitedSimprocs_default_spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2, &l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__2);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1, &l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__1);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3, &l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_instInhabitedStep_default;
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods_default___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_instInhabitedTransformStep_default;
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods_default___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods_default___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Meta_Simp_instInhabitedMethods_default___closed__2));
x_3 = ((lean_object*)(l_Lean_Meta_Simp_instInhabitedMethods_default___closed__1));
x_4 = ((lean_object*)(l_Lean_Meta_Simp_instInhabitedMethods_default___closed__0));
x_5 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3, &l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3_once, _init_l_Lean_Meta_Simp_instInhabitedMethods_default___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getMethods___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getMethods(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_post(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getContext___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getConfig___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getConfig___redArg(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_30; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_4, 8);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_4, 7);
lean_dec(x_31);
x_22 = x_4;
x_23 = x_30;
goto block_29;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
if (x_23 == 0)
{
lean_ctor_set(x_22, 7, x_24);
x_25 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_13);
lean_ctor_set(x_28, 3, x_14);
lean_ctor_set(x_28, 4, x_15);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_24);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set_uint32(x_28, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_28, sizeof(void*)*9 + 4, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*9 + 8, x_21);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_apply_8(x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withParent___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_31; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get_uint32(x_5, sizeof(void*)*9);
x_18 = lean_ctor_get(x_5, 5);
x_19 = lean_ctor_get(x_5, 6);
x_20 = lean_ctor_get_uint32(x_5, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_5, 8);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_5, 7);
lean_dec(x_32);
x_23 = x_5;
x_24 = x_31;
goto block_30;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
if (x_24 == 0)
{
lean_ctor_set(x_23, 7, x_25);
x_26 = x_23;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_16);
lean_ctor_set(x_29, 5, x_18);
lean_ctor_set(x_29, 6, x_19);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set(x_29, 8, x_21);
lean_ctor_set_uint32(x_29, sizeof(void*)*9, x_17);
lean_ctor_set_uint32(x_29, sizeof(void*)*9 + 4, x_20);
lean_ctor_set_uint8(x_29, sizeof(void*)*9 + 8, x_22);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_apply_8(x_3, x_4, x_26, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_withParent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimpTheorems___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpTheorems___redArg(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpCongrTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_inDSimp___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_inDSimp___redArg(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_inDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_31; 
x_6 = lean_st_ref_take(x_1);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_ctor_get(x_6, 3);
x_11 = lean_ctor_get(x_6, 4);
x_12 = lean_ctor_get(x_6, 5);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
x_13 = x_6;
x_14 = x_31;
goto block_30;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_7, 0);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_7, 1);
lean_dec(x_29);
x_16 = x_7;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_3);
x_18 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_3);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set(x_24, 4, x_11);
lean_ctor_set(x_24, 5, x_12);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_set(x_1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_60; 
x_10 = lean_st_ref_get(x_4);
x_11 = lean_st_ref_get(x_4);
x_12 = lean_st_ref_take(x_4);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_ctor_get(x_12, 3);
x_17 = lean_ctor_get(x_12, 4);
x_18 = lean_ctor_get(x_12, 5);
x_60 = !lean_is_exclusive(x_12);
if (x_60 == 0)
{
x_19 = x_12;
x_20 = x_60;
goto block_59;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_SMap_switch___redArg(x_13);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_14);
lean_ctor_set(x_58, 2, x_15);
lean_ctor_set(x_58, 3, x_16);
lean_ctor_set(x_58, 4, x_17);
lean_ctor_set(x_58, 5, x_18);
x_22 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_st_ref_set(x_4, x_22);
x_24 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
lean_dec_ref(x_25);
lean_inc(x_4);
x_28 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_45; 
x_29 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
x_30 = x_28;
x_31 = x_45;
goto block_44;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_32; 
lean_inc(x_29);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 1);
x_32 = x_30;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_29);
x_32 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
x_33 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_4, x_27, x_26, x_32);
lean_dec_ref(x_32);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_33, 0);
lean_dec(x_41);
x_34 = x_33;
x_35 = x_40;
goto block_39;
}
else
{
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_29);
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_29);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
lean_dec_ref(x_28);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_4, x_27, x_26, x_47);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_48, 0);
lean_dec(x_56);
x_49 = x_48;
x_50 = x_55;
goto block_54;
}
else
{
lean_dec(x_48);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_46);
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_46);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withPreservedCache___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_61; 
x_11 = lean_st_ref_get(x_5);
x_12 = lean_st_ref_get(x_5);
x_13 = lean_st_ref_take(x_5);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 5);
x_61 = !lean_is_exclusive(x_13);
if (x_61 == 0)
{
x_20 = x_13;
x_21 = x_61;
goto block_60;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_SMap_switch___redArg(x_14);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_22);
x_23 = x_20;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_15);
lean_ctor_set(x_59, 2, x_16);
lean_ctor_set(x_59, 3, x_17);
lean_ctor_set(x_59, 4, x_18);
lean_ctor_set(x_59, 5, x_19);
x_23 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_st_ref_set(x_5, x_23);
x_25 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
lean_dec_ref(x_26);
lean_inc(x_5);
x_29 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_46; 
x_30 = lean_ctor_get(x_29, 0);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
x_31 = x_29;
x_32 = x_46;
goto block_45;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_33; 
lean_inc(x_30);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 1);
x_33 = x_31;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_30);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_34 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_5, x_28, x_27, x_33);
lean_dec_ref(x_33);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_35 = x_34;
x_36 = x_41;
goto block_40;
}
else
{
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_30);
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_30);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
lean_dec_ref(x_29);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_5, x_28, x_27, x_48);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_49, 0);
lean_dec(x_57);
x_50 = x_49;
x_51 = x_56;
goto block_55;
}
else
{
lean_dec(x_49);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_47);
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withPreservedCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_20; 
x_5 = lean_st_ref_take(x_1);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_10 = lean_ctor_get(x_5, 5);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_11 = x_5;
x_12 = x_20;
goto block_19;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_2);
x_13 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
lean_ctor_set(x_18, 3, x_8);
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 5, x_10);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_st_ref_set(x_1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__0, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__1, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__1);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1, &l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withInDSimpWithCache___redArg___closed__1);
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_55; 
x_10 = lean_st_ref_get(x_4);
x_11 = lean_st_ref_take(x_4);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_16 = lean_ctor_get(x_11, 5);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_11, 0);
lean_dec(x_56);
x_17 = x_11;
x_18 = x_55;
goto block_54;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__2, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_19);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set(x_53, 2, x_13);
lean_ctor_set(x_53, 3, x_14);
lean_ctor_set(x_53, 4, x_15);
lean_ctor_set(x_53, 5, x_16);
x_20 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_st_ref_set(x_4, x_20);
x_22 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_22);
lean_dec(x_10);
lean_inc(x_4);
x_23 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_25 = x_23;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; 
lean_inc(x_24);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 1);
x_27 = x_25;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_24);
x_27 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_28 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_22, x_27);
lean_dec_ref(x_27);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_29 = x_28;
x_30 = x_35;
goto block_34;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_24);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_24);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec_ref(x_23);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_22, x_42);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_44 = x_43;
x_45 = x_50;
goto block_49;
}
else
{
lean_dec(x_43);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_41);
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_41);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withFreshCache___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_56; 
x_11 = lean_st_ref_get(x_5);
x_12 = lean_st_ref_take(x_5);
x_13 = lean_ctor_get(x_12, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = lean_ctor_get(x_12, 3);
x_16 = lean_ctor_get(x_12, 4);
x_17 = lean_ctor_get(x_12, 5);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
x_18 = x_12;
x_19 = x_56;
goto block_55;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__2, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__2);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_20);
x_21 = x_18;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_14);
lean_ctor_set(x_54, 3, x_15);
lean_ctor_set(x_54, 4, x_16);
lean_ctor_set(x_54, 5, x_17);
x_21 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_st_ref_set(x_5, x_21);
x_23 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_23);
lean_dec(x_11);
lean_inc(x_5);
x_24 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_41; 
x_25 = lean_ctor_get(x_24, 0);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
x_26 = x_24;
x_27 = x_41;
goto block_40;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; 
lean_inc(x_25);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
x_28 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_25);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_23, x_28);
lean_dec_ref(x_28);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_30 = x_29;
x_31 = x_36;
goto block_35;
}
else
{
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_25);
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_25);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
lean_dec_ref(x_24);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_23, x_43);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_44, 0);
lean_dec(x_52);
x_45 = x_44;
x_46 = x_51;
goto block_50;
}
else
{
lean_dec(x_44);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_42);
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withFreshCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_69; 
x_12 = lean_st_ref_get(x_6);
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 1);
x_15 = lean_ctor_get(x_13, 2);
x_16 = lean_ctor_get(x_13, 3);
x_17 = lean_ctor_get(x_13, 4);
x_18 = lean_ctor_get(x_13, 5);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_13, 0);
lean_dec(x_70);
x_19 = x_13;
x_20 = x_69;
goto block_68;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__2, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__2);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_21);
lean_ctor_set(x_67, 1, x_14);
lean_ctor_set(x_67, 2, x_15);
lean_ctor_set(x_67, 3, x_16);
lean_ctor_set(x_67, 4, x_17);
lean_ctor_set(x_67, 5, x_18);
x_22 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_64; 
x_23 = lean_st_ref_set(x_6, x_22);
x_24 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
x_27 = lean_ctor_get(x_4, 2);
x_28 = lean_ctor_get(x_4, 3);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_4, 4);
lean_dec(x_65);
x_29 = x_4;
x_30 = x_64;
goto block_63;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_1);
x_31 = x_29;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_62, 0, x_25);
lean_ctor_set(x_62, 1, x_26);
lean_ctor_set(x_62, 2, x_27);
lean_ctor_set(x_62, 3, x_28);
lean_ctor_set(x_62, 4, x_1);
x_31 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_32; 
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_32 = lean_apply_8(x_3, x_31, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_49; 
x_33 = lean_ctor_get(x_32, 0);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
x_34 = x_32;
x_35 = x_49;
goto block_48;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_36; 
lean_inc(x_33);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
x_36 = x_34;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_33);
x_36 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
x_37 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_24, x_36);
lean_dec_ref(x_36);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_38 = x_37;
x_39 = x_44;
goto block_43;
}
else
{
lean_dec(x_37);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_33);
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
lean_dec_ref(x_32);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_24, x_51);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_52, 0);
lean_dec(x_60);
x_53 = x_52;
x_54 = x_59;
goto block_58;
}
else
{
lean_dec(x_52);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_50);
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_50);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Meta_Simp_withDischarger___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_70; 
x_13 = lean_st_ref_get(x_7);
x_14 = lean_st_ref_take(x_7);
x_15 = lean_ctor_get(x_14, 1);
x_16 = lean_ctor_get(x_14, 2);
x_17 = lean_ctor_get(x_14, 3);
x_18 = lean_ctor_get(x_14, 4);
x_19 = lean_ctor_get(x_14, 5);
x_70 = !lean_is_exclusive(x_14);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_14, 0);
lean_dec(x_71);
x_20 = x_14;
x_21 = x_70;
goto block_69;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_obj_once(&l_Lean_Meta_Simp_withFreshCache___redArg___closed__2, &l_Lean_Meta_Simp_withFreshCache___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshCache___redArg___closed__2);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_22);
x_23 = x_20;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_22);
lean_ctor_set(x_68, 1, x_15);
lean_ctor_set(x_68, 2, x_16);
lean_ctor_set(x_68, 3, x_17);
lean_ctor_set(x_68, 4, x_18);
lean_ctor_set(x_68, 5, x_19);
x_23 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_65; 
x_24 = lean_st_ref_set(x_7, x_23);
x_25 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_ctor_get(x_5, 3);
x_65 = !lean_is_exclusive(x_5);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_5, 4);
lean_dec(x_66);
x_30 = x_5;
x_31 = x_65;
goto block_64;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_32; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 4, x_2);
x_32 = x_30;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_27);
lean_ctor_set(x_63, 2, x_28);
lean_ctor_set(x_63, 3, x_29);
lean_ctor_set(x_63, 4, x_2);
x_32 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_33; 
lean_ctor_set_uint8(x_32, sizeof(void*)*5, x_3);
lean_inc(x_7);
x_33 = lean_apply_8(x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_50; 
x_34 = lean_ctor_get(x_33, 0);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
x_35 = x_33;
x_36 = x_50;
goto block_49;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_37; 
lean_inc(x_34);
if (x_36 == 0)
{
lean_ctor_set_tag(x_35, 1);
x_37 = x_35;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_34);
x_37 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_25, x_37);
lean_dec_ref(x_37);
lean_dec(x_7);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_39 = x_38;
x_40 = x_45;
goto block_44;
}
else
{
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_34);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_34);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
x_51 = lean_ctor_get(x_33, 0);
lean_inc(x_51);
lean_dec_ref(x_33);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_25, x_52);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_53, 0);
lean_dec(x_61);
x_54 = x_53;
x_55 = x_60;
goto block_59;
}
else
{
lean_dec(x_53);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_51);
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_51);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Meta_Simp_withDischarger(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fget_borrowed(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
x_21 = lean_name_eq(x_17, x_19);
if (x_21 == 0)
{
x_9 = x_21;
goto block_12;
}
else
{
if (x_18 == 0)
{
if (x_20 == 0)
{
x_9 = x_21;
goto block_12;
}
else
{
goto block_8;
}
}
else
{
x_9 = x_20;
goto block_12;
}
}
}
else
{
goto block_8;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
goto block_8;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Meta_Origin_key(x_4);
x_23 = l_Lean_Meta_Origin_key(x_16);
x_24 = lean_name_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_9 = x_24;
goto block_12;
}
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
block_12:
{
if (x_9 == 0)
{
goto block_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_37; 
x_4 = lean_ctor_get(x_1, 0);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
x_5 = x_1;
x_6 = x_37;
goto block_36;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec_ref(x_13);
x_25 = lean_name_eq(x_21, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
x_15 = x_25;
goto block_20;
}
else
{
if (x_22 == 0)
{
if (x_24 == 0)
{
x_15 = x_25;
goto block_20;
}
else
{
lean_object* x_26; 
lean_dec(x_14);
lean_del_object(x_5);
x_26 = lean_box(0);
return x_26;
}
}
else
{
x_15 = x_24;
goto block_20;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_del_object(x_5);
x_27 = lean_box(0);
return x_27;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_13);
lean_dec(x_14);
lean_del_object(x_5);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Meta_Origin_key(x_3);
x_30 = l_Lean_Meta_Origin_key(x_13);
lean_dec(x_13);
x_31 = lean_name_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_15 = x_31;
goto block_20;
}
}
block_20:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
lean_del_object(x_5);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec_ref(x_12);
x_33 = lean_usize_shift_right(x_2, x_8);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
lean_del_object(x_5);
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg(x_38, x_39, x_40, x_3);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_7; uint64_t x_11; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_16) == 0)
{
uint64_t x_17; 
x_17 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_7 = x_17;
goto block_10;
}
else
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_16, sizeof(void*)*2);
x_7 = x_18;
goto block_10;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_19) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_11 = x_20;
goto block_14;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_19, sizeof(void*)*2);
x_11 = x_21;
goto block_14;
}
}
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Origin_key(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint64_t x_23; 
x_23 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_3 = x_23;
goto block_6;
}
else
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_22, sizeof(void*)*2);
lean_dec(x_22);
x_3 = x_24;
goto block_6;
}
}
block_6:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
block_10:
{
uint64_t x_8; uint64_t x_9; 
x_8 = 13;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_3 = x_9;
goto block_6;
}
block_14:
{
uint64_t x_12; uint64_t x_13; 
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_3 = x_13;
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_53; 
x_6 = lean_ctor_get(x_5, 0);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
x_7 = x_5;
x_8 = x_53;
goto block_52;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_53;
goto block_52;
}
block_52:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_51; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 5);
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
x_21 = x_14;
x_22 = x_51;
goto block_50;
}
else
{
lean_inc(x_15);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_15, 2);
x_26 = lean_ctor_get(x_15, 3);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
x_27 = x_15;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_29; lean_object* x_43; 
lean_inc_ref(x_24);
x_43 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_24, x_1);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_44);
x_29 = x_46;
goto block_42;
}
else
{
lean_object* x_47; 
lean_dec(x_43);
x_47 = lean_unsigned_to_nat(1u);
x_29 = x_47;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(x_24, x_1, x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_30);
x_31 = x_27;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_25);
lean_ctor_set(x_41, 3, x_26);
x_31 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_32; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_31);
x_32 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_18);
lean_ctor_set(x_39, 3, x_19);
lean_ctor_set(x_39, 4, x_20);
lean_ctor_set(x_39, 5, x_31);
x_32 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_set(x_2, x_32);
x_34 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_34);
x_35 = x_7;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
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
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_5, 0);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
x_55 = x_5;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_5);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(x_1, x_4, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTriedSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_28; lean_object* x_52; 
x_52 = l_Lean_isDiagnosticsEnabled___redArg(x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
x_28 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_88; 
x_55 = lean_st_ref_take(x_2);
x_56 = lean_ctor_get(x_55, 5);
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_55, 2);
x_60 = lean_ctor_get(x_55, 3);
x_61 = lean_ctor_get(x_55, 4);
x_88 = !lean_is_exclusive(x_55);
if (x_88 == 0)
{
x_62 = x_55;
x_63 = x_88;
goto block_87;
}
else
{
lean_inc(x_56);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_62 = lean_box(0);
x_63 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_86; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
x_66 = lean_ctor_get(x_56, 2);
x_67 = lean_ctor_get(x_56, 3);
x_86 = !lean_is_exclusive(x_56);
if (x_86 == 0)
{
x_68 = x_56;
x_69 = x_86;
goto block_85;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_68 = lean_box(0);
x_69 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_70; lean_object* x_80; 
lean_inc_ref(x_64);
x_80 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_64, x_1);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_81, x_82);
lean_dec(x_81);
x_70 = x_83;
goto block_79;
}
else
{
lean_object* x_84; 
lean_dec(x_80);
x_84 = lean_unsigned_to_nat(1u);
x_70 = x_84;
goto block_79;
}
block_79:
{
lean_object* x_71; lean_object* x_72; 
lean_inc_ref(x_1);
x_71 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_UsedSimps_insert_spec__0___redArg(x_64, x_1, x_70);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_65);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_67);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 5, x_72);
x_73 = x_62;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_58);
lean_ctor_set(x_76, 2, x_59);
lean_ctor_set(x_76, 3, x_60);
lean_ctor_set(x_76, 4, x_61);
lean_ctor_set(x_76, 5, x_72);
x_73 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_74; 
x_74 = lean_st_ref_set(x_2, x_73);
x_28 = lean_box(0);
goto block_51;
}
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_52, 0);
x_96 = !lean_is_exclusive(x_52);
if (x_96 == 0)
{
x_90 = x_52;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_52);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_26; 
x_9 = lean_st_ref_take(x_7);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 4);
x_15 = lean_ctor_get(x_9, 5);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_16 = x_9;
x_17 = x_26;
goto block_25;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Meta_Simp_UsedSimps_insert(x_13, x_6);
if (x_17 == 0)
{
lean_ctor_set(x_16, 3, x_18);
x_19 = x_16;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_15);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_set(x_7, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
block_51:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_32 = l_Lean_Meta_isEqnThm_x3f___redArg(x_30, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; uint8_t x_35; uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_1, 0);
lean_dec(x_42);
x_34 = x_1;
x_35 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 1, x_29);
x_37 = x_39;
goto block_38;
}
block_38:
{
x_6 = x_37;
x_7 = x_2;
x_8 = lean_box(0);
goto block_27;
}
}
}
else
{
lean_dec(x_33);
x_6 = x_1;
x_7 = x_2;
x_8 = lean_box(0);
goto block_27;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_32, 0);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
x_44 = x_32;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
x_6 = x_1;
x_7 = x_2;
x_8 = lean_box(0);
goto block_27;
}
}
else
{
x_6 = x_1;
x_7 = x_2;
x_8 = lean_box(0);
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_1, x_4, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = lean_name_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = lean_name_eq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___closed__0);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_22; 
x_22 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_10 = x_22;
goto block_21;
}
else
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_10 = x_23;
goto block_21;
}
block_21:
{
size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; 
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_9; 
x_9 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_4 = x_9;
goto block_8;
}
else
{
uint64_t x_10; 
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_4 = x_10;
goto block_8;
}
block_8:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_name_eq(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_7; 
x_7 = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_UsedSimps_contains_spec__0___redArg___closed__0);
x_3 = x_7;
goto block_6;
}
else
{
uint64_t x_8; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_3 = x_8;
goto block_6;
}
block_6:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg(x_1, x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_53; 
x_6 = lean_ctor_get(x_5, 0);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
x_7 = x_5;
x_8 = x_53;
goto block_52;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_53;
goto block_52;
}
block_52:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_51; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 5);
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
x_21 = x_14;
x_22 = x_51;
goto block_50;
}
else
{
lean_inc(x_15);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_15, 2);
x_26 = lean_ctor_get(x_15, 3);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
x_27 = x_15;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_29; lean_object* x_43; 
lean_inc_ref(x_25);
x_43 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg(x_25, x_1);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_44);
x_29 = x_46;
goto block_42;
}
else
{
lean_object* x_47; 
lean_dec(x_43);
x_47 = lean_unsigned_to_nat(1u);
x_29 = x_47;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0___redArg(x_25, x_1, x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_30);
x_31 = x_27;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_26);
x_31 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_32; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_31);
x_32 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_18);
lean_ctor_set(x_39, 3, x_19);
lean_ctor_set(x_39, 4, x_20);
lean_ctor_set(x_39, 5, x_31);
x_32 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_set(x_2, x_32);
x_34 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_34);
x_35 = x_7;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
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
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_5, 0);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
x_55 = x_5;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_5);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordCongrTheorem___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordCongrTheorem___redArg(x_1, x_4, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordCongrTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_recordCongrTheorem_spec__1_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_recordCongrTheorem_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
if (x_6 == 0)
{
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_13 == 0)
{
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_12);
x_16 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1(x_1, x_10, x_14, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__1(x_1, x_4, x_9, x_10);
return x_11;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_49; 
x_6 = lean_ctor_get(x_5, 0);
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
x_7 = x_5;
x_8 = x_49;
goto block_48;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_49;
goto block_48;
}
block_48:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_47; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_ctor_get(x_14, 3);
x_19 = lean_ctor_get(x_14, 4);
x_20 = lean_ctor_get(x_14, 5);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
x_21 = x_14;
x_22 = x_47;
goto block_46;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_23; uint8_t x_33; 
x_33 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_20);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_45; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
x_36 = lean_ctor_get(x_20, 2);
x_37 = lean_ctor_get(x_20, 3);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
x_38 = x_20;
x_39 = x_45;
goto block_44;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_38 = lean_box(0);
x_39 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_PersistentArray_push___redArg(x_37, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 3, x_40);
x_41 = x_38;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
x_23 = x_41;
goto block_32;
}
}
}
else
{
lean_dec_ref(x_1);
x_23 = x_20;
goto block_32;
}
block_32:
{
lean_object* x_24; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_23);
x_24 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_18);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_23);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_st_ref_set(x_2, x_24);
x_26 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_26);
x_27 = x_7;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_5, 0);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
x_51 = x_5;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(x_1, x_4, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTheoremWithBadKeys(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Meta_mkEqRefl(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_7, 0);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
x_11 = x_7;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Result_getProof(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_isExprDefEq(x_1, x_9, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_9);
x_13 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_15 = l_Lean_Meta_mkEq(x_1, x_9, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_mkExpectedTypeHint(x_14, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_dec(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
else
{
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_8, 0);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
x_28 = x_8;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_getProof_x27(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Meta_Simp_Result_mkCast___closed__1));
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_2);
x_15 = l_Lean_Meta_mkAppM(x_10, x_14, x_3, x_4, x_5, x_6);
return x_15;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_mkCast(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_expr_eqv(x_13, x_2);
if (x_14 == 0)
{
goto block_11;
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
else
{
goto block_11;
}
block_11:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Meta_mkEqMPR(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_mkEqMPR(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_expr_eqv(x_13, x_2);
if (x_14 == 0)
{
goto block_11;
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
else
{
goto block_11;
}
block_11:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Meta_mkEqMP(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_mkEqMP(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_10 = x_1;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_app___override(x_9, x_2);
x_13 = 1;
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_14 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_8);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_55; 
x_21 = lean_ctor_get(x_1, 0);
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_1, 1);
lean_dec(x_56);
x_22 = x_1;
x_23 = x_55;
goto block_54;
}
else
{
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_53; 
x_24 = lean_ctor_get(x_8, 0);
x_53 = !lean_is_exclusive(x_8);
if (x_53 == 0)
{
x_25 = x_8;
x_26 = x_53;
goto block_52;
}
else
{
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_27; 
lean_inc_ref(x_2);
x_27 = l_Lean_Meta_mkCongrFun(x_24, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_43; 
x_28 = lean_ctor_get(x_27, 0);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
x_29 = x_27;
x_30 = x_43;
goto block_42;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_app___override(x_21, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_32 = x_25;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_28);
x_32 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_33; lean_object* x_34; 
x_33 = 1;
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_31);
x_34 = x_22;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_34);
x_35 = x_29;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_del_object(x_25);
lean_del_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_27, 0);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
x_45 = x_27;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_mkCongrFun(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_10 = x_2;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_app___override(x_1, x_9);
x_13 = 1;
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_14 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_8);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_55; 
x_21 = lean_ctor_get(x_2, 0);
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 1);
lean_dec(x_56);
x_22 = x_2;
x_23 = x_55;
goto block_54;
}
else
{
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_53; 
x_24 = lean_ctor_get(x_8, 0);
x_53 = !lean_is_exclusive(x_8);
if (x_53 == 0)
{
x_25 = x_8;
x_26 = x_53;
goto block_52;
}
else
{
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_27; 
lean_inc_ref(x_1);
x_27 = l_Lean_Meta_mkCongrArg(x_1, x_24, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_43; 
x_28 = lean_ctor_get(x_27, 0);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
x_29 = x_27;
x_30 = x_43;
goto block_42;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_app___override(x_1, x_21);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_32 = x_25;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_28);
x_32 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_33; lean_object* x_34; 
x_33 = 1;
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_31);
x_34 = x_22;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_34);
x_35 = x_29;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_del_object(x_25);
lean_del_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_27, 0);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
x_45 = x_27;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_mkCongrArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_109; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
x_12 = x_2;
x_13 = x_109;
goto block_108;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_14; 
lean_inc_ref(x_10);
lean_inc_ref(x_8);
x_14 = l_Lean_Expr_app___override(x_8, x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_15; lean_object* x_16; 
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = 1;
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_16 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_11);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_48; 
x_20 = lean_ctor_get(x_11, 0);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
x_21 = x_11;
x_22 = x_48;
goto block_47;
}
else
{
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_mkCongrArg(x_8, x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_38; 
x_24 = lean_ctor_get(x_23, 0);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
x_25 = x_23;
x_26 = x_38;
goto block_37;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_27; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_27 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_24);
x_27 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_28; lean_object* x_29; 
x_28 = 1;
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_14);
x_29 = x_12;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_27);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_del_object(x_21);
lean_dec_ref(x_14);
lean_del_object(x_12);
x_39 = lean_ctor_get(x_23, 0);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
x_40 = x_23;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
else
{
lean_dec_ref(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_77; 
x_49 = lean_ctor_get(x_9, 0);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
x_50 = x_9;
x_51 = x_77;
goto block_76;
}
else
{
lean_inc(x_49);
lean_dec(x_9);
x_50 = lean_box(0);
x_51 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_mkCongrFun(x_49, x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_67; 
x_53 = lean_ctor_get(x_52, 0);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
x_54 = x_52;
x_55 = x_67;
goto block_66;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_56; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_53);
x_56 = x_50;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_53);
x_56 = x_65;
goto block_64;
}
block_64:
{
uint8_t x_57; lean_object* x_58; 
x_57 = 1;
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_56);
lean_ctor_set(x_12, 0, x_14);
x_58 = x_12;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_56);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_57);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_58);
x_59 = x_54;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_del_object(x_50);
lean_dec_ref(x_14);
lean_del_object(x_12);
x_68 = lean_ctor_get(x_52, 0);
x_75 = !lean_is_exclusive(x_52);
if (x_75 == 0)
{
x_69 = x_52;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_52);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_107; 
lean_dec_ref(x_10);
x_78 = lean_ctor_get(x_9, 0);
lean_inc(x_78);
lean_dec_ref(x_9);
x_79 = lean_ctor_get(x_11, 0);
x_107 = !lean_is_exclusive(x_11);
if (x_107 == 0)
{
x_80 = x_11;
x_81 = x_107;
goto block_106;
}
else
{
lean_inc(x_79);
lean_dec(x_11);
x_80 = lean_box(0);
x_81 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_82; 
x_82 = l_Lean_Meta_mkCongr(x_78, x_79, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_97; 
x_83 = lean_ctor_get(x_82, 0);
x_97 = !lean_is_exclusive(x_82);
if (x_97 == 0)
{
x_84 = x_82;
x_85 = x_97;
goto block_96;
}
else
{
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_86; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 0, x_83);
x_86 = x_80;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_83);
x_86 = x_95;
goto block_94;
}
block_94:
{
uint8_t x_87; lean_object* x_88; 
x_87 = 1;
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_86);
lean_ctor_set(x_12, 0, x_14);
x_88 = x_12;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_14);
lean_ctor_set(x_93, 1, x_86);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_87);
if (x_85 == 0)
{
lean_ctor_set(x_84, 0, x_88);
x_89 = x_84;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_88);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_del_object(x_80);
lean_dec_ref(x_14);
lean_del_object(x_12);
x_98 = lean_ctor_get(x_82, 0);
x_105 = !lean_is_exclusive(x_82);
if (x_105 == 0)
{
x_99 = x_82;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_82);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_mkCongr(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Simp_mkImpCongr___closed__2));
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_unsigned_to_nat(1892u);
x_4 = ((lean_object*)(l_Lean_Meta_Simp_mkImpCongr___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_Simp_mkImpCongr___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_56; 
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; size_t x_82; size_t x_83; uint8_t x_84; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_1, 1);
x_73 = lean_ctor_get(x_1, 2);
x_74 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_75 = lean_ctor_get(x_2, 0);
x_76 = lean_ctor_get(x_3, 0);
x_82 = lean_ptr_addr(x_72);
x_83 = lean_ptr_addr(x_75);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
x_77 = x_84;
goto block_81;
}
else
{
size_t x_85; size_t x_86; uint8_t x_87; 
x_85 = lean_ptr_addr(x_73);
x_86 = lean_ptr_addr(x_76);
x_87 = lean_usize_dec_eq(x_85, x_86);
x_77 = x_87;
goto block_81;
}
block_81:
{
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc(x_71);
lean_dec_ref(x_1);
lean_inc_ref(x_76);
lean_inc_ref(x_75);
x_78 = l_Lean_Expr_forallE___override(x_71, x_75, x_76, x_74);
x_56 = x_78;
goto block_70;
}
else
{
uint8_t x_79; 
x_79 = l_Lean_instBEqBinderInfo_beq(x_74, x_74);
if (x_79 == 0)
{
lean_object* x_80; 
lean_inc(x_71);
lean_dec_ref(x_1);
lean_inc_ref(x_76);
lean_inc_ref(x_75);
x_80 = l_Lean_Expr_forallE___override(x_71, x_75, x_76, x_74);
x_56 = x_80;
goto block_70;
}
else
{
x_56 = x_1;
goto block_70;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_1);
x_88 = lean_obj_once(&l_Lean_Meta_Simp_mkImpCongr___closed__3, &l_Lean_Meta_Simp_mkImpCongr___closed__3_once, _init_l_Lean_Meta_Simp_mkImpCongr___closed__3);
x_89 = l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(x_88);
x_56 = x_89;
goto block_70;
}
block_55:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_15 = l_Lean_Meta_Simp_Result_getProof(x_2, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_17 = l_Lean_Meta_Simp_Result_getProof(x_3, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_mkImpCongr(x_16, x_18, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_30; 
x_20 = lean_ctor_get(x_19, 0);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
x_21 = x_19;
x_22 = x_30;
goto block_29;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_25);
x_26 = x_21;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_9);
x_31 = lean_ctor_get(x_19, 0);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
x_32 = x_19;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_39 = lean_ctor_get(x_17, 0);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
x_40 = x_17;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
x_47 = lean_ctor_get(x_15, 0);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
x_48 = x_15;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
block_70:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; uint8_t x_67; 
lean_inc(x_58);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_67 = !lean_is_exclusive(x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_3, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_3, 0);
lean_dec(x_69);
x_59 = x_3;
x_60 = x_67;
goto block_66;
}
else
{
lean_dec(x_3);
x_59 = lean_box(0);
x_60 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_61; lean_object* x_62; 
x_61 = 1;
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_56);
x_62 = x_59;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_58);
x_62 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_63; 
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
x_9 = x_56;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = lean_box(0);
goto block_55;
}
}
else
{
x_9 = x_56;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = lean_box(0);
goto block_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_mkImpCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4));
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6));
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_8);
x_2 = x_11;
goto block_6;
}
else
{
x_2 = x_9;
goto block_6;
}
block_6:
{
if (x_2 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Expr_appArg_x21(x_1);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2));
x_5 = l_Lean_Expr_isAppOf(x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_appFn_x21(x_1);
lean_dec_ref(x_1);
x_4 = l_Lean_Expr_appFn_x21(x_3);
lean_dec_ref(x_3);
x_5 = l_Lean_Expr_appArg_x21(x_4);
lean_dec_ref(x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_30; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
x_15 = x_3;
x_16 = x_30;
goto block_29;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get_borrowed(x_17, x_13, x_2);
x_19 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
if (x_16 == 0)
{
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
x_20 = x_22;
goto block_21;
}
block_21:
{
x_5 = x_20;
x_6 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_inc(x_18);
x_23 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_18);
x_24 = lean_array_set(x_13, x_2, x_23);
x_25 = lean_box(x_19);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_24);
x_26 = x_15;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_5 = x_26;
x_6 = lean_box(0);
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_obj_once(&l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0, &l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0_once, _init_l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0);
x_8 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_8);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_8, x_10);
lean_dec(x_8);
lean_inc_ref(x_1);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_9, x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_13, x_14, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_34; 
x_19 = lean_ctor_get(x_18, 0);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
x_20 = x_18;
x_21 = x_34;
goto block_33;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_1);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_Expr_getAppFn(x_1);
lean_dec_ref(x_1);
x_29 = l_Lean_mkAppN(x_28, x_27);
lean_dec(x_27);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_29);
x_30 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_18, 0);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
x_36 = x_18;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_1, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_270; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_270 = !lean_is_exclusive(x_6);
if (x_270 == 0)
{
x_19 = x_6;
x_20 = x_270;
goto block_269;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_158; uint8_t x_159; 
x_32 = lean_array_uget_borrowed(x_3, x_5);
x_158 = lean_array_get_size(x_1);
x_159 = lean_nat_dec_lt(x_17, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_18, 0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_160);
x_161 = lean_infer_type(x_160, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_163 = l_Lean_Meta_whnfD(x_162, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Expr_isArrow(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_166 = lean_dsimp(x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_168 = l_Lean_Meta_Simp_mkCongrFun(x_18, x_167, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_21 = x_169;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_170 = lean_ctor_get(x_168, 0);
x_177 = !lean_is_exclusive(x_168);
if (x_177 == 0)
{
x_171 = x_168;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_178 = lean_ctor_get(x_166, 0);
x_185 = !lean_is_exclusive(x_166);
if (x_185 == 0)
{
x_179 = x_166;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_166);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
else
{
lean_object* x_186; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_186 = lean_simp(x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_188 = l_Lean_Meta_Simp_mkCongr(x_18, x_187, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
x_21 = x_189;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_197; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_190 = lean_ctor_get(x_188, 0);
x_197 = !lean_is_exclusive(x_188);
if (x_197 == 0)
{
x_191 = x_188;
x_192 = x_197;
goto block_196;
}
else
{
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_box(0);
x_192 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_193; 
if (x_192 == 0)
{
x_193 = x_191;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_190);
x_193 = x_195;
goto block_194;
}
block_194:
{
return x_193;
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_205; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_198 = lean_ctor_get(x_186, 0);
x_205 = !lean_is_exclusive(x_186);
if (x_205 == 0)
{
x_199 = x_186;
x_200 = x_205;
goto block_204;
}
else
{
lean_inc(x_198);
lean_dec(x_186);
x_199 = lean_box(0);
x_200 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_201; 
if (x_200 == 0)
{
x_201 = x_199;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_198);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; uint8_t x_213; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_206 = lean_ctor_get(x_163, 0);
x_213 = !lean_is_exclusive(x_163);
if (x_213 == 0)
{
x_207 = x_163;
x_208 = x_213;
goto block_212;
}
else
{
lean_inc(x_206);
lean_dec(x_163);
x_207 = lean_box(0);
x_208 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_209; 
if (x_208 == 0)
{
x_209 = x_207;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_206);
x_209 = x_211;
goto block_210;
}
block_210:
{
return x_209;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_221; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_214 = lean_ctor_get(x_161, 0);
x_221 = !lean_is_exclusive(x_161);
if (x_221 == 0)
{
x_215 = x_161;
x_216 = x_221;
goto block_220;
}
else
{
lean_inc(x_214);
lean_dec(x_161);
x_215 = lean_box(0);
x_216 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_217; 
if (x_216 == 0)
{
x_217 = x_215;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_214);
x_217 = x_219;
goto block_218;
}
block_218:
{
return x_217;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3));
x_223 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_222, x_12);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_144 = x_18;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_11;
x_150 = x_12;
x_151 = x_13;
x_152 = lean_box(0);
goto block_157;
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_226 = lean_array_fget_borrowed(x_1, x_17);
x_227 = lean_ctor_get_uint8(x_226, sizeof(void*)*1 + 1);
x_228 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5);
lean_inc(x_17);
x_229 = l_Nat_reprFast(x_17);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = l_Lean_MessageData_ofFormat(x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Nat_reprFast(x_158);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = l_Lean_MessageData_ofFormat(x_236);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
lean_inc(x_32);
x_241 = l_Lean_MessageData_ofExpr(x_32);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
if (x_227 == 0)
{
lean_object* x_259; 
x_259 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__12));
x_245 = x_259;
goto block_258;
}
else
{
lean_object* x_260; 
x_260 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__13));
x_245 = x_260;
goto block_258;
}
block_258:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = l_Lean_MessageData_ofFormat(x_246);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_222, x_248, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_249) == 0)
{
lean_dec_ref(x_249);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_144 = x_18;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_11;
x_150 = x_12;
x_151 = x_13;
x_152 = lean_box(0);
goto block_157;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_257; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_250 = lean_ctor_get(x_249, 0);
x_257 = !lean_is_exclusive(x_249);
if (x_257 == 0)
{
x_251 = x_249;
x_252 = x_257;
goto block_256;
}
else
{
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_box(0);
x_252 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_253; 
if (x_252 == 0)
{
x_253 = x_251;
goto block_254;
}
else
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_250);
x_253 = x_255;
goto block_254;
}
block_254:
{
return x_253;
}
}
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_268; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_261 = lean_ctor_get(x_223, 0);
x_268 = !lean_is_exclusive(x_223);
if (x_268 == 0)
{
x_262 = x_223;
x_263 = x_268;
goto block_267;
}
else
{
lean_inc(x_261);
lean_dec(x_223);
x_262 = lean_box(0);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_263 == 0)
{
x_264 = x_262;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_261);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
}
block_31:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_17, x_23);
lean_dec(x_17);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_24);
x_25 = x_19;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_21);
x_25 = x_30;
goto block_29;
}
block_29:
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_25;
goto _start;
}
}
block_49:
{
lean_object* x_39; 
lean_inc(x_32);
x_39 = l_Lean_Meta_Simp_mkCongrFun(x_38, x_32, x_33, x_36, x_37, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_21 = x_40;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_41 = lean_ctor_get(x_39, 0);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
x_42 = x_39;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
block_143:
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_58, sizeof(void*)*1 + 1);
lean_dec_ref(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_inc(x_51);
lean_inc_ref(x_57);
lean_inc(x_55);
lean_inc_ref(x_50);
lean_inc(x_32);
x_61 = lean_simp(x_32, x_53, x_56, x_52, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_Simp_mkCongr(x_59, x_62, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_21 = x_64;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_65 = lean_ctor_get(x_63, 0);
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
x_66 = x_63;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_73 = lean_ctor_get(x_61, 0);
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
x_74 = x_61;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_61);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_59, 0);
lean_inc(x_51);
lean_inc_ref(x_57);
lean_inc(x_55);
lean_inc_ref(x_50);
lean_inc_ref(x_81);
x_82 = lean_infer_type(x_81, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_51);
lean_inc_ref(x_57);
lean_inc(x_55);
lean_inc_ref(x_50);
x_84 = l_Lean_Meta_whnfD(x_83, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Expr_isArrow(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_51);
lean_inc_ref(x_57);
lean_inc(x_55);
lean_inc_ref(x_50);
lean_inc(x_32);
x_87 = lean_dsimp(x_32, x_53, x_56, x_52, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Lean_Meta_Simp_mkCongrFun(x_59, x_88, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_21 = x_90;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_91 = lean_ctor_get(x_89, 0);
x_98 = !lean_is_exclusive(x_89);
if (x_98 == 0)
{
x_92 = x_89;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_99 = lean_ctor_get(x_87, 0);
x_106 = !lean_is_exclusive(x_87);
if (x_106 == 0)
{
x_100 = x_87;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_87);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
else
{
lean_object* x_107; 
lean_inc(x_51);
lean_inc_ref(x_57);
lean_inc(x_55);
lean_inc_ref(x_50);
lean_inc(x_32);
x_107 = lean_simp(x_32, x_53, x_56, x_52, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l_Lean_Meta_Simp_mkCongr(x_59, x_108, x_50, x_55, x_57, x_51);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_21 = x_110;
x_22 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_111 = lean_ctor_get(x_109, 0);
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
x_112 = x_109;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_119 = lean_ctor_get(x_107, 0);
x_126 = !lean_is_exclusive(x_107);
if (x_126 == 0)
{
x_120 = x_107;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_107);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_127 = lean_ctor_get(x_84, 0);
x_134 = !lean_is_exclusive(x_84);
if (x_134 == 0)
{
x_128 = x_84;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_84);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_del_object(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_135 = lean_ctor_get(x_82, 0);
x_142 = !lean_is_exclusive(x_82);
if (x_142 == 0)
{
x_136 = x_82;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_dec(x_82);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
}
block_157:
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_array_fget_borrowed(x_1, x_17);
x_154 = lean_ctor_get_uint8(x_153, sizeof(void*)*1 + 4);
if (x_154 == 0)
{
lean_inc(x_153);
x_50 = x_148;
x_51 = x_151;
x_52 = x_147;
x_53 = x_145;
x_54 = lean_box(0);
x_55 = x_149;
x_56 = x_146;
x_57 = x_150;
x_58 = x_153;
x_59 = x_144;
goto block_143;
}
else
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 28);
if (x_155 == 0)
{
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
x_33 = x_148;
x_34 = x_151;
x_35 = lean_box(0);
x_36 = x_149;
x_37 = x_150;
x_38 = x_144;
goto block_49;
}
else
{
uint8_t x_156; 
x_156 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 14);
if (x_156 == 0)
{
lean_inc(x_153);
x_50 = x_148;
x_51 = x_151;
x_52 = x_147;
x_53 = x_145;
x_54 = lean_box(0);
x_55 = x_149;
x_56 = x_146;
x_57 = x_150;
x_58 = x_153;
x_59 = x_144;
goto block_143;
}
else
{
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
x_33 = x_148;
x_34 = x_151;
x_35 = lean_box(0);
x_36 = x_149;
x_37 = x_150;
x_38 = x_144;
goto block_49;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Meta_Simp_getConfig___redArg(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_14);
x_16 = l_Lean_Meta_getFunInfoNArgs(x_14, x_15, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_46; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_17, 1);
lean_dec(x_47);
x_19 = x_17;
x_20 = x_46;
goto block_45;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(0u);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_1);
x_22 = x_44;
goto block_43;
}
block_43:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_array_size(x_2);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2(x_18, x_13, x_2, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
lean_dec_ref(x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_34; 
x_26 = lean_ctor_get(x_25, 0);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
x_27 = x_25;
x_28 = x_34;
goto block_33;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_29);
x_30 = x_27;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_35 = lean_ctor_get(x_25, 0);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
x_36 = x_25;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_16, 0);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
x_49 = x_16;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_1);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_congrArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__5));
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(1817u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__4));
x_5 = ((lean_object*)(l_Lean_Meta_Simp_mkImpCongr___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_128; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_128 = !lean_is_exclusive(x_2);
if (x_128 == 0)
{
x_11 = x_2;
x_12 = x_128;
goto block_127;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_13; uint8_t x_114; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_117; lean_object* x_118; size_t x_119; size_t x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_1, 0);
x_118 = lean_ctor_get(x_1, 1);
x_119 = lean_ptr_addr(x_117);
x_120 = lean_ptr_addr(x_9);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
x_114 = x_121;
goto block_116;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_118);
x_123 = lean_ptr_addr(x_3);
x_124 = lean_usize_dec_eq(x_122, x_123);
x_114 = x_124;
goto block_116;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6);
x_126 = l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(x_125);
x_13 = x_126;
goto block_113;
}
block_113:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_14 = 1;
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_15 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_10);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_112; 
x_19 = lean_ctor_get(x_10, 0);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
x_20 = x_10;
x_21 = x_112;
goto block_111;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_22; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_22 = lean_infer_type(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_23);
x_24 = l_Lean_Meta_getLevel(x_23, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_26 = lean_infer_type(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_28 = l_Lean_Meta_getLevel(x_27, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_appFn_x21(x_1);
lean_dec_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_30);
x_31 = lean_infer_type(x_30, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_33 = l_Lean_Meta_whnfD(x_32, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_62; 
x_34 = lean_ctor_get(x_33, 0);
x_62 = !lean_is_exclusive(x_33);
if (x_62 == 0)
{
x_35 = x_33;
x_36 = x_62;
goto block_61;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_62;
goto block_61;
}
block_61:
{
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_38);
lean_dec_ref(x_34);
x_39 = 0;
lean_inc(x_23);
x_40 = l_Lean_mkLambda(x_37, x_39, x_23, x_38);
x_41 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__1));
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_mkConst(x_41, x_44);
x_46 = l_Lean_mkApp6(x_45, x_23, x_40, x_30, x_9, x_19, x_3);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_46);
x_47 = x_20;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_46);
x_47 = x_56;
goto block_55;
}
block_55:
{
uint8_t x_48; lean_object* x_49; 
x_48 = 1;
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_47);
lean_ctor_set(x_11, 0, x_13);
x_49 = x_11;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_47);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_49);
x_50 = x_35;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
x_57 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__3);
x_58 = l_Lean_indentExpr(x_30);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg(x_59, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_60;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_63 = lean_ctor_get(x_33, 0);
x_70 = !lean_is_exclusive(x_33);
if (x_70 == 0)
{
x_64 = x_33;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_33);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_71 = lean_ctor_get(x_31, 0);
x_78 = !lean_is_exclusive(x_31);
if (x_78 == 0)
{
x_72 = x_31;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_31);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_25);
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_79 = lean_ctor_get(x_28, 0);
x_86 = !lean_is_exclusive(x_28);
if (x_86 == 0)
{
x_80 = x_28;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_28);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_25);
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_26, 0);
x_94 = !lean_is_exclusive(x_26);
if (x_94 == 0)
{
x_88 = x_26;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_26);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_24, 0);
x_102 = !lean_is_exclusive(x_24);
if (x_102 == 0)
{
x_96 = x_24;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_24);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_22, 0);
x_110 = !lean_is_exclusive(x_22);
if (x_110 == 0)
{
x_104 = x_22;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_22);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
}
}
block_116:
{
if (x_114 == 0)
{
lean_object* x_115; 
lean_inc_ref(x_3);
lean_inc_ref(x_9);
x_115 = l_Lean_Expr_app___override(x_9, x_3);
x_13 = x_115;
goto block_113;
}
else
{
lean_inc_ref(x_1);
x_13 = x_1;
goto block_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_appArg_x21(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = lean_infer_type(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_10);
x_11 = l_Lean_Meta_getLevel(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = lean_infer_type(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_14);
x_15 = l_Lean_Meta_getLevel(x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
x_16 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_17 = x_15;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_mkConst(x_1, x_21);
x_23 = l_Lean_mkAppB(x_22, x_10, x_14);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_29 = lean_ctor_get(x_15, 0);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
x_30 = x_15;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_11, 0);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
x_38 = x_11;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_66; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_11 = x_3;
x_12 = x_66;
goto block_65;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_13; uint8_t x_52; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
x_57 = lean_ptr_addr(x_55);
x_58 = lean_ptr_addr(x_2);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
x_52 = x_59;
goto block_54;
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
x_60 = lean_ptr_addr(x_56);
x_61 = lean_ptr_addr(x_9);
x_62 = lean_usize_dec_eq(x_60, x_61);
x_52 = x_62;
goto block_54;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6);
x_64 = l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(x_63);
x_13 = x_64;
goto block_51;
}
block_51:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = 1;
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_15 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_10);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_50; 
x_19 = lean_ctor_get(x_10, 0);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
x_20 = x_10;
x_21 = x_50;
goto block_49;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_22; lean_object* x_23; 
x_22 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__1));
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(x_22, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_25 = x_23;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_28 = l_Lean_mkApp4(x_24, x_27, x_9, x_2, x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_28);
x_29 = x_20;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_28);
x_29 = x_38;
goto block_37;
}
block_37:
{
uint8_t x_30; lean_object* x_31; 
x_30 = 1;
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_13);
x_31 = x_11;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_29);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_31);
x_32 = x_25;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_del_object(x_20);
lean_dec(x_19);
lean_dec_ref(x_13);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_23, 0);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
x_42 = x_23;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
block_54:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_53 = l_Lean_Expr_app___override(x_2, x_9);
x_13 = x_53;
goto block_51;
}
else
{
lean_inc_ref(x_1);
x_13 = x_1;
goto block_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_134; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_134 = !lean_is_exclusive(x_3);
if (x_134 == 0)
{
x_13 = x_3;
x_14 = x_134;
goto block_133;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_15; uint8_t x_120; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_123; lean_object* x_124; size_t x_125; size_t x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_1, 0);
x_124 = lean_ctor_get(x_1, 1);
x_125 = lean_ptr_addr(x_123);
x_126 = lean_ptr_addr(x_9);
x_127 = lean_usize_dec_eq(x_125, x_126);
if (x_127 == 0)
{
x_120 = x_127;
goto block_122;
}
else
{
size_t x_128; size_t x_129; uint8_t x_130; 
x_128 = lean_ptr_addr(x_124);
x_129 = lean_ptr_addr(x_11);
x_130 = lean_usize_dec_eq(x_128, x_129);
x_120 = x_130;
goto block_122;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27___closed__6);
x_132 = l_panic___at___00Lean_Meta_Simp_mkImpCongr_spec__0(x_131);
x_15 = x_132;
goto block_119;
}
block_119:
{
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_16; lean_object* x_17; 
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_16 = 1;
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_17 = x_13;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_12);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_52; 
x_21 = lean_ctor_get(x_12, 0);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
x_22 = x_12;
x_23 = x_52;
goto block_51;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_24; lean_object* x_25; 
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrArg_x27___closed__1));
lean_inc_ref(x_1);
x_25 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(x_24, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_42; 
x_26 = lean_ctor_get(x_25, 0);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
x_27 = x_25;
x_28 = x_42;
goto block_41;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_30 = l_Lean_mkApp4(x_26, x_29, x_11, x_9, x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_30);
x_31 = x_22;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_30);
x_31 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 1;
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_15);
x_33 = x_13;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_31);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_33);
x_34 = x_27;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_del_object(x_22);
lean_dec(x_21);
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_25, 0);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
x_44 = x_25;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_84; 
x_53 = lean_ctor_get(x_10, 0);
x_84 = !lean_is_exclusive(x_10);
if (x_84 == 0)
{
x_54 = x_10;
x_55 = x_84;
goto block_83;
}
else
{
lean_inc(x_53);
lean_dec(x_10);
x_54 = lean_box(0);
x_55 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_56; lean_object* x_57; 
x_56 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__1));
lean_inc_ref(x_1);
x_57 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(x_56, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_74; 
x_58 = lean_ctor_get(x_57, 0);
x_74 = !lean_is_exclusive(x_57);
if (x_74 == 0)
{
x_59 = x_57;
x_60 = x_74;
goto block_73;
}
else
{
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lean_Expr_appFn_x21(x_1);
lean_dec_ref(x_1);
x_62 = l_Lean_mkApp4(x_58, x_61, x_9, x_53, x_11);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_62);
x_63 = x_54;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_62);
x_63 = x_72;
goto block_71;
}
block_71:
{
uint8_t x_64; lean_object* x_65; 
x_64 = 1;
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_63);
lean_ctor_set(x_13, 0, x_15);
x_65 = x_13;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_15);
lean_ctor_set(x_70, 1, x_63);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_64);
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_65);
x_66 = x_59;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_del_object(x_54);
lean_dec(x_53);
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_57, 0);
x_82 = !lean_is_exclusive(x_57);
if (x_82 == 0)
{
x_76 = x_57;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_118; 
x_85 = lean_ctor_get(x_10, 0);
lean_inc(x_85);
lean_dec_ref(x_10);
x_86 = lean_ctor_get(x_12, 0);
x_118 = !lean_is_exclusive(x_12);
if (x_118 == 0)
{
x_87 = x_12;
x_88 = x_118;
goto block_117;
}
else
{
lean_inc(x_86);
lean_dec(x_12);
x_87 = lean_box(0);
x_88 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_89; lean_object* x_90; 
x_89 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___closed__3));
lean_inc_ref(x_1);
x_90 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrPrefix(x_89, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_108; 
x_91 = lean_ctor_get(x_90, 0);
x_108 = !lean_is_exclusive(x_90);
if (x_108 == 0)
{
x_92 = x_90;
x_93 = x_108;
goto block_107;
}
else
{
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = l_Lean_Expr_appFn_x21(x_1);
x_95 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_96 = l_Lean_mkApp6(x_91, x_94, x_9, x_95, x_11, x_85, x_86);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_96);
x_97 = x_87;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_96);
x_97 = x_106;
goto block_105;
}
block_105:
{
uint8_t x_98; lean_object* x_99; 
x_98 = 1;
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_97);
lean_ctor_set(x_13, 0, x_15);
x_99 = x_13;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_15);
lean_ctor_set(x_104, 1, x_97);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_98);
if (x_93 == 0)
{
lean_ctor_set(x_92, 0, x_99);
x_100 = x_92;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_del_object(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_90, 0);
x_116 = !lean_is_exclusive(x_90);
if (x_116 == 0)
{
x_110 = x_90;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_90);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
}
}
}
block_122:
{
if (x_120 == 0)
{
lean_object* x_121; 
lean_inc_ref(x_11);
lean_inc_ref(x_9);
x_121 = l_Lean_Expr_app___override(x_9, x_11);
x_15 = x_121;
goto block_119;
}
else
{
lean_inc_ref(x_1);
x_15 = x_1;
goto block_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_76; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_13 = x_11;
x_14 = x_76;
goto block_75;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_73; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 1);
lean_dec(x_74);
x_19 = x_12;
x_20 = x_73;
goto block_72;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_28);
lean_ctor_set(x_71, 3, x_27);
lean_ctor_set(x_71, 4, x_26);
x_29 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_22);
x_30 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_32, 1);
lean_dec(x_64);
x_39 = x_32;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_47);
lean_ctor_set(x_61, 4, x_46);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_42);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_Lean_Meta_Simp_instInhabitedResult_default;
x_53 = l_instInhabitedOfMonad___redArg(x_51, x_52);
x_54 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_panic_fn(x_55, x_1);
x_57 = lean_apply_8(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_57;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2));
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_unsigned_to_nat(717u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_16);
x_20 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit(x_1, x_2, x_3, x_16, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_171; 
x_21 = lean_ctor_get(x_20, 0);
x_171 = !lean_is_exclusive(x_20);
if (x_171 == 0)
{
x_22 = x_20;
x_23 = x_171;
goto block_170;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_3);
x_25 = lean_nat_dec_lt(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_del_object(x_22);
lean_dec(x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_16);
x_26 = lean_infer_type(x_16, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_28 = l_Lean_Meta_whnfD(x_27, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_isArrow(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_17);
x_31 = lean_dsimp(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(x_4, x_21, x_32, x_9, x_10, x_11, x_12);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_34 = lean_ctor_get(x_31, 0);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
x_35 = x_31;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_17);
x_42 = lean_simp(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(x_4, x_21, x_43, x_9, x_10, x_11, x_12);
return x_44;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_42;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_45 = lean_ctor_get(x_28, 0);
x_52 = !lean_is_exclusive(x_28);
if (x_52 == 0)
{
x_46 = x_28;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_53 = lean_ctor_get(x_26, 0);
x_60 = !lean_is_exclusive(x_26);
if (x_60 == 0)
{
x_54 = x_26;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_26);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_169; 
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__3));
x_62 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_61, x_11);
x_63 = lean_ctor_get(x_62, 0);
x_169 = !lean_is_exclusive(x_62);
if (x_169 == 0)
{
x_64 = x_62;
x_65 = x_169;
goto block_168;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_129; 
x_66 = lean_array_fget_borrowed(x_3, x_19);
x_129 = lean_unbox(x_63);
lean_dec(x_63);
if (x_129 == 0)
{
lean_del_object(x_64);
lean_del_object(x_22);
lean_dec(x_19);
x_115 = x_6;
x_116 = x_7;
x_117 = x_8;
x_118 = x_9;
x_119 = x_10;
x_120 = x_11;
x_121 = x_12;
x_122 = lean_box(0);
goto block_128;
}
else
{
uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 1);
x_131 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__5);
x_132 = l_Nat_reprFast(x_19);
if (x_65 == 0)
{
lean_ctor_set_tag(x_64, 3);
lean_ctor_set(x_64, 0, x_132);
x_133 = x_64;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_132);
x_133 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = l_Lean_MessageData_ofFormat(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__7);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Nat_reprFast(x_24);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 0, x_138);
x_139 = x_22;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_138);
x_139 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__9);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_inc_ref(x_17);
x_144 = l_Lean_MessageData_ofExpr(x_17);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__11);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
if (x_130 == 0)
{
lean_object* x_162; 
x_162 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__12));
x_148 = x_162;
goto block_161;
}
else
{
lean_object* x_163; 
x_163 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_congrArgs_spec__2___closed__13));
x_148 = x_163;
goto block_161;
}
block_161:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Lean_MessageData_ofFormat(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_61, x_151, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_dec_ref(x_152);
x_115 = x_6;
x_116 = x_7;
x_117 = x_8;
x_118 = x_9;
x_119 = x_10;
x_120 = x_11;
x_121 = x_12;
x_122 = lean_box(0);
goto block_128;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_153 = lean_ctor_get(x_152, 0);
x_160 = !lean_is_exclusive(x_152);
if (x_160 == 0)
{
x_154 = x_152;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
}
}
}
block_114:
{
uint8_t x_75; 
x_75 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 1);
if (x_75 == 0)
{
lean_object* x_76; 
lean_inc(x_74);
lean_inc_ref(x_72);
lean_inc(x_69);
lean_inc_ref(x_67);
lean_inc_ref(x_17);
x_76 = lean_simp(x_17, x_68, x_73, x_70, x_67, x_69, x_72, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(x_4, x_21, x_77, x_67, x_69, x_72, x_74);
return x_78;
}
else
{
lean_dec(x_74);
lean_dec_ref(x_72);
lean_dec(x_69);
lean_dec_ref(x_67);
lean_dec(x_21);
lean_dec_ref(x_4);
return x_76;
}
}
else
{
lean_object* x_79; 
lean_inc(x_74);
lean_inc_ref(x_72);
lean_inc(x_69);
lean_inc_ref(x_67);
lean_inc_ref(x_16);
x_79 = lean_infer_type(x_16, x_67, x_69, x_72, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_74);
lean_inc_ref(x_72);
lean_inc(x_69);
lean_inc_ref(x_67);
x_81 = l_Lean_Meta_whnfD(x_80, x_67, x_69, x_72, x_74);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Expr_isArrow(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_inc(x_74);
lean_inc_ref(x_72);
lean_inc(x_69);
lean_inc_ref(x_67);
lean_inc_ref(x_17);
x_84 = lean_dsimp(x_17, x_68, x_73, x_70, x_67, x_69, x_72, x_74);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(x_4, x_21, x_85, x_67, x_69, x_72, x_74);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_74);
lean_dec_ref(x_72);
lean_dec(x_69);
lean_dec_ref(x_67);
lean_dec(x_21);
lean_dec_ref(x_4);
x_87 = lean_ctor_get(x_84, 0);
x_94 = !lean_is_exclusive(x_84);
if (x_94 == 0)
{
x_88 = x_84;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_object* x_95; 
lean_inc(x_74);
lean_inc_ref(x_72);
lean_inc(x_69);
lean_inc_ref(x_67);
lean_inc_ref(x_17);
x_95 = lean_simp(x_17, x_68, x_73, x_70, x_67, x_69, x_72, x_74);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongr_x27(x_4, x_21, x_96, x_67, x_69, x_72, x_74);
return x_97;
}
else
{
lean_dec(x_74);
lean_dec_ref(x_72);
lean_dec(x_69);
lean_dec_ref(x_67);
lean_dec(x_21);
lean_dec_ref(x_4);
return x_95;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_21);
lean_dec_ref(x_4);
x_98 = lean_ctor_get(x_81, 0);
x_105 = !lean_is_exclusive(x_81);
if (x_105 == 0)
{
x_99 = x_81;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_81);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_21);
lean_dec_ref(x_4);
x_106 = lean_ctor_get(x_79, 0);
x_113 = !lean_is_exclusive(x_79);
if (x_113 == 0)
{
x_107 = x_79;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_79);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
}
block_128:
{
uint8_t x_123; 
x_123 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 4);
if (x_123 == 0)
{
x_67 = x_118;
x_68 = x_115;
x_69 = x_119;
x_70 = x_117;
x_71 = lean_box(0);
x_72 = x_120;
x_73 = x_116;
x_74 = x_121;
goto block_114;
}
else
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 28);
if (x_124 == 0)
{
lean_object* x_125; 
lean_inc_ref(x_17);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
x_125 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(x_4, x_21, x_17, x_118, x_119, x_120, x_121);
return x_125;
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 14);
if (x_126 == 0)
{
x_67 = x_118;
x_68 = x_115;
x_69 = x_119;
x_70 = x_117;
x_71 = lean_box(0);
x_72 = x_120;
x_73 = x_116;
x_74 = x_121;
goto block_114;
}
else
{
lean_object* x_127; 
lean_inc_ref(x_17);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
x_127 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrFun_x27(x_4, x_21, x_17, x_118, x_119, x_120, x_121);
return x_127;
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
lean_dec(x_19);
lean_dec_ref(x_4);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_20;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_172 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__3);
x_173 = l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0(x_172, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_173;
}
}
else
{
lean_object* x_174; 
lean_dec_ref(x_4);
x_174 = lean_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_174;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAppUsingCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_Simp_getConfig___redArg(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Expr_getAppFn(x_1);
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_13);
lean_inc_ref(x_12);
x_14 = l_Lean_Meta_getFunInfoNArgs(x_12, x_13, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit(x_12, x_11, x_16, x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_13);
lean_dec_ref(x_16);
lean_dec(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_19 = x_14;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAppUsingCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpAppUsingCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; lean_object* x_11; uint8_t x_12; 
x_5 = 1;
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_unbox(x_11);
switch (x_12) {
case 0:
{
x_6 = x_4;
goto block_10;
}
case 2:
{
x_6 = x_4;
goto block_10;
}
default: 
{
return x_5;
}
}
block_10:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_Meta_instBEqCongrArgKind_beq(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_getFunInfo(x_1, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_getCongrSimpKinds(x_1, x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_97; 
x_12 = lean_ctor_get(x_11, 0);
x_97 = !lean_is_exclusive(x_11);
if (x_97 == 0)
{
x_13 = x_11;
x_14 = x_97;
goto block_96;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_12);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
else
{
if (x_21 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_20);
x_24 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__0(x_12, x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_del_object(x_13);
x_25 = l_Lean_Meta_Simp_getConfig___redArg(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*3 + 23);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_10, x_12, x_24, x_3, x_4, x_5, x_6);
return x_28;
}
else
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_30);
lean_inc(x_29);
x_31 = l_Lean_Meta_mkCongrSimpForConst_x3f(x_29, x_30, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_54, 1);
x_56 = lean_ctor_get(x_54, 2);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_eq(x_57, x_20);
if (x_58 == 0)
{
lean_dec_ref(x_32);
goto block_53;
}
else
{
uint8_t x_59; 
x_59 = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg(x_56, x_12, x_57);
if (x_59 == 0)
{
lean_dec_ref(x_32);
goto block_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_93; 
lean_dec_ref(x_1);
lean_dec(x_12);
lean_dec(x_10);
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1));
x_61 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_60, x_5);
x_62 = lean_ctor_get(x_61, 0);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
x_63 = x_61;
x_64 = x_93;
goto block_92;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_93;
goto block_92;
}
block_92:
{
uint8_t x_65; 
x_65 = lean_unbox(x_62);
lean_dec(x_62);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_32);
x_66 = x_63;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_32);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_del_object(x_63);
x_69 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__7);
x_70 = l_Lean_Expr_getAppFn(x_55);
x_71 = l_Lean_MessageData_ofExpr(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_60, x_74, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_75, 0);
lean_dec(x_83);
x_76 = x_75;
x_77 = x_82;
goto block_81;
}
else
{
lean_dec(x_75);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_32);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_32);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec_ref(x_32);
x_84 = lean_ctor_get(x_75, 0);
x_91 = !lean_is_exclusive(x_75);
if (x_91 == 0)
{
x_85 = x_75;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_75);
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
}
}
else
{
lean_object* x_94; 
lean_dec(x_32);
x_94 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_10, x_12, x_24, x_3, x_4, x_5, x_6);
return x_94;
}
block_53:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__1));
x_34 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_33, x_5);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_10, x_12, x_24, x_3, x_4, x_5, x_6);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__3);
lean_inc(x_29);
x_39 = l_Lean_MessageData_ofName(x_29);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5, &l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___closed__5);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_33, x_42, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec_ref(x_43);
x_44 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_10, x_12, x_24, x_3, x_4, x_5, x_6);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_1);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_45 = lean_ctor_get(x_43, 0);
x_52 = !lean_is_exclusive(x_43);
if (x_52 == 0)
{
x_46 = x_43;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_31;
}
}
else
{
lean_object* x_95; 
x_95 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_10, x_12, x_24, x_3, x_4, x_5, x_6);
return x_95;
}
}
}
}
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_8);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_11, 0);
x_105 = !lean_is_exclusive(x_11);
if (x_105 == 0)
{
x_99 = x_11;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_11);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_9, 0);
x_113 = !lean_is_exclusive(x_9);
if (x_113 == 0)
{
x_107 = x_9;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_9);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg(x_1, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_is_matcher(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg(x_1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_13, x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Expr_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_st_ref_get(x_5);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg(x_12, x_1);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_inc_ref(x_1);
x_14 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkCongrSimp_x3f_go_x3f___redArg(x_1, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_38; 
x_15 = lean_ctor_get(x_14, 0);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
x_16 = x_14;
x_17 = x_38;
goto block_37;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_36; 
x_18 = lean_st_ref_take(x_5);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 2);
x_22 = lean_ctor_get(x_18, 3);
x_23 = lean_ctor_get(x_18, 4);
x_24 = lean_ctor_get(x_18, 5);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
x_25 = x_18;
x_26 = x_36;
goto block_35;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_27; lean_object* x_28; 
lean_inc(x_15);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_20, x_1, x_15);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_27);
x_28 = x_25;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_23);
lean_ctor_set(x_34, 5, x_24);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_st_ref_set(x_5, x_28);
if (x_17 == 0)
{
x_30 = x_16;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_15);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_14;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_13, 0);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
x_40 = x_13;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 0);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_apply_9(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_27; 
x_14 = l_Lean_Expr_constName_x21(x_3);
x_15 = l_Lean_Meta_isMatcher___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__2___redArg(x_14, x_10);
x_16 = lean_ctor_get(x_15, 0);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
x_17 = x_15;
x_18 = x_27;
goto block_26;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_19; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_del_object(x_17);
x_20 = lean_box(0);
x_21 = lean_apply_9(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_22 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = ((lean_object*)(l_Lean_Meta_Simp_mkCongrSimp_x3f___closed__0));
x_13 = l_Lean_Expr_isConst(x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkCongrSimp_x3f___lam__1___boxed), 11, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_1);
x_16 = lean_box(0);
x_17 = l_Lean_profileitM___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__3___redArg(x_12, x_10, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_mkCongrSimp_x3f_spec__1_spec__3_spec__6_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_76; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_13 = x_11;
x_14 = x_76;
goto block_75;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_73; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 1);
lean_dec(x_74);
x_19 = x_12;
x_20 = x_73;
goto block_72;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_28);
lean_ctor_set(x_71, 3, x_27);
lean_ctor_set(x_71, 4, x_26);
x_29 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_22);
x_30 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_32, 1);
lean_dec(x_64);
x_39 = x_32;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_47);
lean_ctor_set(x_61, 4, x_46);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_42);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_box(0);
x_53 = l_instInhabitedOfMonad___redArg(x_51, x_52);
x_54 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_panic_fn(x_55, x_1);
x_57 = lean_apply_8(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_57;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_76; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_13 = x_11;
x_14 = x_76;
goto block_75;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_73; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 1);
lean_dec(x_74);
x_19 = x_12;
x_20 = x_73;
goto block_72;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_28);
lean_ctor_set(x_71, 3, x_27);
lean_ctor_set(x_71, 4, x_26);
x_29 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_22);
x_30 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_32, 1);
lean_dec(x_64);
x_39 = x_32;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_47);
lean_ctor_set(x_61, 4, x_46);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_42);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_box(0);
x_53 = l_instInhabitedOfMonad___redArg(x_51, x_52);
x_54 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_panic_fn(x_55, x_1);
x_57 = lean_apply_8(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_57;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(817u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_7, x_6);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_227; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 0);
x_227 = !lean_is_exclusive(x_8);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_8, 1);
lean_dec(x_228);
x_31 = x_8;
x_32 = x_227;
goto block_226;
}
else
{
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_box(0);
x_32 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_224; 
x_33 = lean_ctor_get(x_25, 0);
x_224 = !lean_is_exclusive(x_25);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_25, 1);
lean_dec(x_225);
x_34 = x_25;
x_35 = x_224;
goto block_223;
}
else
{
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_box(0);
x_35 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_221; 
x_36 = lean_ctor_get(x_26, 0);
x_221 = !lean_is_exclusive(x_26);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_26, 1);
lean_dec(x_222);
x_37 = x_26;
x_38 = x_221;
goto block_220;
}
else
{
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_box(0);
x_38 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_218; 
x_39 = lean_ctor_get(x_27, 0);
x_218 = !lean_is_exclusive(x_27);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_27, 1);
lean_dec(x_219);
x_40 = x_27;
x_41 = x_218;
goto block_217;
}
else
{
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_box(0);
x_41 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_215; 
x_42 = lean_ctor_get(x_28, 0);
x_215 = !lean_is_exclusive(x_28);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_28, 1);
lean_dec(x_216);
x_43 = x_28;
x_44 = x_215;
goto block_214;
}
else
{
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_box(0);
x_44 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_213; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
x_213 = !lean_is_exclusive(x_29);
if (x_213 == 0)
{
x_47 = x_29;
x_48 = x_213;
goto block_212;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
x_51 = lean_ctor_get(x_30, 2);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
if (x_48 == 0)
{
x_53 = x_47;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_45);
lean_ctor_set(x_71, 1, x_46);
x_53 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_54; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_53);
x_54 = x_43;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_42);
lean_ctor_set(x_69, 1, x_53);
x_54 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_55; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_54);
x_55 = x_40;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_39);
lean_ctor_set(x_67, 1, x_54);
x_55 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_56; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_55);
x_56 = x_37;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_36);
lean_ctor_set(x_65, 1, x_55);
x_56 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_57; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_56);
x_57 = x_34;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_56);
x_57 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_58; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_57);
x_58 = x_31;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_30);
lean_ctor_set(x_61, 1, x_57);
x_58 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
}
}
else
{
lean_object* x_72; uint8_t x_73; uint8_t x_208; 
lean_inc(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
x_208 = !lean_is_exclusive(x_30);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_30, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_30, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_30, 0);
lean_dec(x_211);
x_72 = x_30;
x_73 = x_208;
goto block_207;
}
else
{
lean_dec(x_30);
x_72 = lean_box(0);
x_73 = x_208;
goto block_207;
}
block_207:
{
uint8_t x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 14);
x_75 = lean_array_fget(x_49, x_50);
x_76 = lean_nat_dec_eq(x_1, x_2);
x_77 = lean_array_uget_borrowed(x_5, x_7);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_50, x_78);
lean_dec(x_50);
if (x_73 == 0)
{
lean_ctor_set(x_72, 1, x_79);
x_80 = x_72;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_79);
lean_ctor_set(x_206, 2, x_51);
x_80 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
if (x_74 == 0)
{
uint8_t x_184; uint8_t x_185; uint8_t x_186; 
x_184 = lean_unbox(x_39);
lean_dec(x_39);
x_185 = lean_unbox(x_42);
lean_dec(x_42);
x_186 = lean_unbox(x_46);
lean_dec(x_46);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_131 = x_33;
x_132 = x_36;
x_133 = x_184;
x_134 = x_185;
x_135 = x_45;
x_136 = x_186;
x_137 = x_9;
x_138 = x_10;
x_139 = x_11;
x_140 = x_12;
x_141 = x_13;
x_142 = x_14;
x_143 = x_15;
x_144 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_array_get_size(x_4);
x_188 = lean_nat_dec_lt(x_45, x_187);
if (x_188 == 0)
{
uint8_t x_189; uint8_t x_190; uint8_t x_191; 
x_189 = lean_unbox(x_39);
lean_dec(x_39);
x_190 = lean_unbox(x_42);
lean_dec(x_42);
x_191 = lean_unbox(x_46);
lean_dec(x_46);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_131 = x_33;
x_132 = x_36;
x_133 = x_189;
x_134 = x_190;
x_135 = x_45;
x_136 = x_191;
x_137 = x_9;
x_138 = x_10;
x_139 = x_11;
x_140 = x_12;
x_141 = x_13;
x_142 = x_14;
x_143 = x_15;
x_144 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_array_fget_borrowed(x_4, x_45);
x_193 = lean_ctor_get_uint8(x_192, sizeof(void*)*1 + 4);
if (x_193 == 0)
{
uint8_t x_194; uint8_t x_195; uint8_t x_196; 
x_194 = lean_unbox(x_39);
lean_dec(x_39);
x_195 = lean_unbox(x_42);
lean_dec(x_42);
x_196 = lean_unbox(x_46);
lean_dec(x_46);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_131 = x_33;
x_132 = x_36;
x_133 = x_194;
x_134 = x_195;
x_135 = x_45;
x_136 = x_196;
x_137 = x_9;
x_138 = x_10;
x_139 = x_11;
x_140 = x_12;
x_141 = x_13;
x_142 = x_14;
x_143 = x_15;
x_144 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_75);
lean_del_object(x_47);
lean_del_object(x_43);
lean_del_object(x_40);
lean_del_object(x_37);
lean_del_object(x_34);
lean_del_object(x_31);
lean_inc(x_77);
x_197 = lean_array_push(x_36, x_77);
x_198 = lean_nat_add(x_45, x_78);
lean_dec(x_45);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_46);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_42);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_39);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_33);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_80);
lean_ctor_set(x_204, 1, x_203);
x_17 = x_204;
x_18 = lean_box(0);
goto block_22;
}
}
}
block_110:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_nat_add(x_85, x_78);
lean_dec(x_85);
x_89 = lean_box(x_86);
if (x_48 == 0)
{
lean_ctor_set(x_47, 1, x_89);
lean_ctor_set(x_47, 0, x_88);
x_90 = x_47;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_88);
lean_ctor_set(x_109, 1, x_89);
x_90 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(x_84);
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_90);
lean_ctor_set(x_43, 0, x_91);
x_92 = x_43;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_90);
x_92 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_box(x_83);
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_92);
lean_ctor_set(x_40, 0, x_93);
x_94 = x_40;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_92);
x_94 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_95; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_94);
lean_ctor_set(x_37, 0, x_82);
x_95 = x_37;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_94);
x_95 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_96; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_95);
lean_ctor_set(x_34, 0, x_81);
x_96 = x_34;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_95);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_96);
lean_ctor_set(x_31, 0, x_80);
x_97 = x_31;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_80);
lean_ctor_set(x_99, 1, x_96);
x_97 = x_99;
goto block_98;
}
block_98:
{
x_17 = x_97;
x_18 = lean_box(0);
goto block_22;
}
}
}
}
}
}
}
block_120:
{
lean_object* x_119; 
x_119 = lean_array_push(x_116, x_114);
x_81 = x_115;
x_82 = x_119;
x_83 = x_111;
x_84 = x_112;
x_85 = x_113;
x_86 = x_117;
x_87 = lean_box(0);
goto block_110;
}
block_130:
{
uint8_t x_129; 
x_129 = lean_expr_eqv(x_77, x_124);
lean_dec_ref(x_124);
if (x_129 == 0)
{
x_81 = x_121;
x_82 = x_125;
x_83 = x_122;
x_84 = x_126;
x_85 = x_123;
x_86 = x_76;
x_87 = lean_box(0);
goto block_110;
}
else
{
x_81 = x_121;
x_82 = x_125;
x_83 = x_122;
x_84 = x_126;
x_85 = x_123;
x_86 = x_127;
x_87 = lean_box(0);
goto block_110;
}
}
block_183:
{
uint8_t x_145; 
x_145 = lean_unbox(x_75);
lean_dec(x_75);
switch (x_145) {
case 0:
{
lean_object* x_146; 
lean_inc(x_77);
x_146 = lean_dsimp(x_77, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_expr_eqv(x_77, x_147);
if (x_148 == 0)
{
x_111 = x_133;
x_112 = x_134;
x_113 = x_135;
x_114 = x_147;
x_115 = x_131;
x_116 = x_132;
x_117 = x_76;
x_118 = lean_box(0);
goto block_120;
}
else
{
x_111 = x_133;
x_112 = x_134;
x_113 = x_135;
x_114 = x_147;
x_115 = x_131;
x_116 = x_132;
x_117 = x_136;
x_118 = lean_box(0);
goto block_120;
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_dec(x_135);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_80);
lean_del_object(x_47);
lean_del_object(x_43);
lean_del_object(x_40);
lean_del_object(x_37);
lean_del_object(x_34);
lean_del_object(x_31);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_149 = lean_ctor_get(x_146, 0);
x_156 = !lean_is_exclusive(x_146);
if (x_156 == 0)
{
x_150 = x_146;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
case 3:
{
lean_object* x_157; 
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_inc(x_77);
x_157 = lean_array_push(x_132, x_77);
x_81 = x_131;
x_82 = x_157;
x_83 = x_76;
x_84 = x_134;
x_85 = x_135;
x_86 = x_136;
x_87 = lean_box(0);
goto block_110;
}
case 5:
{
lean_object* x_158; 
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_inc(x_77);
x_158 = lean_array_push(x_132, x_77);
x_81 = x_131;
x_82 = x_158;
x_83 = x_133;
x_84 = x_134;
x_85 = x_135;
x_86 = x_136;
x_87 = lean_box(0);
goto block_110;
}
case 2:
{
lean_object* x_159; 
lean_inc(x_77);
x_159 = lean_simp(x_77, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_array_push(x_131, x_160);
lean_inc_ref(x_161);
x_164 = lean_array_push(x_132, x_161);
if (lean_obj_tag(x_162) == 0)
{
x_121 = x_163;
x_122 = x_133;
x_123 = x_135;
x_124 = x_161;
x_125 = x_164;
x_126 = x_134;
x_127 = x_136;
x_128 = lean_box(0);
goto block_130;
}
else
{
lean_dec_ref(x_162);
x_121 = x_163;
x_122 = x_133;
x_123 = x_135;
x_124 = x_161;
x_125 = x_164;
x_126 = x_76;
x_127 = x_136;
x_128 = lean_box(0);
goto block_130;
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_135);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_80);
lean_del_object(x_47);
lean_del_object(x_43);
lean_del_object(x_40);
lean_del_object(x_37);
lean_del_object(x_34);
lean_del_object(x_31);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_165 = lean_ctor_get(x_159, 0);
x_172 = !lean_is_exclusive(x_159);
if (x_172 == 0)
{
x_166 = x_159;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
default: 
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__1);
x_174 = l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_173, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_174) == 0)
{
lean_dec_ref(x_174);
x_81 = x_131;
x_82 = x_132;
x_83 = x_133;
x_84 = x_134;
x_85 = x_135;
x_86 = x_136;
x_87 = lean_box(0);
goto block_110;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec(x_135);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_80);
lean_del_object(x_47);
lean_del_object(x_43);
lean_del_object(x_40);
lean_del_object(x_37);
lean_del_object(x_34);
lean_del_object(x_31);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_175 = lean_ctor_get(x_174, 0);
x_182 = !lean_is_exclusive(x_174);
if (x_182 == 0)
{
x_176 = x_174;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_7, x_19);
x_7 = x_20;
x_8 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(884u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_4, x_3);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_288; 
x_22 = lean_ctor_get(x_5, 1);
x_288 = !lean_is_exclusive(x_5);
if (x_288 == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_5, 0);
lean_dec(x_289);
x_23 = x_5;
x_24 = x_288;
goto block_287;
}
else
{
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_288;
goto block_287;
}
block_287:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_285; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 0);
x_285 = !lean_is_exclusive(x_25);
if (x_285 == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_25, 1);
lean_dec(x_286);
x_30 = x_25;
x_31 = x_285;
goto block_284;
}
else
{
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_282; 
x_32 = lean_ctor_get(x_22, 0);
x_282 = !lean_is_exclusive(x_22);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_22, 1);
lean_dec(x_283);
x_33 = x_22;
x_34 = x_282;
goto block_281;
}
else
{
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_box(0);
x_34 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_279; 
x_35 = lean_ctor_get(x_26, 0);
x_279 = !lean_is_exclusive(x_26);
if (x_279 == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_26, 1);
lean_dec(x_280);
x_36 = x_26;
x_37 = x_279;
goto block_278;
}
else
{
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_box(0);
x_37 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_276; 
x_38 = lean_ctor_get(x_27, 0);
x_276 = !lean_is_exclusive(x_27);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_27, 1);
lean_dec(x_277);
x_39 = x_27;
x_40 = x_276;
goto block_275;
}
else
{
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_box(0);
x_40 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_274; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
x_274 = !lean_is_exclusive(x_28);
if (x_274 == 0)
{
x_43 = x_28;
x_44 = x_274;
goto block_273;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_box(0);
x_44 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
x_47 = lean_ctor_get(x_29, 2);
x_48 = lean_box(0);
x_49 = lean_nat_dec_lt(x_46, x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
if (x_44 == 0)
{
x_50 = x_43;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_42);
x_50 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_51; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_50);
x_51 = x_39;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_38);
lean_ctor_set(x_66, 1, x_50);
x_51 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_52; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_51);
x_52 = x_36;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_35);
lean_ctor_set(x_64, 1, x_51);
x_52 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_53; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_52);
x_53 = x_30;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_29);
lean_ctor_set(x_62, 1, x_52);
x_53 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_54; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_53);
x_54 = x_33;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_32);
lean_ctor_set(x_60, 1, x_53);
x_54 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_55; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_54);
lean_ctor_set(x_23, 0, x_48);
x_55 = x_23;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_54);
x_55 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_269; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
x_269 = !lean_is_exclusive(x_29);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_29, 2);
lean_dec(x_270);
x_271 = lean_ctor_get(x_29, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_29, 0);
lean_dec(x_272);
x_69 = x_29;
x_70 = x_269;
goto block_268;
}
else
{
lean_dec(x_29);
x_69 = lean_box(0);
x_70 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_32, 0);
x_72 = lean_ctor_get(x_32, 1);
x_73 = lean_ctor_get(x_32, 2);
x_74 = lean_array_fget(x_45, x_46);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_46, x_75);
lean_dec(x_46);
if (x_70 == 0)
{
lean_ctor_set(x_69, 1, x_76);
x_77 = x_69;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_267, 0, x_45);
lean_ctor_set(x_267, 1, x_76);
lean_ctor_set(x_267, 2, x_47);
x_77 = x_267;
goto block_266;
}
block_266:
{
uint8_t x_78; 
x_78 = lean_nat_dec_lt(x_72, x_73);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_74);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
if (x_44 == 0)
{
x_79 = x_43;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_41);
lean_ctor_set(x_97, 1, x_42);
x_79 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_80; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_79);
x_80 = x_39;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_38);
lean_ctor_set(x_95, 1, x_79);
x_80 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_81; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_80);
x_81 = x_36;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_35);
lean_ctor_set(x_93, 1, x_80);
x_81 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_82; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_81);
lean_ctor_set(x_30, 0, x_77);
x_82 = x_30;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_81);
x_82 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_83; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_82);
x_83 = x_33;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_32);
lean_ctor_set(x_89, 1, x_82);
x_83 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_84; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_83);
lean_ctor_set(x_23, 0, x_48);
x_84 = x_23;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_48);
lean_ctor_set(x_87, 1, x_83);
x_84 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
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
lean_object* x_98; uint8_t x_99; uint8_t x_262; 
lean_inc(x_73);
lean_inc(x_72);
lean_inc_ref(x_71);
x_262 = !lean_is_exclusive(x_32);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_32, 2);
lean_dec(x_263);
x_264 = lean_ctor_get(x_32, 1);
lean_dec(x_264);
x_265 = lean_ctor_get(x_32, 0);
lean_dec(x_265);
x_98 = x_32;
x_99 = x_262;
goto block_261;
}
else
{
lean_dec(x_32);
x_98 = lean_box(0);
x_99 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_array_uget_borrowed(x_2, x_4);
x_101 = lean_array_fget(x_71, x_72);
x_102 = lean_nat_add(x_72, x_75);
lean_dec(x_72);
if (x_99 == 0)
{
lean_ctor_set(x_98, 1, x_102);
x_103 = x_98;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_260, 0, x_71);
lean_ctor_set(x_260, 1, x_102);
lean_ctor_set(x_260, 2, x_73);
x_103 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_inc(x_100);
x_131 = l_Lean_Expr_app___override(x_38, x_100);
x_132 = l_Lean_Expr_bindingBody_x21(x_42);
lean_dec(x_42);
x_133 = lean_unbox(x_74);
lean_dec(x_74);
switch (x_133) {
case 0:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
x_134 = lean_array_push(x_41, x_101);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_35);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_77);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_103);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_48);
lean_ctor_set(x_140, 1, x_139);
x_14 = x_140;
x_15 = lean_box(0);
goto block_19;
}
case 3:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_101);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
lean_inc(x_100);
x_141 = lean_array_push(x_41, x_100);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_132);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_35);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_77);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_103);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_48);
lean_ctor_set(x_147, 1, x_146);
x_14 = x_147;
x_15 = lean_box(0);
goto block_19;
}
case 5:
{
lean_object* x_148; lean_object* x_149; lean_object* x_159; 
lean_dec(x_101);
lean_inc(x_100);
x_148 = lean_array_push(x_41, x_100);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_100);
x_159 = lean_infer_type(x_100, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = l_Lean_Expr_bindingDomain_x21(x_132);
x_162 = lean_expr_instantiate_rev(x_161, x_148);
lean_dec_ref(x_161);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_162);
x_163 = l_Lean_Meta_isExprDefEq(x_160, x_162, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_162);
x_166 = l_Lean_Meta_trySynthInstance(x_162, x_48, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_168; 
lean_dec_ref(x_162);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_104 = x_131;
x_105 = x_148;
x_106 = x_132;
x_107 = x_168;
x_108 = lean_box(0);
goto block_130;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_167);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_169 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__1));
x_170 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg(x_169, x_11);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_dec_ref(x_162);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_149 = lean_box(0);
goto block_158;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__3);
x_174 = l_Lean_indentExpr(x_162);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg(x_169, x_175, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_dec_ref(x_176);
x_149 = lean_box(0);
goto block_158;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_184; 
lean_dec_ref(x_148);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_dec(x_35);
x_177 = lean_ctor_get(x_176, 0);
x_184 = !lean_is_exclusive(x_176);
if (x_184 == 0)
{
x_178 = x_176;
x_179 = x_184;
goto block_183;
}
else
{
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_box(0);
x_179 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_180; 
if (x_179 == 0)
{
x_180 = x_178;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_177);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_dec_ref(x_162);
lean_dec_ref(x_148);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_dec(x_35);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_185 = lean_ctor_get(x_170, 0);
x_192 = !lean_is_exclusive(x_170);
if (x_192 == 0)
{
x_186 = x_170;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_170);
x_186 = lean_box(0);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_187 == 0)
{
x_188 = x_186;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_185);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_200; 
lean_dec_ref(x_162);
lean_dec_ref(x_148);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_193 = lean_ctor_get(x_166, 0);
x_200 = !lean_is_exclusive(x_166);
if (x_200 == 0)
{
x_194 = x_166;
x_195 = x_200;
goto block_199;
}
else
{
lean_inc(x_193);
lean_dec(x_166);
x_194 = lean_box(0);
x_195 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_196; 
if (x_195 == 0)
{
x_196 = x_194;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_193);
x_196 = x_198;
goto block_197;
}
block_197:
{
return x_196;
}
}
}
}
else
{
lean_dec_ref(x_162);
lean_inc(x_100);
x_104 = x_131;
x_105 = x_148;
x_106 = x_132;
x_107 = x_100;
x_108 = lean_box(0);
goto block_130;
}
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_208; 
lean_dec_ref(x_162);
lean_dec_ref(x_148);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_201 = lean_ctor_get(x_163, 0);
x_208 = !lean_is_exclusive(x_163);
if (x_208 == 0)
{
x_202 = x_163;
x_203 = x_208;
goto block_207;
}
else
{
lean_inc(x_201);
lean_dec(x_163);
x_202 = lean_box(0);
x_203 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_204; 
if (x_203 == 0)
{
x_204 = x_202;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_201);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_dec_ref(x_148);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_209 = lean_ctor_get(x_159, 0);
x_216 = !lean_is_exclusive(x_159);
if (x_216 == 0)
{
x_210 = x_159;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_159);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
block_158:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__0));
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_132);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_131);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_35);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_77);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_103);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_150);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
case 2:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_101);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
x_217 = l_Lean_Meta_Simp_instInhabitedResult_default;
lean_inc(x_100);
x_218 = lean_array_push(x_41, x_100);
x_219 = lean_array_get_borrowed(x_217, x_1, x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_219);
lean_inc(x_100);
x_220 = l_Lean_Meta_Simp_Result_getProof_x27(x_100, x_219, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get(x_219, 0);
x_223 = lean_nat_add(x_35, x_75);
lean_dec(x_35);
lean_inc(x_221);
lean_inc_ref(x_222);
x_224 = l_Lean_mkAppB(x_131, x_222, x_221);
lean_inc_ref(x_222);
x_225 = lean_array_push(x_218, x_222);
x_226 = lean_array_push(x_225, x_221);
x_227 = l_Lean_Expr_bindingBody_x21(x_132);
lean_dec_ref(x_132);
x_228 = l_Lean_Expr_bindingBody_x21(x_227);
lean_dec_ref(x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_224);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_223);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_77);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_103);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_48);
lean_ctor_set(x_234, 1, x_233);
x_14 = x_234;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_218);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_dec(x_35);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_235 = lean_ctor_get(x_220, 0);
x_242 = !lean_is_exclusive(x_220);
if (x_242 == 0)
{
x_236 = x_220;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_220);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
default: 
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_101);
lean_del_object(x_43);
lean_del_object(x_39);
lean_del_object(x_36);
lean_del_object(x_33);
lean_del_object(x_30);
lean_del_object(x_23);
x_243 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___closed__4);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_244 = l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_243, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_244);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_41);
lean_ctor_set(x_245, 1, x_132);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_131);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_35);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_77);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_103);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_48);
lean_ctor_set(x_250, 1, x_249);
x_14 = x_250;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_103);
lean_dec_ref(x_77);
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_251 = lean_ctor_get(x_244, 0);
x_258 = !lean_is_exclusive(x_244);
if (x_258 == 0)
{
x_252 = x_244;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_244);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
}
}
block_130:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_inc_ref(x_107);
x_109 = l_Lean_Expr_app___override(x_104, x_107);
x_110 = lean_array_push(x_105, x_107);
x_111 = l_Lean_Expr_bindingBody_x21(x_106);
lean_dec_ref(x_106);
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_111);
lean_ctor_set(x_43, 0, x_110);
x_112 = x_43;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_110);
lean_ctor_set(x_129, 1, x_111);
x_112 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_113; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_112);
lean_ctor_set(x_39, 0, x_109);
x_113 = x_39;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_109);
lean_ctor_set(x_127, 1, x_112);
x_113 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_114; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_113);
x_114 = x_36;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_113);
x_114 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_115; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_114);
lean_ctor_set(x_30, 0, x_77);
x_115 = x_30;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_77);
lean_ctor_set(x_123, 1, x_114);
x_115 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_116; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_115);
lean_ctor_set(x_33, 0, x_103);
x_116 = x_33;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_103);
lean_ctor_set(x_121, 1, x_115);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_116);
lean_ctor_set(x_23, 0, x_48);
x_117 = x_23;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_48);
lean_ctor_set(x_119, 1, x_116);
x_117 = x_119;
goto block_118;
}
block_118:
{
x_14 = x_117;
x_15 = lean_box(0);
goto block_19;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_5 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__2));
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(885u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_224; 
x_12 = lean_ctor_get(x_11, 0);
x_224 = !lean_is_exclusive(x_11);
if (x_224 == 0)
{
x_13 = x_11;
x_14 = x_224;
goto block_223;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_224;
goto block_223;
}
block_223:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_218; 
x_15 = lean_ctor_get(x_12, 0);
x_218 = !lean_is_exclusive(x_12);
if (x_218 == 0)
{
x_16 = x_12;
x_17 = x_218;
goto block_217;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_20);
lean_dec(x_15);
x_21 = lean_array_get_size(x_20);
x_22 = l_Lean_Expr_getAppNumArgs(x_1);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_del_object(x_13);
x_28 = lean_obj_once(&l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0, &l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0_once, _init_l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__0);
lean_inc(x_22);
x_29 = lean_mk_array(x_22, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_22, x_30);
lean_inc_ref(x_1);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_29, x_31);
x_33 = lean_array_get_size(x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_10);
x_34 = l_Lean_Meta_getFunInfoNArgs(x_10, x_33, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_208; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Simp_getConfig___redArg(x_3);
x_37 = lean_ctor_get(x_36, 0);
x_208 = !lean_is_exclusive(x_36);
if (x_208 == 0)
{
x_38 = x_36;
x_39 = x_208;
goto block_207;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_205; 
x_40 = lean_ctor_get(x_35, 0);
x_205 = !lean_is_exclusive(x_35);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_35, 1);
lean_dec(x_206);
x_41 = x_35;
x_42 = x_205;
goto block_204;
}
else
{
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = ((lean_object*)(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__0));
x_45 = l_Array_toSubarray___redArg(x_20, x_43, x_21);
x_46 = ((lean_object*)(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__5));
lean_inc_ref(x_45);
if (x_42 == 0)
{
lean_ctor_set(x_41, 1, x_46);
lean_ctor_set(x_41, 0, x_45);
x_47 = x_41;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_45);
lean_ctor_set(x_203, 1, x_46);
x_47 = x_203;
goto block_202;
}
block_202:
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = lean_array_size(x_32);
x_49 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_50 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_21, x_22, x_37, x_40, x_32, x_48, x_49, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_40);
lean_dec(x_37);
lean_dec(x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_193; 
x_51 = lean_ctor_get(x_50, 0);
x_193 = !lean_is_exclusive(x_50);
if (x_193 == 0)
{
x_52 = x_50;
x_53 = x_193;
goto block_192;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_190; 
x_54 = lean_ctor_get(x_51, 1);
x_190 = !lean_is_exclusive(x_51);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_51, 0);
lean_dec(x_191);
x_55 = x_51;
x_56 = x_190;
goto block_189;
}
else
{
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_box(0);
x_56 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_187; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 0);
x_187 = !lean_is_exclusive(x_54);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_54, 1);
lean_dec(x_188);
x_61 = x_54;
x_62 = x_187;
goto block_186;
}
else
{
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_184; 
x_63 = lean_ctor_get(x_57, 0);
x_184 = !lean_is_exclusive(x_57);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_57, 1);
lean_dec(x_185);
x_64 = x_57;
x_65 = x_184;
goto block_183;
}
else
{
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_box(0);
x_65 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_181; 
x_66 = lean_ctor_get(x_58, 0);
x_181 = !lean_is_exclusive(x_58);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_58, 1);
lean_dec(x_182);
x_67 = x_58;
x_68 = x_181;
goto block_180;
}
else
{
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_box(0);
x_68 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_179; 
x_69 = lean_ctor_get(x_59, 0);
x_70 = lean_ctor_get(x_59, 1);
x_179 = !lean_is_exclusive(x_59);
if (x_179 == 0)
{
x_71 = x_59;
x_72 = x_179;
goto block_178;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_59);
x_71 = lean_box(0);
x_72 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_70, 1);
lean_inc(x_160);
lean_dec(x_70);
x_161 = lean_unbox(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_160);
lean_del_object(x_71);
lean_dec(x_69);
lean_del_object(x_67);
lean_dec(x_66);
lean_del_object(x_64);
lean_dec(x_63);
lean_del_object(x_61);
lean_dec(x_60);
lean_del_object(x_55);
lean_del_object(x_52);
lean_dec_ref(x_45);
lean_dec_ref(x_32);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_23);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_164);
x_165 = x_38;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_164);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
else
{
uint8_t x_168; 
lean_dec_ref(x_1);
x_168 = lean_unbox(x_69);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_unbox(x_66);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
lean_del_object(x_71);
lean_dec(x_69);
lean_del_object(x_67);
lean_dec(x_66);
lean_del_object(x_64);
lean_del_object(x_61);
lean_dec(x_60);
lean_del_object(x_55);
lean_del_object(x_52);
lean_dec_ref(x_45);
lean_dec_ref(x_32);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_170 = l_Lean_mkAppN(x_10, x_63);
lean_dec(x_63);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_unbox(x_160);
lean_dec(x_160);
lean_ctor_set_uint8(x_172, sizeof(void*)*2, x_173);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_172);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_174);
x_175 = x_38;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_174);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
else
{
lean_dec(x_160);
lean_del_object(x_38);
lean_dec_ref(x_10);
goto block_159;
}
}
else
{
lean_dec(x_160);
lean_del_object(x_38);
lean_dec_ref(x_10);
goto block_159;
}
}
block_94:
{
uint8_t x_77; 
x_77 = lean_unbox(x_69);
lean_dec(x_69);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_74);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_79);
x_80 = x_16;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_79);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_80);
x_81 = x_52;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
else
{
lean_object* x_86; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_73);
x_86 = x_16;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_73);
x_86 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_74);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_88);
x_89 = x_52;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_88);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
block_159:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_array_get_size(x_63);
x_96 = l_Array_toSubarray___redArg(x_63, x_43, x_95);
x_97 = lean_box(0);
if (x_72 == 0)
{
lean_ctor_set(x_71, 1, x_18);
lean_ctor_set(x_71, 0, x_44);
x_98 = x_71;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_44);
lean_ctor_set(x_158, 1, x_18);
x_98 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_99; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_98);
lean_ctor_set(x_67, 0, x_19);
x_99 = x_67;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_19);
lean_ctor_set(x_156, 1, x_98);
x_99 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_100; 
if (x_65 == 0)
{
lean_ctor_set(x_64, 1, x_99);
lean_ctor_set(x_64, 0, x_43);
x_100 = x_64;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_43);
lean_ctor_set(x_154, 1, x_99);
x_100 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_101; 
if (x_62 == 0)
{
lean_ctor_set(x_61, 1, x_100);
lean_ctor_set(x_61, 0, x_45);
x_101 = x_61;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_45);
lean_ctor_set(x_152, 1, x_100);
x_101 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_102; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 1, x_101);
lean_ctor_set(x_55, 0, x_96);
x_102 = x_55;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_96);
lean_ctor_set(x_150, 1, x_101);
x_102 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_60, x_32, x_48, x_49, x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_32);
lean_dec(x_60);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_140; 
x_105 = lean_ctor_get(x_104, 0);
x_140 = !lean_is_exclusive(x_104);
if (x_140 == 0)
{
x_106 = x_104;
x_107 = x_140;
goto block_139;
}
else
{
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_box(0);
x_107 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_ctor_get(x_108, 1);
x_110 = lean_ctor_get(x_109, 1);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 0);
lean_inc(x_113);
lean_dec(x_105);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_del_object(x_106);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_expr_instantiate_rev(x_116, x_115);
lean_dec(x_115);
lean_dec(x_116);
x_118 = ((lean_object*)(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__6));
x_119 = lean_unsigned_to_nat(3u);
x_120 = l_Lean_Expr_isAppOfArity(x_117, x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_117);
lean_dec(x_114);
lean_dec(x_69);
lean_dec(x_66);
lean_del_object(x_52);
lean_del_object(x_16);
x_121 = lean_obj_once(&l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7, &l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7_once, _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___closed__7);
x_122 = l_panic___at___00Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__3(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_122;
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_123 = l_Lean_Expr_appArg_x21(x_117);
lean_dec_ref(x_117);
x_124 = lean_unbox(x_66);
lean_dec(x_66);
if (x_124 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_73 = x_114;
x_74 = x_120;
x_75 = x_123;
x_76 = lean_box(0);
goto block_94;
}
else
{
lean_object* x_125; 
x_125 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_123, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_73 = x_114;
x_74 = x_120;
x_75 = x_126;
x_76 = lean_box(0);
goto block_94;
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_114);
lean_dec(x_69);
lean_del_object(x_52);
lean_del_object(x_16);
x_127 = lean_ctor_get(x_125, 0);
x_134 = !lean_is_exclusive(x_125);
if (x_134 == 0)
{
x_128 = x_125;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_69);
lean_dec(x_66);
lean_del_object(x_52);
lean_del_object(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_113, 0);
lean_inc(x_135);
lean_dec_ref(x_113);
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_135);
x_136 = x_106;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_135);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_148; 
lean_dec(x_69);
lean_dec(x_66);
lean_del_object(x_52);
lean_del_object(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_141 = lean_ctor_get(x_104, 0);
x_148 = !lean_is_exclusive(x_104);
if (x_148 == 0)
{
x_142 = x_104;
x_143 = x_148;
goto block_147;
}
else
{
lean_inc(x_141);
lean_dec(x_104);
x_142 = lean_box(0);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_143 == 0)
{
x_144 = x_142;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_141);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
}
}
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
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_201; 
lean_dec_ref(x_45);
lean_del_object(x_38);
lean_dec_ref(x_32);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_50, 0);
x_201 = !lean_is_exclusive(x_50);
if (x_201 == 0)
{
x_195 = x_50;
x_196 = x_201;
goto block_200;
}
else
{
lean_inc(x_194);
lean_dec(x_50);
x_195 = lean_box(0);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
if (x_196 == 0)
{
x_197 = x_195;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_194);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_dec_ref(x_32);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_34, 0);
x_216 = !lean_is_exclusive(x_34);
if (x_216 == 0)
{
x_210 = x_34;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_34);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_219 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_219);
x_220 = x_13;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_219);
x_220 = x_222;
goto block_221;
}
block_221:
{
return x_220;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_232; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_225 = lean_ctor_get(x_11, 0);
x_232 = !lean_is_exclusive(x_11);
if (x_232 == 0)
{
x_226 = x_11;
x_227 = x_232;
goto block_231;
}
else
{
lean_inc(x_225);
lean_dec(x_11);
x_226 = lean_box(0);
x_227 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_228; 
if (x_227 == 0)
{
x_228 = x_226;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_225);
x_228 = x_230;
goto block_229;
}
block_229:
{
return x_228;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_12);
x_13 = l_Lean_Meta_mkCongrFun(x_4, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_10 = x_1;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = l_Lean_mkAppN(x_9, x_2);
x_13 = 1;
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_14 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_8);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_57; 
x_21 = lean_ctor_get(x_1, 0);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 1);
lean_dec(x_58);
x_22 = x_1;
x_23 = x_57;
goto block_56;
}
else
{
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_55; 
x_24 = lean_ctor_get(x_8, 0);
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
x_25 = x_8;
x_26 = x_55;
goto block_54;
}
else
{
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = x_55;
goto block_54;
}
block_54:
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_array_size(x_2);
x_28 = 0;
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_Result_addExtraArgs_spec__0(x_2, x_27, x_28, x_24, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_45; 
x_30 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_31 = x_29;
x_32 = x_45;
goto block_44;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_mkAppN(x_21, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_34 = x_25;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_30);
x_34 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_35; lean_object* x_36; 
x_35 = 1;
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_34);
lean_ctor_set(x_22, 0, x_33);
x_36 = x_22;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_35);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_36);
x_37 = x_31;
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
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_del_object(x_25);
lean_del_object(x_22);
lean_dec_ref(x_21);
x_46 = lean_ctor_get(x_29, 0);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
x_47 = x_29;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_32; 
x_8 = lean_ctor_get(x_1, 0);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
x_9 = x_1;
x_10 = x_32;
goto block_31;
}
else
{
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_Result_addExtraArgs(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
x_13 = x_11;
x_14 = x_22;
goto block_21;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_12);
x_15 = x_9;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_del_object(x_9);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_57; 
x_33 = lean_ctor_get(x_1, 0);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
x_34 = x_1;
x_35 = x_57;
goto block_56;
}
else
{
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Simp_Result_addExtraArgs(x_33, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_36, 0);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
x_38 = x_36;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_40; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_37);
x_40 = x_34;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_37);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_40);
x_41 = x_38;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_del_object(x_34);
x_48 = lean_ctor_get(x_36, 0);
x_55 = !lean_is_exclusive(x_36);
if (x_55 == 0)
{
x_49 = x_36;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
default: 
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_1);
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; uint8_t x_91; 
x_91 = !lean_is_exclusive(x_1);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_1, 0);
lean_dec(x_92);
x_60 = x_1;
x_61 = x_91;
goto block_90;
}
else
{
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_89; 
x_62 = lean_ctor_get(x_58, 0);
x_89 = !lean_is_exclusive(x_58);
if (x_89 == 0)
{
x_63 = x_58;
x_64 = x_89;
goto block_88;
}
else
{
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Simp_Result_addExtraArgs(x_62, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_79; 
x_66 = lean_ctor_get(x_65, 0);
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
x_67 = x_65;
x_68 = x_79;
goto block_78;
}
else
{
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_69; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_66);
x_69 = x_63;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_66);
x_69 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_70; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_69);
x_70 = x_60;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_69);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_70);
x_71 = x_67;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
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
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_del_object(x_63);
lean_del_object(x_60);
x_80 = lean_ctor_get(x_65, 0);
x_87 = !lean_is_exclusive(x_65);
if (x_87 == 0)
{
x_81 = x_65;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_65);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Step_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkAppN(x_3, x_2);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
case 1:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_13 = x_1;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_mkAppN(x_12, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
default: 
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_22 = x_1;
x_23 = x_37;
goto block_36;
}
else
{
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
x_24 = lean_ctor_get(x_21, 0);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
x_25 = x_21;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_mkAppN(x_24, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_27);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_28);
x_29 = x_22;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = 1;
x_13 = 1;
x_14 = 1;
x_15 = lean_usize_sub(x_3, x_14);
x_20 = lean_array_uget_borrowed(x_2, x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_inc(x_20);
x_23 = lean_array_push(x_22, x_20);
x_24 = l_Lean_Meta_mkLambdaFVars(x_23, x_5, x_1, x_12, x_1, x_12, x_13, x_6, x_7, x_8, x_9);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_26 = l_Lean_Meta_mkFunExt(x_25, x_6, x_7, x_8, x_9);
x_16 = x_26;
goto block_19;
}
else
{
x_16 = x_24;
goto block_19;
}
block_19:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_3 = x_15;
x_5 = x_17;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_16;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_58; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
x_11 = x_1;
x_12 = x_58;
goto block_57;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_58;
goto block_57;
}
block_57:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_9, x_8, x_13, x_8, x_13, x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_48; 
x_16 = lean_ctor_get(x_15, 0);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
x_17 = x_15;
x_18 = x_48;
goto block_47;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_19; lean_object* x_20; 
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_del_object(x_17);
lean_del_object(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_13);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec_ref(x_10);
x_32 = lean_array_get_size(x_2);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = x_31;
x_20 = lean_box(0);
goto block_28;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_32);
x_36 = 0;
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addLambdas_spec__0(x_8, x_2, x_35, x_36, x_31, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_19 = x_38;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_del_object(x_17);
lean_dec(x_16);
lean_del_object(x_11);
x_39 = lean_ctor_get(x_37, 0);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
x_40 = x_37;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_16);
x_22 = x_11;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_21);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_13);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_49 = lean_ctor_get(x_15, 0);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
x_50 = x_15;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_1);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addLambdas(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = 1;
x_13 = 1;
x_14 = 1;
x_15 = lean_usize_sub(x_3, x_14);
x_20 = lean_array_uget_borrowed(x_2, x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_inc(x_20);
x_23 = lean_array_push(x_22, x_20);
x_24 = l_Lean_Meta_mkLambdaFVars(x_23, x_5, x_1, x_12, x_1, x_12, x_13, x_6, x_7, x_8, x_9);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_26 = l_Lean_Meta_mkForallCongr(x_25, x_6, x_7, x_8, x_9);
x_16 = x_26;
goto block_19;
}
else
{
x_16 = x_24;
goto block_19;
}
block_19:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_3 = x_15;
x_5 = x_17;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_16;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_58; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
x_11 = x_1;
x_12 = x_58;
goto block_57;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_58;
goto block_57;
}
block_57:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_2, x_9, x_8, x_13, x_13, x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_48; 
x_16 = lean_ctor_get(x_15, 0);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
x_17 = x_15;
x_18 = x_48;
goto block_47;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_19; lean_object* x_20; 
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_del_object(x_17);
lean_del_object(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_13);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec_ref(x_10);
x_32 = lean_array_get_size(x_2);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = x_31;
x_20 = lean_box(0);
goto block_28;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_32);
x_36 = 0;
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Simp_Result_addForalls_spec__0(x_8, x_2, x_35, x_36, x_31, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_19 = x_38;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_del_object(x_17);
lean_dec(x_16);
lean_del_object(x_11);
x_39 = lean_ctor_get(x_37, 0);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
x_40 = x_37;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_16);
x_22 = x_11;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_21);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_13);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_49 = lean_ctor_get(x_15, 0);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
x_50 = x_15;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_1);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addForalls(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_65; 
x_8 = l_Lean_Meta_Context_config(x_3);
x_9 = lean_ctor_get_uint8(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, 1);
x_11 = lean_ctor_get_uint8(x_8, 2);
x_12 = lean_ctor_get_uint8(x_8, 3);
x_13 = lean_ctor_get_uint8(x_8, 4);
x_14 = lean_ctor_get_uint8(x_8, 5);
x_15 = lean_ctor_get_uint8(x_8, 6);
x_16 = lean_ctor_get_uint8(x_8, 7);
x_17 = lean_ctor_get_uint8(x_8, 8);
x_18 = lean_ctor_get_uint8(x_8, 10);
x_19 = lean_ctor_get_uint8(x_8, 11);
x_20 = lean_ctor_get_uint8(x_8, 12);
x_21 = lean_ctor_get_uint8(x_8, 13);
x_22 = lean_ctor_get_uint8(x_8, 14);
x_23 = lean_ctor_get_uint8(x_8, 15);
x_24 = lean_ctor_get_uint8(x_8, 16);
x_25 = lean_ctor_get_uint8(x_8, 17);
x_26 = lean_ctor_get_uint8(x_8, 18);
x_65 = !lean_is_exclusive(x_8);
if (x_65 == 0)
{
x_27 = x_8;
x_28 = x_65;
goto block_64;
}
else
{
lean_dec(x_8);
x_27 = lean_box(0);
x_28 = x_65;
goto block_64;
}
block_64:
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_3, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 6);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
if (x_28 == 0)
{
x_39 = x_27;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_63, 0, x_9);
lean_ctor_set_uint8(x_63, 1, x_10);
lean_ctor_set_uint8(x_63, 2, x_11);
lean_ctor_set_uint8(x_63, 3, x_12);
lean_ctor_set_uint8(x_63, 4, x_13);
lean_ctor_set_uint8(x_63, 5, x_14);
lean_ctor_set_uint8(x_63, 6, x_15);
lean_ctor_set_uint8(x_63, 7, x_16);
lean_ctor_set_uint8(x_63, 8, x_17);
lean_ctor_set_uint8(x_63, 10, x_18);
lean_ctor_set_uint8(x_63, 11, x_19);
lean_ctor_set_uint8(x_63, 12, x_20);
lean_ctor_set_uint8(x_63, 13, x_21);
lean_ctor_set_uint8(x_63, 14, x_22);
lean_ctor_set_uint8(x_63, 15, x_23);
lean_ctor_set_uint8(x_63, 16, x_24);
lean_ctor_set_uint8(x_63, 17, x_25);
lean_ctor_set_uint8(x_63, 18, x_26);
x_39 = x_63;
goto block_62;
}
block_62:
{
uint64_t x_40; lean_object* x_41; uint8_t x_42; uint8_t x_54; 
lean_ctor_set_uint8(x_39, 9, x_1);
x_40 = l_Lean_Meta_Context_configKey(x_3);
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_3, 6);
lean_dec(x_55);
x_56 = lean_ctor_get(x_3, 5);
lean_dec(x_56);
x_57 = lean_ctor_get(x_3, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_3, 0);
lean_dec(x_61);
x_41 = x_3;
x_42 = x_54;
goto block_53;
}
else
{
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = x_54;
goto block_53;
}
block_53:
{
uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
x_43 = 2;
x_44 = lean_uint64_shift_right(x_40, x_43);
x_45 = lean_uint64_shift_left(x_44, x_43);
x_46 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_47 = lean_uint64_lor(x_45, x_46);
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_47);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_48);
x_49 = x_41;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_30);
lean_ctor_set(x_52, 2, x_31);
lean_ctor_set(x_52, 3, x_32);
lean_ctor_set(x_52, 4, x_33);
lean_ctor_set(x_52, 5, x_34);
lean_ctor_set(x_52, 6, x_35);
lean_ctor_set_uint8(x_52, sizeof(void*)*7, x_29);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 1, x_36);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 2, x_37);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 3, x_38);
x_49 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_50; 
x_50 = lean_apply_5(x_2, x_49, x_4, x_5, x_6, lean_box(0));
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_144; 
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0);
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 2);
x_13 = lean_ctor_get(x_10, 3);
x_14 = lean_ctor_get(x_10, 4);
x_144 = !lean_is_exclusive(x_10);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_10, 1);
lean_dec(x_145);
x_15 = x_10;
x_16 = x_144;
goto block_143;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1));
x_18 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2));
lean_inc_ref(x_11);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_13);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_12);
if (x_16 == 0)
{
lean_ctor_set(x_15, 4, x_22);
lean_ctor_set(x_15, 3, x_23);
lean_ctor_set(x_15, 2, x_24);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_21);
x_25 = x_15;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_21);
lean_ctor_set(x_142, 1, x_17);
lean_ctor_set(x_142, 2, x_24);
lean_ctor_set(x_142, 3, x_23);
lean_ctor_set(x_142, 4, x_22);
x_25 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_139; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
x_27 = l_ReaderT_instMonad___redArg(x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
lean_closure_set(x_28, 2, x_27);
x_29 = l_instMonadControlTOfPure___redArg(x_28);
x_30 = lean_ctor_get(x_9, 0);
x_139 = !lean_is_exclusive(x_9);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_9, 1);
lean_dec(x_140);
x_31 = x_9;
x_32 = x_139;
goto block_138;
}
else
{
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_box(0);
x_32 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_136; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_136 = !lean_is_exclusive(x_30);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_30, 1);
lean_dec(x_137);
x_37 = x_30;
x_38 = x_136;
goto block_135;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc_ref(x_33);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_36);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_34);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_42);
lean_ctor_set(x_37, 3, x_43);
lean_ctor_set(x_37, 2, x_44);
lean_ctor_set(x_37, 1, x_17);
lean_ctor_set(x_37, 0, x_41);
x_45 = x_37;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_41);
lean_ctor_set(x_134, 1, x_17);
lean_ctor_set(x_134, 2, x_44);
lean_ctor_set(x_134, 3, x_43);
lean_ctor_set(x_134, 4, x_42);
x_45 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_46; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 0, x_45);
x_46 = x_31;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_45);
lean_ctor_set(x_132, 1, x_18);
x_46 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_129; 
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = lean_ctor_get(x_47, 0);
x_129 = !lean_is_exclusive(x_47);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_47, 1);
lean_dec(x_130);
x_49 = x_47;
x_50 = x_129;
goto block_128;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_126; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 2);
x_53 = lean_ctor_get(x_48, 3);
x_54 = lean_ctor_get(x_48, 4);
x_126 = !lean_is_exclusive(x_48);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_48, 1);
lean_dec(x_127);
x_55 = x_48;
x_56 = x_126;
goto block_125;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
x_55 = lean_box(0);
x_56 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3));
x_58 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4));
lean_inc_ref(x_51);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_59, 0, x_51);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_64, 0, x_52);
if (x_56 == 0)
{
lean_ctor_set(x_55, 4, x_62);
lean_ctor_set(x_55, 3, x_63);
lean_ctor_set(x_55, 2, x_64);
lean_ctor_set(x_55, 1, x_57);
lean_ctor_set(x_55, 0, x_61);
x_65 = x_55;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_61);
lean_ctor_set(x_124, 1, x_57);
lean_ctor_set(x_124, 2, x_64);
lean_ctor_set(x_124, 3, x_63);
lean_ctor_set(x_124, 4, x_62);
x_65 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_66; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_65);
x_66 = x_49;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_65);
lean_ctor_set(x_122, 1, x_58);
x_66 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; uint8_t x_120; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec_ref(x_1);
x_69 = l_Lean_Meta_Context_config(x_3);
x_70 = lean_ctor_get_uint8(x_69, 0);
x_71 = lean_ctor_get_uint8(x_69, 1);
x_72 = lean_ctor_get_uint8(x_69, 2);
x_73 = lean_ctor_get_uint8(x_69, 3);
x_74 = lean_ctor_get_uint8(x_69, 4);
x_75 = lean_ctor_get_uint8(x_69, 5);
x_76 = lean_ctor_get_uint8(x_69, 6);
x_77 = lean_ctor_get_uint8(x_69, 7);
x_78 = lean_ctor_get_uint8(x_69, 8);
x_79 = lean_ctor_get_uint8(x_69, 9);
x_80 = lean_ctor_get_uint8(x_69, 11);
x_81 = lean_ctor_get_uint8(x_69, 12);
x_82 = lean_ctor_get_uint8(x_69, 13);
x_83 = lean_ctor_get_uint8(x_69, 14);
x_84 = lean_ctor_get_uint8(x_69, 15);
x_85 = lean_ctor_get_uint8(x_69, 16);
x_86 = lean_ctor_get_uint8(x_69, 17);
x_87 = lean_ctor_get_uint8(x_69, 18);
x_120 = !lean_is_exclusive(x_69);
if (x_120 == 0)
{
x_88 = x_69;
x_89 = x_120;
goto block_119;
}
else
{
lean_dec(x_69);
x_88 = lean_box(0);
x_89 = x_120;
goto block_119;
}
block_119:
{
uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; uint8_t x_117; 
x_90 = lean_ctor_get_uint8(x_67, sizeof(void*)*3 + 6);
lean_dec_ref(x_67);
x_91 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_92 = lean_ctor_get(x_3, 1);
x_93 = lean_ctor_get(x_3, 2);
x_94 = lean_ctor_get(x_3, 3);
x_95 = lean_ctor_get(x_3, 4);
x_96 = lean_ctor_get(x_3, 5);
x_97 = lean_ctor_get(x_3, 6);
x_98 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_99 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_100 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_117 = !lean_is_exclusive(x_3);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_3, 0);
lean_dec(x_118);
x_101 = x_3;
x_102 = x_117;
goto block_116;
}
else
{
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_3);
x_101 = lean_box(0);
x_102 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_103; 
if (x_89 == 0)
{
x_103 = x_88;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_115, 0, x_70);
lean_ctor_set_uint8(x_115, 1, x_71);
lean_ctor_set_uint8(x_115, 2, x_72);
lean_ctor_set_uint8(x_115, 3, x_73);
lean_ctor_set_uint8(x_115, 4, x_74);
lean_ctor_set_uint8(x_115, 5, x_75);
lean_ctor_set_uint8(x_115, 6, x_76);
lean_ctor_set_uint8(x_115, 7, x_77);
lean_ctor_set_uint8(x_115, 8, x_78);
lean_ctor_set_uint8(x_115, 9, x_79);
lean_ctor_set_uint8(x_115, 11, x_80);
lean_ctor_set_uint8(x_115, 12, x_81);
lean_ctor_set_uint8(x_115, 13, x_82);
lean_ctor_set_uint8(x_115, 14, x_83);
lean_ctor_set_uint8(x_115, 15, x_84);
lean_ctor_set_uint8(x_115, 16, x_85);
lean_ctor_set_uint8(x_115, 17, x_86);
lean_ctor_set_uint8(x_115, 18, x_87);
x_103 = x_115;
goto block_114;
}
block_114:
{
uint64_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_ctor_set_uint8(x_103, 10, x_90);
x_104 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_103);
x_105 = 2;
x_106 = lean_box(x_105);
x_107 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_107, 0, x_106);
lean_closure_set(x_107, 1, x_2);
x_108 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set_uint64(x_108, sizeof(void*)*1, x_104);
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_108);
x_109 = x_101;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_92);
lean_ctor_set(x_113, 2, x_93);
lean_ctor_set(x_113, 3, x_94);
lean_ctor_set(x_113, 4, x_95);
lean_ctor_set(x_113, 5, x_96);
lean_ctor_set(x_113, 6, x_97);
lean_ctor_set_uint8(x_113, sizeof(void*)*7, x_91);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 1, x_98);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 2, x_99);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 3, x_100);
x_109 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lean_Meta_withTrackingZetaDeltaSet___redArg(x_29, x_66, x_68, x_107);
x_111 = lean_apply_5(x_110, x_109, x_4, x_5, x_6, lean_box(0));
return x_111;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_145; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_145 = !lean_is_exclusive(x_11);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_11, 1);
lean_dec(x_146);
x_16 = x_11;
x_17 = x_145;
goto block_144;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__1));
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_22);
lean_ctor_set(x_143, 1, x_18);
lean_ctor_set(x_143, 2, x_25);
lean_ctor_set(x_143, 3, x_24);
lean_ctor_set(x_143, 4, x_23);
x_26 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_140; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
lean_closure_set(x_29, 2, x_28);
x_30 = l_instMonadControlTOfPure___redArg(x_29);
x_31 = lean_ctor_get(x_10, 0);
x_140 = !lean_is_exclusive(x_10);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_10, 1);
lean_dec(x_141);
x_32 = x_10;
x_33 = x_140;
goto block_139;
}
else
{
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_box(0);
x_33 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_137; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_137 = !lean_is_exclusive(x_31);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_31, 1);
lean_dec(x_138);
x_38 = x_31;
x_39 = x_137;
goto block_136;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_34);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_37);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_43);
lean_ctor_set(x_38, 3, x_44);
lean_ctor_set(x_38, 2, x_45);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set(x_38, 0, x_42);
x_46 = x_38;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_42);
lean_ctor_set(x_135, 1, x_18);
lean_ctor_set(x_135, 2, x_45);
lean_ctor_set(x_135, 3, x_44);
lean_ctor_set(x_135, 4, x_43);
x_46 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_47; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 0, x_46);
x_47 = x_32;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_46);
lean_ctor_set(x_133, 1, x_19);
x_47 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_130; 
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = lean_ctor_get(x_48, 0);
x_130 = !lean_is_exclusive(x_48);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_48, 1);
lean_dec(x_131);
x_50 = x_48;
x_51 = x_130;
goto block_129;
}
else
{
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_127; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 2);
x_54 = lean_ctor_get(x_49, 3);
x_55 = lean_ctor_get(x_49, 4);
x_127 = !lean_is_exclusive(x_49);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_49, 1);
lean_dec(x_128);
x_56 = x_49;
x_57 = x_127;
goto block_126;
}
else
{
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
x_56 = lean_box(0);
x_57 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__3));
x_59 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_simpAppUsingCongr_visit_spec__0___closed__4));
lean_inc_ref(x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_55);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_54);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_53);
if (x_57 == 0)
{
lean_ctor_set(x_56, 4, x_63);
lean_ctor_set(x_56, 3, x_64);
lean_ctor_set(x_56, 2, x_65);
lean_ctor_set(x_56, 1, x_58);
lean_ctor_set(x_56, 0, x_62);
x_66 = x_56;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_62);
lean_ctor_set(x_125, 1, x_58);
lean_ctor_set(x_125, 2, x_65);
lean_ctor_set(x_125, 3, x_64);
lean_ctor_set(x_125, 4, x_63);
x_66 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_67; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 1, x_59);
lean_ctor_set(x_50, 0, x_66);
x_67 = x_50;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_66);
lean_ctor_set(x_123, 1, x_59);
x_67 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; uint8_t x_90; uint8_t x_121; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
lean_dec_ref(x_2);
x_70 = l_Lean_Meta_Context_config(x_4);
x_71 = lean_ctor_get_uint8(x_70, 0);
x_72 = lean_ctor_get_uint8(x_70, 1);
x_73 = lean_ctor_get_uint8(x_70, 2);
x_74 = lean_ctor_get_uint8(x_70, 3);
x_75 = lean_ctor_get_uint8(x_70, 4);
x_76 = lean_ctor_get_uint8(x_70, 5);
x_77 = lean_ctor_get_uint8(x_70, 6);
x_78 = lean_ctor_get_uint8(x_70, 7);
x_79 = lean_ctor_get_uint8(x_70, 8);
x_80 = lean_ctor_get_uint8(x_70, 9);
x_81 = lean_ctor_get_uint8(x_70, 11);
x_82 = lean_ctor_get_uint8(x_70, 12);
x_83 = lean_ctor_get_uint8(x_70, 13);
x_84 = lean_ctor_get_uint8(x_70, 14);
x_85 = lean_ctor_get_uint8(x_70, 15);
x_86 = lean_ctor_get_uint8(x_70, 16);
x_87 = lean_ctor_get_uint8(x_70, 17);
x_88 = lean_ctor_get_uint8(x_70, 18);
x_121 = !lean_is_exclusive(x_70);
if (x_121 == 0)
{
x_89 = x_70;
x_90 = x_121;
goto block_120;
}
else
{
lean_dec(x_70);
x_89 = lean_box(0);
x_90 = x_121;
goto block_120;
}
block_120:
{
uint8_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; uint8_t x_118; 
x_91 = lean_ctor_get_uint8(x_68, sizeof(void*)*3 + 6);
lean_dec_ref(x_68);
x_92 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_93 = lean_ctor_get(x_4, 1);
x_94 = lean_ctor_get(x_4, 2);
x_95 = lean_ctor_get(x_4, 3);
x_96 = lean_ctor_get(x_4, 4);
x_97 = lean_ctor_get(x_4, 5);
x_98 = lean_ctor_get(x_4, 6);
x_99 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_100 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_101 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_4, 0);
lean_dec(x_119);
x_102 = x_4;
x_103 = x_118;
goto block_117;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_4);
x_102 = lean_box(0);
x_103 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_104; 
if (x_90 == 0)
{
x_104 = x_89;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_116, 0, x_71);
lean_ctor_set_uint8(x_116, 1, x_72);
lean_ctor_set_uint8(x_116, 2, x_73);
lean_ctor_set_uint8(x_116, 3, x_74);
lean_ctor_set_uint8(x_116, 4, x_75);
lean_ctor_set_uint8(x_116, 5, x_76);
lean_ctor_set_uint8(x_116, 6, x_77);
lean_ctor_set_uint8(x_116, 7, x_78);
lean_ctor_set_uint8(x_116, 8, x_79);
lean_ctor_set_uint8(x_116, 9, x_80);
lean_ctor_set_uint8(x_116, 11, x_81);
lean_ctor_set_uint8(x_116, 12, x_82);
lean_ctor_set_uint8(x_116, 13, x_83);
lean_ctor_set_uint8(x_116, 14, x_84);
lean_ctor_set_uint8(x_116, 15, x_85);
lean_ctor_set_uint8(x_116, 16, x_86);
lean_ctor_set_uint8(x_116, 17, x_87);
lean_ctor_set_uint8(x_116, 18, x_88);
x_104 = x_116;
goto block_115;
}
block_115:
{
uint64_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_ctor_set_uint8(x_104, 10, x_91);
x_105 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_104);
x_106 = 2;
x_107 = lean_box(x_106);
x_108 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_108, 0, x_107);
lean_closure_set(x_108, 1, x_3);
x_109 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set_uint64(x_109, sizeof(void*)*1, x_105);
if (x_103 == 0)
{
lean_ctor_set(x_102, 0, x_109);
x_110 = x_102;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_114, 2, x_94);
lean_ctor_set(x_114, 3, x_95);
lean_ctor_set(x_114, 4, x_96);
lean_ctor_set(x_114, 5, x_97);
lean_ctor_set(x_114, 6, x_98);
lean_ctor_set_uint8(x_114, sizeof(void*)*7, x_92);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 1, x_99);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 2, x_100);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 3, x_101);
x_110 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_Meta_withTrackingZetaDeltaSet___redArg(x_30, x_67, x_69, x_108);
x_112 = lean_apply_5(x_111, x_110, x_5, x_6, x_7, lean_box(0));
return x_112;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_withSimpContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_ctor_get(x_3, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_1, x_2, x_5);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg(x_4, x_1);
if (x_8 == 0)
{
x_2 = x_7;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Lean_Meta_Simp_UsedSimps_insert(x_7, x_10);
x_2 = x_11;
x_3 = x_6;
goto _start;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaDeltaFVarIds___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_26; 
x_6 = lean_ctor_get(x_5, 0);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
x_7 = x_5;
x_8 = x_26;
goto block_25;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_24; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
x_11 = x_2;
x_12 = x_24;
goto block_23;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_14, x_9, x_13);
x_16 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDeltaCore_spec__1_spec__1(x_6, x_15, x_13);
lean_dec(x_6);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_16);
x_17 = x_11;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_10);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_17);
x_18 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec_ref(x_2);
x_27 = lean_ctor_get(x_5, 0);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
x_28 = x_5;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_congrArgs_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
x_5 = lean_st_ref_take(x_1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_5, 2);
lean_dec(x_20);
x_10 = x_5;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_2);
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_8);
lean_ctor_set(x_17, 4, x_9);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_st_ref_set(x_1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
x_5 = lean_st_ref_take(x_1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_5, 1);
lean_dec(x_20);
x_10 = x_5;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_2);
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_8);
lean_ctor_set(x_17, 4, x_9);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_st_ref_set(x_1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0, &l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0_once, _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1, &l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1_once, _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_91; 
x_8 = lean_st_ref_get(x_4);
x_9 = lean_st_ref_take(x_4);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 2);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_91 = !lean_is_exclusive(x_9);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_9, 1);
lean_dec(x_92);
x_14 = x_9;
x_15 = x_91;
goto block_90;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_obj_once(&l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2, &l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2_once, _init_l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___closed__2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
x_17 = x_14;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_16);
lean_ctor_set(x_89, 2, x_11);
lean_ctor_set(x_89, 3, x_12);
lean_ctor_set(x_89, 4, x_13);
x_17 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_87; 
x_18 = lean_st_ref_set(x_4, x_17);
x_19 = lean_st_ref_take(x_4);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 2);
x_23 = lean_ctor_get(x_19, 3);
x_24 = lean_ctor_get(x_19, 4);
x_87 = !lean_is_exclusive(x_19);
if (x_87 == 0)
{
x_25 = x_19;
x_26 = x_87;
goto block_86;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(1);
if (x_26 == 0)
{
lean_ctor_set(x_25, 2, x_27);
x_28 = x_25;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_21);
lean_ctor_set(x_85, 2, x_27);
lean_ctor_set(x_85, 3, x_23);
lean_ctor_set(x_85, 4, x_24);
x_28 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_82; 
x_29 = lean_st_ref_set(x_4, x_28);
x_30 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_30);
lean_dec(x_8);
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
x_36 = lean_ctor_get(x_3, 6);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_40 = x_3;
x_41 = x_82;
goto block_81;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_40 = lean_box(0);
x_41 = x_82;
goto block_81;
}
block_81:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_56; 
x_42 = 1;
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_1);
x_56 = x_40;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_80, 0, x_31);
lean_ctor_set(x_80, 1, x_1);
lean_ctor_set(x_80, 2, x_32);
lean_ctor_set(x_80, 3, x_33);
lean_ctor_set(x_80, 4, x_34);
lean_ctor_set(x_80, 5, x_35);
lean_ctor_set(x_80, 6, x_36);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 1, x_37);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 2, x_38);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 3, x_39);
x_56 = x_80;
goto block_79;
}
block_55:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
x_45 = lean_box(0);
x_46 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1(x_4, x_30, x_45);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_46, 0);
lean_dec(x_54);
x_47 = x_46;
x_48 = x_53;
goto block_52;
}
else
{
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_43);
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_43);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_79:
{
lean_object* x_57; 
lean_ctor_set_uint8(x_56, sizeof(void*)*7, x_42);
lean_inc(x_4);
x_57 = lean_apply_5(x_2, x_56, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_75; 
x_58 = lean_ctor_get(x_57, 0);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
x_59 = x_57;
x_60 = x_75;
goto block_74;
}
else
{
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_61; 
lean_inc(x_58);
if (x_60 == 0)
{
lean_ctor_set_tag(x_59, 1);
x_61 = x_59;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_58);
x_61 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
x_62 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(x_4, x_22, x_61);
lean_dec_ref(x_62);
x_63 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__1(x_4, x_30, x_61);
lean_dec_ref(x_61);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_63, 0);
lean_dec(x_71);
x_64 = x_63;
x_65 = x_70;
goto block_69;
}
else
{
lean_dec(x_63);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
lean_ctor_set(x_64, 0, x_58);
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_58);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
lean_dec_ref(x_57);
x_77 = lean_box(0);
x_78 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(x_4, x_22, x_77);
lean_dec_ref(x_78);
x_43 = x_76;
x_44 = lean_box(0);
goto block_55;
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_154; 
x_93 = lean_st_ref_take(x_4);
x_94 = lean_ctor_get(x_93, 0);
x_95 = lean_ctor_get(x_93, 1);
x_96 = lean_ctor_get(x_93, 2);
x_97 = lean_ctor_get(x_93, 3);
x_98 = lean_ctor_get(x_93, 4);
x_154 = !lean_is_exclusive(x_93);
if (x_154 == 0)
{
x_99 = x_93;
x_100 = x_154;
goto block_153;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_93);
x_99 = lean_box(0);
x_100 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(1);
if (x_100 == 0)
{
lean_ctor_set(x_99, 2, x_101);
x_102 = x_99;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_94);
lean_ctor_set(x_152, 1, x_95);
lean_ctor_set(x_152, 2, x_101);
lean_ctor_set(x_152, 3, x_97);
lean_ctor_set(x_152, 4, x_98);
x_102 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; uint8_t x_150; 
x_103 = lean_st_ref_set(x_4, x_102);
x_104 = lean_ctor_get(x_3, 0);
x_105 = lean_ctor_get(x_3, 1);
x_106 = lean_ctor_get(x_3, 2);
x_107 = lean_ctor_get(x_3, 3);
x_108 = lean_ctor_get(x_3, 4);
x_109 = lean_ctor_get(x_3, 5);
x_110 = lean_ctor_get(x_3, 6);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_112 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_113 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_150 = !lean_is_exclusive(x_3);
if (x_150 == 0)
{
x_114 = x_3;
x_115 = x_150;
goto block_149;
}
else
{
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_3);
x_114 = lean_box(0);
x_115 = x_150;
goto block_149;
}
block_149:
{
uint8_t x_116; lean_object* x_117; 
x_116 = 0;
if (x_115 == 0)
{
x_117 = x_114;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_148, 0, x_104);
lean_ctor_set(x_148, 1, x_105);
lean_ctor_set(x_148, 2, x_106);
lean_ctor_set(x_148, 3, x_107);
lean_ctor_set(x_148, 4, x_108);
lean_ctor_set(x_148, 5, x_109);
lean_ctor_set(x_148, 6, x_110);
lean_ctor_set_uint8(x_148, sizeof(void*)*7 + 1, x_111);
lean_ctor_set_uint8(x_148, sizeof(void*)*7 + 2, x_112);
lean_ctor_set_uint8(x_148, sizeof(void*)*7 + 3, x_113);
x_117 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_118; 
lean_ctor_set_uint8(x_117, sizeof(void*)*7, x_116);
lean_inc(x_4);
x_118 = lean_apply_5(x_2, x_117, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_135; 
x_119 = lean_ctor_get(x_118, 0);
x_135 = !lean_is_exclusive(x_118);
if (x_135 == 0)
{
x_120 = x_118;
x_121 = x_135;
goto block_134;
}
else
{
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_box(0);
x_121 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_122; 
lean_inc(x_119);
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 1);
x_122 = x_120;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_119);
x_122 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
x_123 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(x_4, x_96, x_122);
lean_dec_ref(x_122);
lean_dec(x_4);
x_130 = !lean_is_exclusive(x_123);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_123, 0);
lean_dec(x_131);
x_124 = x_123;
x_125 = x_130;
goto block_129;
}
else
{
lean_dec(x_123);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
lean_ctor_set(x_124, 0, x_119);
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_119);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
x_136 = lean_ctor_get(x_118, 0);
lean_inc(x_136);
lean_dec_ref(x_118);
x_137 = lean_box(0);
x_138 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___lam__0(x_4, x_96, x_137);
lean_dec(x_4);
x_145 = !lean_is_exclusive(x_138);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_138, 0);
lean_dec(x_146);
x_139 = x_138;
x_140 = x_145;
goto block_144;
}
else
{
lean_dec(x_138);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
lean_ctor_set_tag(x_139, 1);
lean_ctor_set(x_139, 0, x_136);
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_136);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_congrArgs_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_145; 
x_11 = l_Lean_Meta_Context_config(x_6);
x_12 = lean_ctor_get_uint8(x_11, 0);
x_13 = lean_ctor_get_uint8(x_11, 1);
x_14 = lean_ctor_get_uint8(x_11, 2);
x_15 = lean_ctor_get_uint8(x_11, 3);
x_16 = lean_ctor_get_uint8(x_11, 4);
x_17 = lean_ctor_get_uint8(x_11, 5);
x_18 = lean_ctor_get_uint8(x_11, 6);
x_19 = lean_ctor_get_uint8(x_11, 7);
x_20 = lean_ctor_get_uint8(x_11, 8);
x_21 = lean_ctor_get_uint8(x_11, 10);
x_22 = lean_ctor_get_uint8(x_11, 11);
x_23 = lean_ctor_get_uint8(x_11, 12);
x_24 = lean_ctor_get_uint8(x_11, 13);
x_25 = lean_ctor_get_uint8(x_11, 14);
x_26 = lean_ctor_get_uint8(x_11, 15);
x_27 = lean_ctor_get_uint8(x_11, 16);
x_28 = lean_ctor_get_uint8(x_11, 17);
x_29 = lean_ctor_get_uint8(x_11, 18);
x_145 = !lean_is_exclusive(x_11);
if (x_145 == 0)
{
x_30 = x_11;
x_31 = x_145;
goto block_144;
}
else
{
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_32 = lean_st_mk_ref(x_1);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_6, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 6);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_41 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
if (x_31 == 0)
{
x_43 = x_30;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_143, 0, x_12);
lean_ctor_set_uint8(x_143, 1, x_13);
lean_ctor_set_uint8(x_143, 2, x_14);
lean_ctor_set_uint8(x_143, 3, x_15);
lean_ctor_set_uint8(x_143, 4, x_16);
lean_ctor_set_uint8(x_143, 5, x_17);
lean_ctor_set_uint8(x_143, 6, x_18);
lean_ctor_set_uint8(x_143, 7, x_19);
lean_ctor_set_uint8(x_143, 8, x_20);
lean_ctor_set_uint8(x_143, 10, x_21);
lean_ctor_set_uint8(x_143, 11, x_22);
lean_ctor_set_uint8(x_143, 12, x_23);
lean_ctor_set_uint8(x_143, 13, x_24);
lean_ctor_set_uint8(x_143, 14, x_25);
lean_ctor_set_uint8(x_143, 15, x_26);
lean_ctor_set_uint8(x_143, 16, x_27);
lean_ctor_set_uint8(x_143, 17, x_28);
lean_ctor_set_uint8(x_143, 18, x_29);
x_43 = x_143;
goto block_142;
}
block_142:
{
uint64_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_134; 
lean_ctor_set_uint8(x_43, 9, x_2);
x_44 = l_Lean_Meta_Context_configKey(x_6);
x_134 = !lean_is_exclusive(x_6);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_6, 6);
lean_dec(x_135);
x_136 = lean_ctor_get(x_6, 5);
lean_dec(x_136);
x_137 = lean_ctor_get(x_6, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_6, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_6, 2);
lean_dec(x_139);
x_140 = lean_ctor_get(x_6, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_6, 0);
lean_dec(x_141);
x_45 = x_6;
x_46 = x_134;
goto block_133;
}
else
{
lean_dec(x_6);
x_45 = lean_box(0);
x_46 = x_134;
goto block_133;
}
block_133:
{
uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; 
x_47 = 2;
x_48 = lean_uint64_shift_right(x_44, x_47);
x_49 = lean_uint64_shift_left(x_48, x_47);
x_50 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_51 = lean_uint64_lor(x_49, x_50);
x_52 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set_uint64(x_52, sizeof(void*)*1, x_51);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_52);
x_53 = x_45;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_132, 0, x_52);
lean_ctor_set(x_132, 1, x_34);
lean_ctor_set(x_132, 2, x_35);
lean_ctor_set(x_132, 3, x_36);
lean_ctor_set(x_132, 4, x_37);
lean_ctor_set(x_132, 5, x_38);
lean_ctor_set(x_132, 6, x_39);
lean_ctor_set_uint8(x_132, sizeof(void*)*7, x_33);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 1, x_40);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 2, x_41);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 3, x_42);
x_53 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_54; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_53);
lean_inc(x_32);
lean_inc_ref(x_5);
x_54 = lean_apply_8(x_3, x_4, x_5, x_32, x_53, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_122; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_st_ref_get(x_32);
lean_dec(x_32);
x_100 = ((lean_object*)(l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___closed__1));
x_101 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_SimpM_run_spec__0___redArg(x_100, x_8);
x_102 = lean_ctor_get(x_101, 0);
x_122 = !lean_is_exclusive(x_101);
if (x_122 == 0)
{
x_103 = x_101;
x_104 = x_122;
goto block_121;
}
else
{
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = x_122;
goto block_121;
}
block_99:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_98; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_ctor_get(x_56, 2);
x_62 = lean_ctor_get(x_56, 3);
x_63 = lean_ctor_get(x_56, 4);
x_64 = lean_ctor_get(x_56, 5);
x_98 = !lean_is_exclusive(x_56);
if (x_98 == 0)
{
x_65 = x_56;
x_66 = x_98;
goto block_97;
}
else
{
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_56);
x_65 = lean_box(0);
x_66 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_64);
x_68 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateUsedSimpsWithZetaDelta___redArg(x_5, x_67, x_57);
lean_dec(x_57);
lean_dec_ref(x_5);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_88; 
x_69 = lean_ctor_get(x_68, 0);
x_88 = !lean_is_exclusive(x_68);
if (x_88 == 0)
{
x_70 = x_68;
x_71 = x_88;
goto block_87;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_86; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
x_86 = !lean_is_exclusive(x_69);
if (x_86 == 0)
{
x_74 = x_69;
x_75 = x_86;
goto block_85;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_76; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 5, x_73);
lean_ctor_set(x_65, 3, x_72);
x_76 = x_65;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_59);
lean_ctor_set(x_84, 1, x_60);
lean_ctor_set(x_84, 2, x_61);
lean_ctor_set(x_84, 3, x_72);
lean_ctor_set(x_84, 4, x_63);
lean_ctor_set(x_84, 5, x_73);
x_76 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_77; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 1, x_76);
lean_ctor_set(x_74, 0, x_55);
x_77 = x_74;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_55);
lean_ctor_set(x_82, 1, x_76);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_77);
x_78 = x_70;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_del_object(x_65);
lean_dec(x_63);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
x_89 = lean_ctor_get(x_68, 0);
x_96 = !lean_is_exclusive(x_68);
if (x_96 == 0)
{
x_90 = x_68;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_68);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
}
block_121:
{
uint8_t x_105; 
x_105 = lean_unbox(x_102);
lean_dec(x_102);
if (x_105 == 0)
{
lean_del_object(x_103);
lean_dec_ref(x_53);
lean_dec(x_9);
lean_dec_ref(x_8);
x_57 = x_7;
x_58 = lean_box(0);
goto block_99;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_56, 4);
lean_inc(x_106);
x_107 = l_Nat_reprFast(x_106);
if (x_104 == 0)
{
lean_ctor_set_tag(x_103, 3);
lean_ctor_set(x_103, 0, x_107);
x_108 = x_103;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_107);
x_108 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_MessageData_ofFormat(x_108);
x_110 = l_Lean_addTrace___at___00Lean_Meta_Simp_SimpM_run_spec__1(x_100, x_109, x_53, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_53);
if (lean_obj_tag(x_110) == 0)
{
lean_dec_ref(x_110);
x_57 = x_7;
x_58 = lean_box(0);
goto block_99;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_7);
lean_dec_ref(x_5);
x_111 = lean_ctor_get(x_110, 0);
x_118 = !lean_is_exclusive(x_110);
if (x_118 == 0)
{
x_112 = x_110;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_dec_ref(x_53);
lean_dec(x_32);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
x_123 = lean_ctor_get(x_54, 0);
x_130 = !lean_is_exclusive(x_54);
if (x_130 == 0)
{
x_124 = x_54;
x_125 = x_130;
goto block_129;
}
else
{
lean_inc(x_123);
lean_dec(x_54);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Meta_Simp_SimpM_run___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_64; 
lean_inc_ref(x_5);
x_10 = l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(x_1, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_Meta_Context_config(x_5);
x_15 = lean_ctor_get_uint8(x_14, 0);
x_16 = lean_ctor_get_uint8(x_14, 1);
x_17 = lean_ctor_get_uint8(x_14, 2);
x_18 = lean_ctor_get_uint8(x_14, 3);
x_19 = lean_ctor_get_uint8(x_14, 4);
x_20 = lean_ctor_get_uint8(x_14, 5);
x_21 = lean_ctor_get_uint8(x_14, 6);
x_22 = lean_ctor_get_uint8(x_14, 7);
x_23 = lean_ctor_get_uint8(x_14, 8);
x_24 = lean_ctor_get_uint8(x_14, 9);
x_25 = lean_ctor_get_uint8(x_14, 11);
x_26 = lean_ctor_get_uint8(x_14, 12);
x_27 = lean_ctor_get_uint8(x_14, 13);
x_28 = lean_ctor_get_uint8(x_14, 14);
x_29 = lean_ctor_get_uint8(x_14, 15);
x_30 = lean_ctor_get_uint8(x_14, 16);
x_31 = lean_ctor_get_uint8(x_14, 17);
x_32 = lean_ctor_get_uint8(x_14, 18);
x_64 = !lean_is_exclusive(x_14);
if (x_64 == 0)
{
x_33 = x_14;
x_34 = x_64;
goto block_63;
}
else
{
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; uint8_t x_61; 
x_35 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 6);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get(x_5, 2);
x_39 = lean_ctor_get(x_5, 3);
x_40 = lean_ctor_get(x_5, 4);
x_41 = lean_ctor_get(x_5, 5);
x_42 = lean_ctor_get(x_5, 6);
x_43 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_45 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_5, 0);
lean_dec(x_62);
x_46 = x_5;
x_47 = x_61;
goto block_60;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_46 = lean_box(0);
x_47 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_48; 
if (x_34 == 0)
{
x_48 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_59, 0, x_15);
lean_ctor_set_uint8(x_59, 1, x_16);
lean_ctor_set_uint8(x_59, 2, x_17);
lean_ctor_set_uint8(x_59, 3, x_18);
lean_ctor_set_uint8(x_59, 4, x_19);
lean_ctor_set_uint8(x_59, 5, x_20);
lean_ctor_set_uint8(x_59, 6, x_21);
lean_ctor_set_uint8(x_59, 7, x_22);
lean_ctor_set_uint8(x_59, 8, x_23);
lean_ctor_set_uint8(x_59, 9, x_24);
lean_ctor_set_uint8(x_59, 11, x_25);
lean_ctor_set_uint8(x_59, 12, x_26);
lean_ctor_set_uint8(x_59, 13, x_27);
lean_ctor_set_uint8(x_59, 14, x_28);
lean_ctor_set_uint8(x_59, 15, x_29);
lean_ctor_set_uint8(x_59, 16, x_30);
lean_ctor_set_uint8(x_59, 17, x_31);
lean_ctor_set_uint8(x_59, 18, x_32);
x_48 = x_59;
goto block_58;
}
block_58:
{
uint64_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_ctor_set_uint8(x_48, 10, x_35);
x_49 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_SimpM_run___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_52, 0, x_2);
lean_closure_set(x_52, 1, x_51);
lean_closure_set(x_52, 2, x_4);
lean_closure_set(x_52, 3, x_3);
lean_closure_set(x_52, 4, x_11);
x_53 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set_uint64(x_53, sizeof(void*)*1, x_49);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_53);
x_54 = x_46;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_38);
lean_ctor_set(x_57, 3, x_39);
lean_ctor_set(x_57, 4, x_40);
lean_ctor_set(x_57, 5, x_41);
lean_ctor_set(x_57, 6, x_42);
lean_ctor_set_uint8(x_57, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 1, x_43);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 2, x_44);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 3, x_45);
x_54 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_withTrackingZetaDeltaSet___at___00Lean_Meta_Simp_SimpM_run_spec__2___redArg(x_13, x_52, x_54, x_6, x_7, x_8);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_SimpM_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_SimpM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimpM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_SimpM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
x_11 = lean_expr_eqv(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_10, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_9);
x_14 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = l_Lean_MVarId_replaceTargetEq(x_1, x_14, x_15, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_applySimpResultToTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_9;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Types_1833177992____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_backward_dsimp_instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_backward_dsimp_instances);
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedResult_default = _init_l_Lean_Meta_Simp_instInhabitedResult_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult_default);
l_Lean_Meta_Simp_instInhabitedResult = _init_l_Lean_Meta_Simp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult);
l_Lean_Meta_Simp_instInhabitedContext_default = _init_l_Lean_Meta_Simp_instInhabitedContext_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext_default);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l_Lean_Meta_Simp_instInhabitedUsedSimps_default = _init_l_Lean_Meta_Simp_instInhabitedUsedSimps_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedUsedSimps_default);
l_Lean_Meta_Simp_instInhabitedUsedSimps = _init_l_Lean_Meta_Simp_instInhabitedUsedSimps();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedUsedSimps);
l_Lean_Meta_Simp_instInhabitedDiagnostics_default = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics_default);
l_Lean_Meta_Simp_instInhabitedDiagnostics = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics);
l_Lean_Meta_Simp_instInhabitedStats_default = _init_l_Lean_Meta_Simp_instInhabitedStats_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStats_default);
l_Lean_Meta_Simp_instInhabitedStats = _init_l_Lean_Meta_Simp_instInhabitedStats();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStats);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed();
l_Lean_Meta_Simp_instInhabitedStep_default = _init_l_Lean_Meta_Simp_instInhabitedStep_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep_default);
l_Lean_Meta_Simp_instInhabitedStep = _init_l_Lean_Meta_Simp_instInhabitedStep();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep);
l_Lean_Meta_Simp_instInhabitedSimprocs_default = _init_l_Lean_Meta_Simp_instInhabitedSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs_default);
l_Lean_Meta_Simp_instInhabitedSimprocs = _init_l_Lean_Meta_Simp_instInhabitedSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs);
l_Lean_Meta_Simp_instInhabitedMethods_default = _init_l_Lean_Meta_Simp_instInhabitedMethods_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods_default);
l_Lean_Meta_Simp_instInhabitedMethods = _init_l_Lean_Meta_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Types(builtin);
}
#ifdef __cplusplus
}
#endif
