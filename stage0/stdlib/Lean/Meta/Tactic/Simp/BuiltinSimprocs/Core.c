// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
// Imports: public import Init.Simproc public import Lean.Meta.Tactic.Simp.Simproc import Lean.Meta.CtorRecognizer
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
static const lean_ctor_object l_reduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_reduceIte___closed__0 = (const lean_object*)&l_reduceIte___closed__0_value;
static const lean_string_object l_reduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_reduceIte___closed__1 = (const lean_object*)&l_reduceIte___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_reduceIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_reduceIte___closed__2 = (const lean_object*)&l_reduceIte___closed__2_value;
static const lean_string_object l_reduceIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_reduceIte___closed__3 = (const lean_object*)&l_reduceIte___closed__3_value;
static const lean_ctor_object l_reduceIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_reduceIte___closed__4 = (const lean_object*)&l_reduceIte___closed__4_value;
static const lean_string_object l_reduceIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_reduceIte___closed__5 = (const lean_object*)&l_reduceIte___closed__5_value;
static const lean_ctor_object l_reduceIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_reduceIte___closed__6 = (const lean_object*)&l_reduceIte___closed__6_value;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(1, 182, 106, 10, 77, 189, 166, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceIte___closed__2_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(lean_object*);
static lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_;
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(lean_object*);
static const lean_string_object l_reduceDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_reduceDIte___closed__0 = (const lean_object*)&l_reduceDIte___closed__0_value;
static const lean_ctor_object l_reduceDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_reduceDIte___closed__1 = (const lean_object*)&l_reduceDIte___closed__1_value;
static const lean_string_object l_reduceDIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "of_eq_false"};
static const lean_object* l_reduceDIte___closed__2 = (const lean_object*)&l_reduceDIte___closed__2_value;
static const lean_ctor_object l_reduceDIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 110, 142, 77, 120, 210, 227, 9)}};
static const lean_object* l_reduceDIte___closed__3 = (const lean_object*)&l_reduceDIte___closed__3_value;
static lean_object* l_reduceDIte___closed__4;
static const lean_string_object l_reduceDIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l_reduceDIte___closed__5 = (const lean_object*)&l_reduceDIte___closed__5_value;
static const lean_ctor_object l_reduceDIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l_reduceDIte___closed__6 = (const lean_object*)&l_reduceDIte___closed__6_value;
static const lean_string_object l_reduceDIte___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_eq_true"};
static const lean_object* l_reduceDIte___closed__7 = (const lean_object*)&l_reduceDIte___closed__7_value;
static const lean_ctor_object l_reduceDIte___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__7_value),LEAN_SCALAR_PTR_LITERAL(180, 216, 190, 52, 49, 30, 207, 178)}};
static const lean_object* l_reduceDIte___closed__8 = (const lean_object*)&l_reduceDIte___closed__8_value;
static lean_object* l_reduceDIte___closed__9;
static const lean_string_object l_reduceDIte___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l_reduceDIte___closed__10 = (const lean_object*)&l_reduceDIte___closed__10_value;
static const lean_ctor_object l_reduceDIte___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__10_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l_reduceDIte___closed__11 = (const lean_object*)&l_reduceDIte___closed__11_value;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(30, 101, 22, 109, 248, 175, 82, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceDIte___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(lean_object*);
static lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object*);
static const lean_ctor_object l_dreduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_dreduceIte___closed__0 = (const lean_object*)&l_dreduceIte___closed__0_value;
static const lean_string_object l_dreduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_dreduceIte___closed__1 = (const lean_object*)&l_dreduceIte___closed__1_value;
static const lean_string_object l_dreduceIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_dreduceIte___closed__2 = (const lean_object*)&l_dreduceIte___closed__2_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_dreduceIte___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_dreduceIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__3_value_aux_0),((lean_object*)&l_dreduceIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l_dreduceIte___closed__3 = (const lean_object*)&l_dreduceIte___closed__3_value;
static const lean_string_object l_dreduceIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_dreduceIte___closed__4 = (const lean_object*)&l_dreduceIte___closed__4_value;
static const lean_ctor_object l_dreduceIte___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_dreduceIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__5_value_aux_0),((lean_object*)&l_dreduceIte___closed__4_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_dreduceIte___closed__5 = (const lean_object*)&l_dreduceIte___closed__5_value;
static const lean_string_object l_dreduceIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_dreduceIte___closed__6 = (const lean_object*)&l_dreduceIte___closed__6_value;
static const lean_ctor_object l_dreduceIte___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_dreduceIte___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__7_value_aux_0),((lean_object*)&l_dreduceIte___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_dreduceIte___closed__7 = (const lean_object*)&l_dreduceIte___closed__7_value;
static const lean_ctor_object l_dreduceIte___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_dreduceIte___closed__8 = (const lean_object*)&l_dreduceIte___closed__8_value;
static const lean_string_object l_dreduceIte___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_dreduceIte___closed__9 = (const lean_object*)&l_dreduceIte___closed__9_value;
static const lean_string_object l_dreduceIte___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_dreduceIte___closed__10 = (const lean_object*)&l_dreduceIte___closed__10_value;
static const lean_ctor_object l_dreduceIte___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_dreduceIte___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__11_value_aux_0),((lean_object*)&l_dreduceIte___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_dreduceIte___closed__11 = (const lean_object*)&l_dreduceIte___closed__11_value;
static const lean_string_object l_dreduceIte___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_dreduceIte___closed__12 = (const lean_object*)&l_dreduceIte___closed__12_value;
static const lean_ctor_object l_dreduceIte___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_dreduceIte___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__13_value_aux_0),((lean_object*)&l_dreduceIte___closed__12_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_dreduceIte___closed__13 = (const lean_object*)&l_dreduceIte___closed__13_value;
lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dreduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(20, 216, 99, 140, 103, 209, 78, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15__value;
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15____boxed(lean_object*);
static lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19____boxed(lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dreduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(222, 220, 170, 50, 32, 2, 19, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15____boxed(lean_object*);
static lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_reduceCtorEq___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_reduceCtorEq___lam__2___closed__0 = (const lean_object*)&l_reduceCtorEq___lam__2___closed__0_value;
static const lean_ctor_object l_reduceCtorEq___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_reduceCtorEq___lam__2___closed__1 = (const lean_object*)&l_reduceCtorEq___lam__2___closed__1_value;
static lean_object* l_reduceCtorEq___lam__2___closed__2;
static lean_object* l_reduceCtorEq___lam__2___closed__3;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static uint64_t l_reduceCtorEq___lam__2___closed__4;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t, uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_reduceCtorEq___closed__0;
static const lean_string_object l_reduceCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_reduceCtorEq___closed__1 = (const lean_object*)&l_reduceCtorEq___closed__1_value;
static const lean_ctor_object l_reduceCtorEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_reduceCtorEq___closed__2 = (const lean_object*)&l_reduceCtorEq___closed__2_value;
static const lean_string_object l_reduceCtorEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_reduceCtorEq___closed__3 = (const lean_object*)&l_reduceCtorEq___closed__3_value;
static const lean_ctor_object l_reduceCtorEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_reduceCtorEq___closed__4 = (const lean_object*)&l_reduceCtorEq___closed__4_value;
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed__const__1;
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceCtorEq___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(lean_object*);
static lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_12 = x_10;
} else {
 lean_dec_ref(x_10);
 x_12 = lean_box(0);
}
x_16 = l_Lean_Expr_cleanupAnnotations(x_11);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
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
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
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
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_reduceIte___closed__2));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_27);
x_34 = lean_simp(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
x_38 = l_Lean_Expr_isTrue(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_inc_ref(x_37);
x_39 = l_Lean_Expr_isFalse(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_40 = ((lean_object*)(l_reduceIte___closed__0));
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; 
lean_free_object(x_34);
x_41 = l_Lean_Meta_Simp_Result_getProof(x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = ((lean_object*)(l_reduceIte___closed__4));
x_45 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_46 = l_Lean_mkConst(x_44, x_45);
lean_inc_ref(x_18);
x_47 = l_Lean_mkApp5(x_46, x_30, x_27, x_24, x_21, x_18);
x_48 = l_Lean_Expr_app___override(x_47, x_43);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_33);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = ((lean_object*)(l_reduceIte___closed__4));
x_54 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_55 = l_Lean_mkConst(x_53, x_54);
lean_inc_ref(x_18);
x_56 = l_Lean_mkApp5(x_55, x_30, x_27, x_24, x_21, x_18);
x_57 = l_Lean_Expr_app___override(x_56, x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_18);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_33);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
return x_41;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_41, 0);
lean_inc(x_63);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; 
lean_free_object(x_34);
x_65 = l_Lean_Meta_Simp_Result_getProof(x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = ((lean_object*)(l_reduceIte___closed__6));
x_69 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_70 = l_Lean_mkConst(x_68, x_69);
lean_inc_ref(x_21);
x_71 = l_Lean_mkApp5(x_70, x_30, x_27, x_24, x_21, x_18);
x_72 = l_Lean_Expr_app___override(x_71, x_67);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_33);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_65, 0, x_75);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
lean_dec(x_65);
x_77 = ((lean_object*)(l_reduceIte___closed__6));
x_78 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_79 = l_Lean_mkConst(x_77, x_78);
lean_inc_ref(x_21);
x_80 = l_Lean_mkApp5(x_79, x_30, x_27, x_24, x_21, x_18);
x_81 = l_Lean_Expr_app___override(x_80, x_76);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_21);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_33);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_86 = !lean_is_exclusive(x_65);
if (x_86 == 0)
{
return x_65;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_65, 0);
lean_inc(x_87);
lean_dec(x_65);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_34, 0);
lean_inc(x_89);
lean_dec(x_34);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
x_91 = l_Lean_Expr_isTrue(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_inc_ref(x_90);
x_92 = l_Lean_Expr_isFalse(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_93 = ((lean_object*)(l_reduceIte___closed__0));
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = l_Lean_Meta_Simp_Result_getProof(x_89, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = ((lean_object*)(l_reduceIte___closed__4));
x_99 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_100 = l_Lean_mkConst(x_98, x_99);
lean_inc_ref(x_18);
x_101 = l_Lean_mkApp5(x_100, x_30, x_27, x_24, x_21, x_18);
x_102 = l_Lean_Expr_app___override(x_101, x_96);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_18);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_33);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
if (lean_is_scalar(x_97)) {
 x_106 = lean_alloc_ctor(0, 1, 0);
} else {
 x_106 = x_97;
}
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_108 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
else
{
lean_object* x_110; 
x_110 = l_Lean_Meta_Simp_Result_getProof(x_89, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = ((lean_object*)(l_reduceIte___closed__6));
x_114 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_115 = l_Lean_mkConst(x_113, x_114);
lean_inc_ref(x_21);
x_116 = l_Lean_mkApp5(x_115, x_30, x_27, x_24, x_21, x_18);
x_117 = l_Lean_Expr_app___override(x_116, x_111);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_119, 0, x_21);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_33);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
if (lean_is_scalar(x_112)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_112;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_122 = lean_ctor_get(x_110, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_123 = x_110;
} else {
 lean_dec_ref(x_110);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_125 = !lean_is_exclusive(x_34);
if (x_125 == 0)
{
return x_34;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_34, 0);
lean_inc(x_126);
lean_dec(x_34);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l_reduceIte___closed__0));
if (lean_is_scalar(x_12)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_12;
}
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_128; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_10);
if (x_128 == 0)
{
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_10, 0);
lean_inc(x_129);
lean_dec(x_10);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_reduceIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_4 = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
return x_2;
}
}
static lean_object* _init_l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
return x_2;
}
}
static lean_object* _init_l_reduceDIte___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_reduceDIte___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_reduceDIte___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_reduceDIte___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_reduceDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_12 = x_10;
} else {
 lean_dec_ref(x_10);
 x_12 = lean_box(0);
}
x_16 = l_Lean_Expr_cleanupAnnotations(x_11);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
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
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
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
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_reduceDIte___closed__1));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_27);
x_34 = lean_simp(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
x_38 = l_Lean_Expr_isTrue(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_inc_ref(x_37);
x_39 = l_Lean_Expr_isFalse(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_40 = ((lean_object*)(l_reduceIte___closed__0));
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; 
lean_free_object(x_34);
x_41 = l_Lean_Meta_Simp_Result_getProof(x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_reduceDIte___closed__4;
lean_inc(x_43);
lean_inc_ref(x_27);
x_45 = l_Lean_mkAppB(x_44, x_27, x_43);
lean_inc_ref(x_18);
x_46 = l_Lean_Expr_app___override(x_18, x_45);
x_47 = l_Lean_Expr_headBeta(x_46);
x_48 = ((lean_object*)(l_reduceDIte___closed__6));
x_49 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_50 = l_Lean_mkConst(x_48, x_49);
x_51 = l_Lean_mkApp5(x_50, x_30, x_27, x_24, x_21, x_18);
x_52 = l_Lean_Expr_app___override(x_51, x_43);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_33);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
lean_dec(x_41);
x_57 = l_reduceDIte___closed__4;
lean_inc(x_56);
lean_inc_ref(x_27);
x_58 = l_Lean_mkAppB(x_57, x_27, x_56);
lean_inc_ref(x_18);
x_59 = l_Lean_Expr_app___override(x_18, x_58);
x_60 = l_Lean_Expr_headBeta(x_59);
x_61 = ((lean_object*)(l_reduceDIte___closed__6));
x_62 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_63 = l_Lean_mkConst(x_61, x_62);
x_64 = l_Lean_mkApp5(x_63, x_30, x_27, x_24, x_21, x_18);
x_65 = l_Lean_Expr_app___override(x_64, x_56);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_33);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_70 = !lean_is_exclusive(x_41);
if (x_70 == 0)
{
return x_41;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_41, 0);
lean_inc(x_71);
lean_dec(x_41);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_free_object(x_34);
x_73 = l_Lean_Meta_Simp_Result_getProof(x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_reduceDIte___closed__9;
lean_inc(x_75);
lean_inc_ref(x_27);
x_77 = l_Lean_mkAppB(x_76, x_27, x_75);
lean_inc_ref(x_21);
x_78 = l_Lean_Expr_app___override(x_21, x_77);
x_79 = l_Lean_Expr_headBeta(x_78);
x_80 = ((lean_object*)(l_reduceDIte___closed__11));
x_81 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_82 = l_Lean_mkConst(x_80, x_81);
x_83 = l_Lean_mkApp5(x_82, x_30, x_27, x_24, x_21, x_18);
x_84 = l_Lean_Expr_app___override(x_83, x_75);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_33);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_73, 0, x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
lean_dec(x_73);
x_89 = l_reduceDIte___closed__9;
lean_inc(x_88);
lean_inc_ref(x_27);
x_90 = l_Lean_mkAppB(x_89, x_27, x_88);
lean_inc_ref(x_21);
x_91 = l_Lean_Expr_app___override(x_21, x_90);
x_92 = l_Lean_Expr_headBeta(x_91);
x_93 = ((lean_object*)(l_reduceDIte___closed__11));
x_94 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_95 = l_Lean_mkConst(x_93, x_94);
x_96 = l_Lean_mkApp5(x_95, x_30, x_27, x_24, x_21, x_18);
x_97 = l_Lean_Expr_app___override(x_96, x_88);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_33);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_102 = !lean_is_exclusive(x_73);
if (x_102 == 0)
{
return x_73;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_73, 0);
lean_inc(x_103);
lean_dec(x_73);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
lean_dec(x_34);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
x_107 = l_Lean_Expr_isTrue(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_inc_ref(x_106);
x_108 = l_Lean_Expr_isFalse(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_105);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_109 = ((lean_object*)(l_reduceIte___closed__0));
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_111; 
x_111 = l_Lean_Meta_Simp_Result_getProof(x_105, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_reduceDIte___closed__4;
lean_inc(x_112);
lean_inc_ref(x_27);
x_115 = l_Lean_mkAppB(x_114, x_27, x_112);
lean_inc_ref(x_18);
x_116 = l_Lean_Expr_app___override(x_18, x_115);
x_117 = l_Lean_Expr_headBeta(x_116);
x_118 = ((lean_object*)(l_reduceDIte___closed__6));
x_119 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_120 = l_Lean_mkConst(x_118, x_119);
x_121 = l_Lean_mkApp5(x_120, x_30, x_27, x_24, x_21, x_18);
x_122 = l_Lean_Expr_app___override(x_121, x_112);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*2, x_33);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
if (lean_is_scalar(x_113)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_113;
}
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_127 = lean_ctor_get(x_111, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_128 = x_111;
} else {
 lean_dec_ref(x_111);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
}
else
{
lean_object* x_130; 
x_130 = l_Lean_Meta_Simp_Result_getProof(x_105, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = l_reduceDIte___closed__9;
lean_inc(x_131);
lean_inc_ref(x_27);
x_134 = l_Lean_mkAppB(x_133, x_27, x_131);
lean_inc_ref(x_21);
x_135 = l_Lean_Expr_app___override(x_21, x_134);
x_136 = l_Lean_Expr_headBeta(x_135);
x_137 = ((lean_object*)(l_reduceDIte___closed__11));
x_138 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_139 = l_Lean_mkConst(x_137, x_138);
x_140 = l_Lean_mkApp5(x_139, x_30, x_27, x_24, x_21, x_18);
x_141 = l_Lean_Expr_app___override(x_140, x_131);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_33);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_132)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_132;
}
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_146 = lean_ctor_get(x_130, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_147 = x_130;
} else {
 lean_dec_ref(x_130);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_149 = !lean_is_exclusive(x_34);
if (x_149 == 0)
{
return x_34;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_34, 0);
lean_inc(x_150);
lean_dec(x_34);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l_reduceIte___closed__0));
if (lean_is_scalar(x_12)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_12;
}
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_152; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_10);
if (x_152 == 0)
{
return x_10;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_10, 0);
lean_inc(x_153);
lean_dec(x_10);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
}
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_reduceDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_4 = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
return x_2;
}
}
static lean_object* _init_l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; 
x_14 = l_Lean_Meta_Simp_inDSimp___redArg(x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = ((lean_object*)(l_dreduceIte___closed__0));
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; 
lean_free_object(x_14);
x_19 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_25 = l_Lean_Expr_cleanupAnnotations(x_20);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_40 = ((lean_object*)(l_reduceIte___closed__2));
x_41 = l_Lean_Expr_isConstOf(x_39, x_40);
lean_dec_ref(x_39);
if (x_41 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_42; 
lean_dec(x_21);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_42 = lean_simp(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_123; uint8_t x_124; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_123 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_123);
lean_dec(x_43);
lean_inc_ref(x_123);
x_124 = l_Lean_Expr_isTrue(x_123);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Expr_isFalse(x_123);
x_45 = x_125;
goto block_122;
}
else
{
lean_dec_ref(x_123);
x_45 = x_124;
goto block_122;
}
block_122:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_44);
x_48 = lean_st_ref_get(x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = ((lean_object*)(l_dreduceIte___closed__3));
x_51 = l_Lean_Environment_contains(x_49, x_50, x_41);
if (x_51 == 0)
{
lean_object* x_52; 
lean_inc(x_6);
x_52 = l_Lean_Meta_whnfD(x_33, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_53, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_Expr_cleanupAnnotations(x_56);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_57);
lean_free_object(x_54);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_dec_ref(x_59);
lean_free_object(x_54);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_62 = ((lean_object*)(l_dreduceIte___closed__5));
x_63 = l_Lean_Expr_isConstOf(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_27);
x_64 = ((lean_object*)(l_dreduceIte___closed__7));
x_65 = l_Lean_Expr_isConstOf(x_61, x_64);
lean_dec_ref(x_61);
if (x_65 == 0)
{
lean_free_object(x_54);
lean_dec_ref(x_30);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_30);
lean_ctor_set(x_54, 0, x_66);
return x_54;
}
}
else
{
lean_object* x_67; 
lean_dec_ref(x_61);
lean_dec_ref(x_30);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_27);
lean_ctor_set(x_54, 0, x_67);
return x_54;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec(x_54);
x_69 = l_Lean_Expr_cleanupAnnotations(x_68);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_72 = l_Lean_Expr_isApp(x_71);
if (x_72 == 0)
{
lean_dec_ref(x_71);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_74 = ((lean_object*)(l_dreduceIte___closed__5));
x_75 = l_Lean_Expr_isConstOf(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_dec_ref(x_27);
x_76 = ((lean_object*)(l_dreduceIte___closed__7));
x_77 = l_Lean_Expr_isConstOf(x_73, x_76);
lean_dec_ref(x_73);
if (x_77 == 0)
{
lean_dec_ref(x_30);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_30);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_73);
lean_dec_ref(x_30);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_27);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_82 = !lean_is_exclusive(x_54);
if (x_82 == 0)
{
return x_54;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_54, 0);
lean_inc(x_83);
lean_dec(x_54);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_52);
if (x_85 == 0)
{
return x_52;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_52, 0);
lean_inc(x_86);
lean_dec(x_52);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = ((lean_object*)(l_dreduceIte___closed__8));
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Expr_proj___override(x_88, x_89, x_33);
lean_inc(x_6);
x_91 = l_Lean_Meta_whnfD(x_90, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_92, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = l_Lean_Expr_cleanupAnnotations(x_95);
x_97 = ((lean_object*)(l_dreduceIte___closed__11));
x_98 = l_Lean_Expr_isConstOf(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_dec_ref(x_27);
x_99 = ((lean_object*)(l_dreduceIte___closed__13));
x_100 = l_Lean_Expr_isConstOf(x_96, x_99);
lean_dec_ref(x_96);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec_ref(x_30);
x_101 = ((lean_object*)(l_dreduceIte___closed__0));
lean_ctor_set(x_93, 0, x_101);
return x_93;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_30);
lean_ctor_set(x_93, 0, x_102);
return x_93;
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_96);
lean_dec_ref(x_30);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_27);
lean_ctor_set(x_93, 0, x_103);
return x_93;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
lean_dec(x_93);
x_105 = l_Lean_Expr_cleanupAnnotations(x_104);
x_106 = ((lean_object*)(l_dreduceIte___closed__11));
x_107 = l_Lean_Expr_isConstOf(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_dec_ref(x_27);
x_108 = ((lean_object*)(l_dreduceIte___closed__13));
x_109 = l_Lean_Expr_isConstOf(x_105, x_108);
lean_dec_ref(x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec_ref(x_30);
x_110 = ((lean_object*)(l_dreduceIte___closed__0));
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_30);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_105);
lean_dec_ref(x_30);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_27);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_116 = !lean_is_exclusive(x_93);
if (x_116 == 0)
{
return x_93;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
lean_dec(x_93);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_6);
x_119 = !lean_is_exclusive(x_91);
if (x_119 == 0)
{
return x_91;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_91, 0);
lean_inc(x_120);
lean_dec(x_91);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
}
}
else
{
uint8_t x_126; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_126 = !lean_is_exclusive(x_42);
if (x_126 == 0)
{
return x_42;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_42, 0);
lean_inc(x_127);
lean_dec(x_42);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_129; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_19);
if (x_129 == 0)
{
return x_19;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_19, 0);
lean_inc(x_130);
lean_dec(x_19);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_14, 0);
lean_inc(x_132);
lean_dec(x_14);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_134 = ((lean_object*)(l_dreduceIte___closed__0));
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
lean_object* x_136; 
x_136 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_142; uint8_t x_143; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_142 = l_Lean_Expr_cleanupAnnotations(x_137);
x_143 = l_Lean_Expr_isApp(x_142);
if (x_143 == 0)
{
lean_dec_ref(x_142);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_144);
x_145 = l_Lean_Expr_appFnCleanup___redArg(x_142);
x_146 = l_Lean_Expr_isApp(x_145);
if (x_146 == 0)
{
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc_ref(x_147);
x_148 = l_Lean_Expr_appFnCleanup___redArg(x_145);
x_149 = l_Lean_Expr_isApp(x_148);
if (x_149 == 0)
{
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc_ref(x_150);
x_151 = l_Lean_Expr_appFnCleanup___redArg(x_148);
x_152 = l_Lean_Expr_isApp(x_151);
if (x_152 == 0)
{
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_151, 1);
lean_inc_ref(x_153);
x_154 = l_Lean_Expr_appFnCleanup___redArg(x_151);
x_155 = l_Lean_Expr_isApp(x_154);
if (x_155 == 0)
{
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = l_Lean_Expr_appFnCleanup___redArg(x_154);
x_157 = ((lean_object*)(l_reduceIte___closed__2));
x_158 = l_Lean_Expr_isConstOf(x_156, x_157);
lean_dec_ref(x_156);
if (x_158 == 0)
{
lean_dec_ref(x_153);
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_141;
}
else
{
lean_object* x_159; 
lean_dec(x_138);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_159 = lean_simp(x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_219; uint8_t x_220; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_219 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_219);
lean_dec(x_160);
lean_inc_ref(x_219);
x_220 = l_Lean_Expr_isTrue(x_219);
if (x_220 == 0)
{
uint8_t x_221; 
x_221 = l_Lean_Expr_isFalse(x_219);
x_162 = x_221;
goto block_218;
}
else
{
lean_dec_ref(x_219);
x_162 = x_220;
goto block_218;
}
block_218:
{
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_163 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_161);
x_165 = lean_st_ref_get(x_8);
x_166 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_166);
lean_dec(x_165);
x_167 = ((lean_object*)(l_dreduceIte___closed__3));
x_168 = l_Lean_Environment_contains(x_166, x_167, x_158);
if (x_168 == 0)
{
lean_object* x_169; 
lean_inc(x_6);
x_169 = l_Lean_Meta_whnfD(x_150, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_170, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = l_Lean_Expr_cleanupAnnotations(x_172);
x_175 = l_Lean_Expr_isApp(x_174);
if (x_175 == 0)
{
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = l_Lean_Expr_appFnCleanup___redArg(x_174);
x_177 = l_Lean_Expr_isApp(x_176);
if (x_177 == 0)
{
lean_dec_ref(x_176);
lean_dec(x_173);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = l_Lean_Expr_appFnCleanup___redArg(x_176);
x_179 = ((lean_object*)(l_dreduceIte___closed__5));
x_180 = l_Lean_Expr_isConstOf(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
lean_dec_ref(x_144);
x_181 = ((lean_object*)(l_dreduceIte___closed__7));
x_182 = l_Lean_Expr_isConstOf(x_178, x_181);
lean_dec_ref(x_178);
if (x_182 == 0)
{
lean_dec(x_173);
lean_dec_ref(x_147);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_147);
if (lean_is_scalar(x_173)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_173;
}
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_178);
lean_dec_ref(x_147);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_144);
if (lean_is_scalar(x_173)) {
 x_186 = lean_alloc_ctor(0, 1, 0);
} else {
 x_186 = x_173;
}
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec_ref(x_147);
lean_dec_ref(x_144);
x_187 = lean_ctor_get(x_171, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_188 = x_171;
} else {
 lean_dec_ref(x_171);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_6);
x_190 = lean_ctor_get(x_169, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_191 = x_169;
} else {
 lean_dec_ref(x_169);
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
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = ((lean_object*)(l_dreduceIte___closed__8));
x_194 = lean_unsigned_to_nat(0u);
x_195 = l_Lean_Expr_proj___override(x_193, x_194, x_150);
lean_inc(x_6);
x_196 = l_Lean_Meta_whnfD(x_195, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_197, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = l_Lean_Expr_cleanupAnnotations(x_199);
x_202 = ((lean_object*)(l_dreduceIte___closed__11));
x_203 = l_Lean_Expr_isConstOf(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
lean_dec_ref(x_144);
x_204 = ((lean_object*)(l_dreduceIte___closed__13));
x_205 = l_Lean_Expr_isConstOf(x_201, x_204);
lean_dec_ref(x_201);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_147);
x_206 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_200)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_200;
}
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_147);
if (lean_is_scalar(x_200)) {
 x_209 = lean_alloc_ctor(0, 1, 0);
} else {
 x_209 = x_200;
}
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec_ref(x_201);
lean_dec_ref(x_147);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_144);
if (lean_is_scalar(x_200)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_200;
}
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_147);
lean_dec_ref(x_144);
x_212 = lean_ctor_get(x_198, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_213 = x_198;
} else {
 lean_dec_ref(x_198);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_6);
x_215 = lean_ctor_get(x_196, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_216 = x_196;
} else {
 lean_dec_ref(x_196);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec_ref(x_144);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_222 = lean_ctor_get(x_159, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_223 = x_159;
} else {
 lean_dec_ref(x_159);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
}
}
}
}
}
block_141:
{
lean_object* x_139; lean_object* x_140; 
x_139 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 1, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_225 = lean_ctor_get(x_136, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_226 = x_136;
} else {
 lean_dec_ref(x_136);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_228 = !lean_is_exclusive(x_14);
if (x_228 == 0)
{
return x_14;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_14, 0);
lean_inc(x_229);
lean_dec(x_14);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_dreduceIte___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_dreduceIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_));
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
x_4 = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_();
return x_2;
}
}
static lean_object* _init_l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; 
x_14 = l_Lean_Meta_Simp_inDSimp___redArg(x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = ((lean_object*)(l_dreduceIte___closed__0));
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; 
lean_free_object(x_14);
x_19 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_25 = l_Lean_Expr_cleanupAnnotations(x_20);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_40 = ((lean_object*)(l_reduceDIte___closed__1));
x_41 = l_Lean_Expr_isConstOf(x_39, x_40);
lean_dec_ref(x_39);
if (x_41 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_24;
}
else
{
lean_object* x_42; 
lean_dec(x_21);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_36);
x_42 = lean_simp(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_155; uint8_t x_156; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_155 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_155);
lean_dec(x_43);
lean_inc_ref(x_155);
x_156 = l_Lean_Expr_isTrue(x_155);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Expr_isFalse(x_155);
x_45 = x_157;
goto block_154;
}
else
{
lean_dec_ref(x_155);
x_45 = x_156;
goto block_154;
}
block_154:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_44);
x_48 = lean_st_ref_get(x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = ((lean_object*)(l_dreduceIte___closed__3));
x_51 = l_Lean_Environment_contains(x_49, x_50, x_41);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_36);
lean_inc(x_6);
x_52 = l_Lean_Meta_whnfD(x_33, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_53, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_Expr_cleanupAnnotations(x_56);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_57);
lean_free_object(x_54);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_59);
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_free_object(x_54);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_63 = ((lean_object*)(l_dreduceIte___closed__5));
x_64 = l_Lean_Expr_isConstOf(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_27);
x_65 = ((lean_object*)(l_dreduceIte___closed__7));
x_66 = l_Lean_Expr_isConstOf(x_62, x_65);
lean_dec_ref(x_62);
if (x_66 == 0)
{
lean_dec_ref(x_59);
lean_free_object(x_54);
lean_dec_ref(x_30);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lean_Expr_app___override(x_30, x_59);
x_68 = l_Lean_Expr_headBeta(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_54, 0, x_69);
return x_54;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_62);
lean_dec_ref(x_30);
x_70 = l_Lean_Expr_app___override(x_27, x_59);
x_71 = l_Lean_Expr_headBeta(x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_54, 0, x_72);
return x_54;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
lean_dec(x_54);
x_74 = l_Lean_Expr_cleanupAnnotations(x_73);
x_75 = l_Lean_Expr_isApp(x_74);
if (x_75 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_76);
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_74);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_80 = ((lean_object*)(l_dreduceIte___closed__5));
x_81 = l_Lean_Expr_isConstOf(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
lean_dec_ref(x_27);
x_82 = ((lean_object*)(l_dreduceIte___closed__7));
x_83 = l_Lean_Expr_isConstOf(x_79, x_82);
lean_dec_ref(x_79);
if (x_83 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_30);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = l_Lean_Expr_app___override(x_30, x_76);
x_85 = l_Lean_Expr_headBeta(x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_79);
lean_dec_ref(x_30);
x_88 = l_Lean_Expr_app___override(x_27, x_76);
x_89 = l_Lean_Expr_headBeta(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_92 = !lean_is_exclusive(x_54);
if (x_92 == 0)
{
return x_54;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_54, 0);
lean_inc(x_93);
lean_dec(x_54);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_52);
if (x_95 == 0)
{
return x_52;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_52, 0);
lean_inc(x_96);
lean_dec(x_52);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = ((lean_object*)(l_dreduceIte___closed__8));
x_99 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_33);
x_100 = l_Lean_Expr_proj___override(x_98, x_99, x_33);
lean_inc(x_6);
x_101 = l_Lean_Meta_whnfD(x_100, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_102, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = l_Lean_Expr_cleanupAnnotations(x_105);
x_107 = ((lean_object*)(l_dreduceIte___closed__11));
x_108 = l_Lean_Expr_isConstOf(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
lean_dec_ref(x_27);
x_109 = ((lean_object*)(l_dreduceIte___closed__13));
x_110 = l_Lean_Expr_isConstOf(x_106, x_109);
lean_dec_ref(x_106);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
x_111 = ((lean_object*)(l_dreduceIte___closed__0));
lean_ctor_set(x_103, 0, x_111);
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_unsigned_to_nat(1u);
x_113 = l_Lean_Expr_proj___override(x_98, x_112, x_33);
x_114 = l_Lean_Meta_mkExpectedPropHint(x_113, x_36);
x_115 = l_Lean_Expr_app___override(x_30, x_114);
x_116 = l_Lean_Expr_headBeta(x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_103, 0, x_117);
return x_103;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_106);
lean_dec_ref(x_30);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Expr_proj___override(x_98, x_118, x_33);
x_120 = l_Lean_mkNot(x_36);
x_121 = l_Lean_Meta_mkExpectedPropHint(x_119, x_120);
x_122 = l_Lean_Expr_app___override(x_27, x_121);
x_123 = l_Lean_Expr_headBeta(x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_103, 0, x_124);
return x_103;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
lean_dec(x_103);
x_126 = l_Lean_Expr_cleanupAnnotations(x_125);
x_127 = ((lean_object*)(l_dreduceIte___closed__11));
x_128 = l_Lean_Expr_isConstOf(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
lean_dec_ref(x_27);
x_129 = ((lean_object*)(l_dreduceIte___closed__13));
x_130 = l_Lean_Expr_isConstOf(x_126, x_129);
lean_dec_ref(x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
x_131 = ((lean_object*)(l_dreduceIte___closed__0));
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_unsigned_to_nat(1u);
x_134 = l_Lean_Expr_proj___override(x_98, x_133, x_33);
x_135 = l_Lean_Meta_mkExpectedPropHint(x_134, x_36);
x_136 = l_Lean_Expr_app___override(x_30, x_135);
x_137 = l_Lean_Expr_headBeta(x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_126);
lean_dec_ref(x_30);
x_140 = lean_unsigned_to_nat(1u);
x_141 = l_Lean_Expr_proj___override(x_98, x_140, x_33);
x_142 = l_Lean_mkNot(x_36);
x_143 = l_Lean_Meta_mkExpectedPropHint(x_141, x_142);
x_144 = l_Lean_Expr_app___override(x_27, x_143);
x_145 = l_Lean_Expr_headBeta(x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
x_148 = !lean_is_exclusive(x_103);
if (x_148 == 0)
{
return x_103;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_103, 0);
lean_inc(x_149);
lean_dec(x_103);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_6);
x_151 = !lean_is_exclusive(x_101);
if (x_151 == 0)
{
return x_101;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_101, 0);
lean_inc(x_152);
lean_dec(x_101);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_158 = !lean_is_exclusive(x_42);
if (x_158 == 0)
{
return x_42;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_42, 0);
lean_inc(x_159);
lean_dec(x_42);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
}
}
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_161; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_19);
if (x_161 == 0)
{
return x_19;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_19, 0);
lean_inc(x_162);
lean_dec(x_19);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
}
else
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_14, 0);
lean_inc(x_164);
lean_dec(x_14);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = ((lean_object*)(l_dreduceIte___closed__0));
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
else
{
lean_object* x_168; 
x_168 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_174; uint8_t x_175; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_174 = l_Lean_Expr_cleanupAnnotations(x_169);
x_175 = l_Lean_Expr_isApp(x_174);
if (x_175 == 0)
{
lean_dec_ref(x_174);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_174, 1);
lean_inc_ref(x_176);
x_177 = l_Lean_Expr_appFnCleanup___redArg(x_174);
x_178 = l_Lean_Expr_isApp(x_177);
if (x_178 == 0)
{
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_177, 1);
lean_inc_ref(x_179);
x_180 = l_Lean_Expr_appFnCleanup___redArg(x_177);
x_181 = l_Lean_Expr_isApp(x_180);
if (x_181 == 0)
{
lean_dec_ref(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_180, 1);
lean_inc_ref(x_182);
x_183 = l_Lean_Expr_appFnCleanup___redArg(x_180);
x_184 = l_Lean_Expr_isApp(x_183);
if (x_184 == 0)
{
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_183, 1);
lean_inc_ref(x_185);
x_186 = l_Lean_Expr_appFnCleanup___redArg(x_183);
x_187 = l_Lean_Expr_isApp(x_186);
if (x_187 == 0)
{
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = l_Lean_Expr_appFnCleanup___redArg(x_186);
x_189 = ((lean_object*)(l_reduceDIte___closed__1));
x_190 = l_Lean_Expr_isConstOf(x_188, x_189);
lean_dec_ref(x_188);
if (x_190 == 0)
{
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
goto block_173;
}
else
{
lean_object* x_191; 
lean_dec(x_170);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_185);
x_191 = lean_simp(x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_267; uint8_t x_268; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
x_267 = lean_ctor_get(x_192, 0);
lean_inc_ref(x_267);
lean_dec(x_192);
lean_inc_ref(x_267);
x_268 = l_Lean_Expr_isTrue(x_267);
if (x_268 == 0)
{
uint8_t x_269; 
x_269 = l_Lean_Expr_isFalse(x_267);
x_194 = x_269;
goto block_266;
}
else
{
lean_dec_ref(x_267);
x_194 = x_268;
goto block_266;
}
block_266:
{
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_195 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 1, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_193);
x_197 = lean_st_ref_get(x_8);
x_198 = lean_ctor_get(x_197, 0);
lean_inc_ref(x_198);
lean_dec(x_197);
x_199 = ((lean_object*)(l_dreduceIte___closed__3));
x_200 = l_Lean_Environment_contains(x_198, x_199, x_190);
if (x_200 == 0)
{
lean_object* x_201; 
lean_dec_ref(x_185);
lean_inc(x_6);
x_201 = l_Lean_Meta_whnfD(x_182, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_202, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
x_206 = l_Lean_Expr_cleanupAnnotations(x_204);
x_207 = l_Lean_Expr_isApp(x_206);
if (x_207 == 0)
{
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_208);
x_209 = l_Lean_Expr_appFnCleanup___redArg(x_206);
x_210 = l_Lean_Expr_isApp(x_209);
if (x_210 == 0)
{
lean_dec_ref(x_209);
lean_dec_ref(x_208);
lean_dec(x_205);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = l_Lean_Expr_appFnCleanup___redArg(x_209);
x_212 = ((lean_object*)(l_dreduceIte___closed__5));
x_213 = l_Lean_Expr_isConstOf(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
lean_dec_ref(x_176);
x_214 = ((lean_object*)(l_dreduceIte___closed__7));
x_215 = l_Lean_Expr_isConstOf(x_211, x_214);
lean_dec_ref(x_211);
if (x_215 == 0)
{
lean_dec_ref(x_208);
lean_dec(x_205);
lean_dec_ref(x_179);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = l_Lean_Expr_app___override(x_179, x_208);
x_217 = l_Lean_Expr_headBeta(x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
if (lean_is_scalar(x_205)) {
 x_219 = lean_alloc_ctor(0, 1, 0);
} else {
 x_219 = x_205;
}
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_211);
lean_dec_ref(x_179);
x_220 = l_Lean_Expr_app___override(x_176, x_208);
x_221 = l_Lean_Expr_headBeta(x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_205)) {
 x_223 = lean_alloc_ctor(0, 1, 0);
} else {
 x_223 = x_205;
}
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec_ref(x_179);
lean_dec_ref(x_176);
x_224 = lean_ctor_get(x_203, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_225 = x_203;
} else {
 lean_dec_ref(x_203);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_6);
x_227 = lean_ctor_get(x_201, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_228 = x_201;
} else {
 lean_dec_ref(x_201);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = ((lean_object*)(l_dreduceIte___closed__8));
x_231 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_182);
x_232 = l_Lean_Expr_proj___override(x_230, x_231, x_182);
lean_inc(x_6);
x_233 = l_Lean_Meta_whnfD(x_232, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_234, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Expr_cleanupAnnotations(x_236);
x_239 = ((lean_object*)(l_dreduceIte___closed__11));
x_240 = l_Lean_Expr_isConstOf(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; 
lean_dec_ref(x_176);
x_241 = ((lean_object*)(l_dreduceIte___closed__13));
x_242 = l_Lean_Expr_isConstOf(x_238, x_241);
lean_dec_ref(x_238);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
x_243 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_237)) {
 x_244 = lean_alloc_ctor(0, 1, 0);
} else {
 x_244 = x_237;
}
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_unsigned_to_nat(1u);
x_246 = l_Lean_Expr_proj___override(x_230, x_245, x_182);
x_247 = l_Lean_Meta_mkExpectedPropHint(x_246, x_185);
x_248 = l_Lean_Expr_app___override(x_179, x_247);
x_249 = l_Lean_Expr_headBeta(x_248);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
if (lean_is_scalar(x_237)) {
 x_251 = lean_alloc_ctor(0, 1, 0);
} else {
 x_251 = x_237;
}
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec_ref(x_238);
lean_dec_ref(x_179);
x_252 = lean_unsigned_to_nat(1u);
x_253 = l_Lean_Expr_proj___override(x_230, x_252, x_182);
x_254 = l_Lean_mkNot(x_185);
x_255 = l_Lean_Meta_mkExpectedPropHint(x_253, x_254);
x_256 = l_Lean_Expr_app___override(x_176, x_255);
x_257 = l_Lean_Expr_headBeta(x_256);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
if (lean_is_scalar(x_237)) {
 x_259 = lean_alloc_ctor(0, 1, 0);
} else {
 x_259 = x_237;
}
lean_ctor_set(x_259, 0, x_258);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
x_260 = lean_ctor_get(x_235, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_261 = x_235;
} else {
 lean_dec_ref(x_235);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_6);
x_263 = lean_ctor_get(x_233, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_264 = x_233;
} else {
 lean_dec_ref(x_233);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 1, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_263);
return x_265;
}
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_176);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_270 = lean_ctor_get(x_191, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_271 = x_191;
} else {
 lean_dec_ref(x_191);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_270);
return x_272;
}
}
}
}
}
}
}
block_173:
{
lean_object* x_171; lean_object* x_172; 
x_171 = ((lean_object*)(l_dreduceIte___closed__0));
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 1, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_273 = lean_ctor_get(x_168, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_274 = x_168;
} else {
 lean_dec_ref(x_168);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_276 = !lean_is_exclusive(x_14);
if (x_276 == 0)
{
return x_14;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_14, 0);
lean_inc(x_277);
lean_dec(x_14);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_dreduceIte___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_dreduceDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_));
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
x_4 = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_();
return x_2;
}
}
static lean_object* _init_l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_));
x_3 = 0;
x_4 = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_;
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_reduceIte___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_reduceCtorEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_reduceIte___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_reduceCtorEq___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l_reduceCtorEq___lam__2___closed__4() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t x_1, uint8_t x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; 
x_13 = l_reduceCtorEq___lam__2___closed__2;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
x_21 = l_Lean_Meta_mkNoConfusion(x_13, x_4, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_reduceCtorEq___lam__2___closed__3;
x_24 = lean_array_push(x_23, x_4);
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_24, x_22, x_1, x_2, x_1, x_2, x_25, x_8, x_9, x_10, x_11);
lean_dec_ref(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Context_config(x_8);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint64_t x_41; uint8_t x_42; 
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_8, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 6);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 1);
x_38 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 2);
x_39 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 3);
x_40 = 1;
lean_ctor_set_uint8(x_28, 9, x_40);
x_41 = l_Lean_Meta_Context_configKey(x_8);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_8, 6);
lean_dec(x_43);
x_44 = lean_ctor_get(x_8, 5);
lean_dec(x_44);
x_45 = lean_ctor_get(x_8, 4);
lean_dec(x_45);
x_46 = lean_ctor_get(x_8, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_8, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_8, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_8, 0);
lean_dec(x_49);
x_50 = lean_uint64_shift_right(x_41, x_3);
x_51 = lean_uint64_shift_left(x_50, x_3);
x_52 = l_reduceCtorEq___lam__2___closed__4;
x_53 = lean_uint64_lor(x_51, x_52);
x_54 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set_uint64(x_54, sizeof(void*)*1, x_53);
lean_ctor_set(x_8, 0, x_54);
x_55 = l_Lean_Meta_mkEqFalse_x27(x_27, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_14 = x_56;
x_15 = lean_box(0);
goto block_20;
}
else
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
x_14 = x_57;
x_15 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_8);
x_61 = lean_uint64_shift_right(x_41, x_3);
x_62 = lean_uint64_shift_left(x_61, x_3);
x_63 = l_reduceCtorEq___lam__2___closed__4;
x_64 = lean_uint64_lor(x_62, x_63);
x_65 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_65, 0, x_28);
lean_ctor_set_uint64(x_65, sizeof(void*)*1, x_64);
x_66 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_31);
lean_ctor_set(x_66, 2, x_32);
lean_ctor_set(x_66, 3, x_33);
lean_ctor_set(x_66, 4, x_34);
lean_ctor_set(x_66, 5, x_35);
lean_ctor_set(x_66, 6, x_36);
lean_ctor_set_uint8(x_66, sizeof(void*)*7, x_30);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 1, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 2, x_38);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 3, x_39);
x_67 = l_Lean_Meta_mkEqFalse_x27(x_27, x_66, x_9, x_10, x_11);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_14 = x_68;
x_15 = lean_box(0);
goto block_20;
}
else
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_14 = x_69;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_73 = lean_ctor_get_uint8(x_28, 0);
x_74 = lean_ctor_get_uint8(x_28, 1);
x_75 = lean_ctor_get_uint8(x_28, 2);
x_76 = lean_ctor_get_uint8(x_28, 3);
x_77 = lean_ctor_get_uint8(x_28, 4);
x_78 = lean_ctor_get_uint8(x_28, 5);
x_79 = lean_ctor_get_uint8(x_28, 6);
x_80 = lean_ctor_get_uint8(x_28, 7);
x_81 = lean_ctor_get_uint8(x_28, 8);
x_82 = lean_ctor_get_uint8(x_28, 10);
x_83 = lean_ctor_get_uint8(x_28, 11);
x_84 = lean_ctor_get_uint8(x_28, 12);
x_85 = lean_ctor_get_uint8(x_28, 13);
x_86 = lean_ctor_get_uint8(x_28, 14);
x_87 = lean_ctor_get_uint8(x_28, 15);
x_88 = lean_ctor_get_uint8(x_28, 16);
x_89 = lean_ctor_get_uint8(x_28, 17);
x_90 = lean_ctor_get_uint8(x_28, 18);
lean_dec(x_28);
x_91 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_92 = lean_ctor_get(x_8, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_8, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_8, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_8, 6);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 1);
x_99 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 2);
x_100 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 3);
x_101 = 1;
x_102 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_102, 0, x_73);
lean_ctor_set_uint8(x_102, 1, x_74);
lean_ctor_set_uint8(x_102, 2, x_75);
lean_ctor_set_uint8(x_102, 3, x_76);
lean_ctor_set_uint8(x_102, 4, x_77);
lean_ctor_set_uint8(x_102, 5, x_78);
lean_ctor_set_uint8(x_102, 6, x_79);
lean_ctor_set_uint8(x_102, 7, x_80);
lean_ctor_set_uint8(x_102, 8, x_81);
lean_ctor_set_uint8(x_102, 9, x_101);
lean_ctor_set_uint8(x_102, 10, x_82);
lean_ctor_set_uint8(x_102, 11, x_83);
lean_ctor_set_uint8(x_102, 12, x_84);
lean_ctor_set_uint8(x_102, 13, x_85);
lean_ctor_set_uint8(x_102, 14, x_86);
lean_ctor_set_uint8(x_102, 15, x_87);
lean_ctor_set_uint8(x_102, 16, x_88);
lean_ctor_set_uint8(x_102, 17, x_89);
lean_ctor_set_uint8(x_102, 18, x_90);
x_103 = l_Lean_Meta_Context_configKey(x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 x_104 = x_8;
} else {
 lean_dec_ref(x_8);
 x_104 = lean_box(0);
}
x_105 = lean_uint64_shift_right(x_103, x_3);
x_106 = lean_uint64_shift_left(x_105, x_3);
x_107 = l_reduceCtorEq___lam__2___closed__4;
x_108 = lean_uint64_lor(x_106, x_107);
x_109 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set_uint64(x_109, sizeof(void*)*1, x_108);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 7, 4);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_92);
lean_ctor_set(x_110, 2, x_93);
lean_ctor_set(x_110, 3, x_94);
lean_ctor_set(x_110, 4, x_95);
lean_ctor_set(x_110, 5, x_96);
lean_ctor_set(x_110, 6, x_97);
lean_ctor_set_uint8(x_110, sizeof(void*)*7, x_91);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 1, x_98);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 2, x_99);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 3, x_100);
x_111 = l_Lean_Meta_mkEqFalse_x27(x_27, x_110, x_9, x_10, x_11);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_14 = x_112;
x_15 = lean_box(0);
goto block_20;
}
else
{
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_14 = x_113;
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_117 = !lean_is_exclusive(x_26);
if (x_117 == 0)
{
return x_26;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_26, 0);
lean_inc(x_118);
lean_dec(x_26);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
x_120 = !lean_is_exclusive(x_21);
if (x_120 == 0)
{
return x_21;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_21, 0);
lean_inc(x_121);
lean_dec(x_21);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint64_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_16 = l_reduceCtorEq___lam__2(x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 0;
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static uint64_t _init_l_reduceCtorEq___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 3;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_reduceCtorEq___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Meta_Context_config(x_5);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_5, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 6);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
lean_inc_ref(x_1);
x_27 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; uint64_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = 3;
lean_ctor_set_uint8(x_15, 9, x_29);
x_30 = l_Lean_Meta_Context_configKey(x_5);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_32 = lean_ctor_get(x_5, 6);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 5);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 4);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 0);
lean_dec(x_38);
x_39 = 2;
x_40 = lean_uint64_shift_right(x_30, x_39);
x_41 = lean_uint64_shift_left(x_40, x_39);
x_42 = l_reduceCtorEq___closed__0;
x_43 = lean_uint64_lor(x_41, x_42);
x_44 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set_uint64(x_44, sizeof(void*)*1, x_43);
lean_ctor_set(x_5, 0, x_44);
x_45 = l_Lean_Expr_cleanupAnnotations(x_28);
x_46 = l_Lean_Expr_isApp(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_45);
lean_dec_ref(x_1);
x_47 = lean_box(0);
x_48 = l_reduceCtorEq___lam__0(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_48;
goto block_14;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_49);
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_45);
x_51 = l_Lean_Expr_isApp(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_1);
x_52 = lean_box(0);
x_53 = l_reduceCtorEq___lam__0(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_53;
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_54);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_50);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_49);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = l_reduceCtorEq___lam__0(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_58;
goto block_14;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_60 = ((lean_object*)(l_reduceCtorEq___closed__2));
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
lean_dec_ref(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_54);
lean_dec_ref(x_49);
lean_dec_ref(x_1);
x_62 = lean_box(0);
x_63 = l_reduceCtorEq___lam__0(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_63;
goto block_14;
}
else
{
lean_object* x_64; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_64 = l_Lean_Meta_constructorApp_x27_x3f(x_54, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_66 = l_Lean_Meta_constructorApp_x27_x3f(x_49, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_65) == 1)
{
if (lean_obj_tag(x_67) == 1)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
lean_dec_ref(x_65);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec_ref(x_67);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec_ref(x_75);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_name_eq(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
if (x_61 == 0)
{
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_71;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_68);
x_81 = lean_box(x_80);
x_82 = lean_box(x_61);
x_83 = l_reduceCtorEq___boxed__const__1;
x_84 = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 12, 3);
lean_closure_set(x_84, 0, x_81);
lean_closure_set(x_84, 1, x_82);
lean_closure_set(x_84, 2, x_83);
x_85 = ((lean_object*)(l_reduceCtorEq___closed__4));
x_86 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(x_85, x_1, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = x_86;
goto block_14;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_71;
}
}
else
{
lean_object* x_87; 
lean_dec(x_68);
lean_dec_ref(x_1);
x_87 = l_reduceCtorEq___lam__1(x_65, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_67);
lean_dec_ref(x_65);
x_10 = x_87;
goto block_14;
}
}
else
{
lean_object* x_88; 
lean_dec(x_68);
lean_dec_ref(x_1);
x_88 = l_reduceCtorEq___lam__1(x_65, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_67);
lean_dec(x_65);
x_10 = x_88;
goto block_14;
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = ((lean_object*)(l_reduceIte___closed__0));
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
uint8_t x_89; 
lean_dec(x_65);
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_66);
if (x_89 == 0)
{
return x_66;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
lean_dec(x_66);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_49);
lean_dec_ref(x_5);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_64);
if (x_92 == 0)
{
return x_64;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_64, 0);
lean_inc(x_93);
lean_dec(x_64);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
}
}
else
{
uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_5);
x_95 = 2;
x_96 = lean_uint64_shift_right(x_30, x_95);
x_97 = lean_uint64_shift_left(x_96, x_95);
x_98 = l_reduceCtorEq___closed__0;
x_99 = lean_uint64_lor(x_97, x_98);
x_100 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set_uint64(x_100, sizeof(void*)*1, x_99);
x_101 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_18);
lean_ctor_set(x_101, 2, x_19);
lean_ctor_set(x_101, 3, x_20);
lean_ctor_set(x_101, 4, x_21);
lean_ctor_set(x_101, 5, x_22);
lean_ctor_set(x_101, 6, x_23);
lean_ctor_set_uint8(x_101, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 1, x_24);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 2, x_25);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 3, x_26);
x_102 = l_Lean_Expr_cleanupAnnotations(x_28);
x_103 = l_Lean_Expr_isApp(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_102);
lean_dec_ref(x_1);
x_104 = lean_box(0);
x_105 = l_reduceCtorEq___lam__0(x_104, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_105;
goto block_14;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_106);
x_107 = l_Lean_Expr_appFnCleanup___redArg(x_102);
x_108 = l_Lean_Expr_isApp(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_109 = lean_box(0);
x_110 = l_reduceCtorEq___lam__0(x_109, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_110;
goto block_14;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_111);
x_112 = l_Lean_Expr_appFnCleanup___redArg(x_107);
x_113 = l_Lean_Expr_isApp(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_114 = lean_box(0);
x_115 = l_reduceCtorEq___lam__0(x_114, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_115;
goto block_14;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_117 = ((lean_object*)(l_reduceCtorEq___closed__2));
x_118 = l_Lean_Expr_isConstOf(x_116, x_117);
lean_dec_ref(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_111);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_119 = lean_box(0);
x_120 = l_reduceCtorEq___lam__0(x_119, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_120;
goto block_14;
}
else
{
lean_object* x_121; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_101);
x_121 = l_Lean_Meta_constructorApp_x27_x3f(x_111, x_101, x_6, x_7, x_8);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_101);
x_123 = l_Lean_Meta_constructorApp_x27_x3f(x_106, x_101, x_6, x_7, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
if (lean_obj_tag(x_122) == 1)
{
if (lean_obj_tag(x_124) == 1)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_129 = lean_ctor_get(x_122, 0);
lean_inc(x_129);
lean_dec_ref(x_122);
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
lean_dec_ref(x_124);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc_ref(x_134);
lean_dec(x_133);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec_ref(x_132);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = lean_name_eq(x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
if (x_137 == 0)
{
if (x_118 == 0)
{
lean_dec_ref(x_101);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_128;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_125);
x_138 = lean_box(x_137);
x_139 = lean_box(x_118);
x_140 = l_reduceCtorEq___boxed__const__1;
x_141 = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 12, 3);
lean_closure_set(x_141, 0, x_138);
lean_closure_set(x_141, 1, x_139);
lean_closure_set(x_141, 2, x_140);
x_142 = ((lean_object*)(l_reduceCtorEq___closed__4));
x_143 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(x_142, x_1, x_141, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
x_10 = x_143;
goto block_14;
}
}
else
{
lean_dec_ref(x_101);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_128;
}
}
else
{
lean_object* x_144; 
lean_dec(x_125);
lean_dec_ref(x_1);
x_144 = l_reduceCtorEq___lam__1(x_122, x_124, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_124);
lean_dec_ref(x_122);
x_10 = x_144;
goto block_14;
}
}
else
{
lean_object* x_145; 
lean_dec(x_125);
lean_dec_ref(x_1);
x_145 = l_reduceCtorEq___lam__1(x_122, x_124, x_2, x_3, x_4, x_101, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_101);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_124);
lean_dec(x_122);
x_10 = x_145;
goto block_14;
}
block_128:
{
lean_object* x_126; lean_object* x_127; 
x_126 = ((lean_object*)(l_reduceIte___closed__0));
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_122);
lean_dec_ref(x_101);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_123, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_147 = x_123;
} else {
 lean_dec_ref(x_123);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_106);
lean_dec_ref(x_101);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_121, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_150 = x_121;
} else {
 lean_dec_ref(x_121);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
}
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_free_object(x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_27);
if (x_152 == 0)
{
return x_27;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_27, 0);
lean_inc(x_153);
lean_dec(x_27);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; 
x_155 = lean_ctor_get_uint8(x_15, 0);
x_156 = lean_ctor_get_uint8(x_15, 1);
x_157 = lean_ctor_get_uint8(x_15, 2);
x_158 = lean_ctor_get_uint8(x_15, 3);
x_159 = lean_ctor_get_uint8(x_15, 4);
x_160 = lean_ctor_get_uint8(x_15, 5);
x_161 = lean_ctor_get_uint8(x_15, 6);
x_162 = lean_ctor_get_uint8(x_15, 7);
x_163 = lean_ctor_get_uint8(x_15, 8);
x_164 = lean_ctor_get_uint8(x_15, 10);
x_165 = lean_ctor_get_uint8(x_15, 11);
x_166 = lean_ctor_get_uint8(x_15, 12);
x_167 = lean_ctor_get_uint8(x_15, 13);
x_168 = lean_ctor_get_uint8(x_15, 14);
x_169 = lean_ctor_get_uint8(x_15, 15);
x_170 = lean_ctor_get_uint8(x_15, 16);
x_171 = lean_ctor_get_uint8(x_15, 17);
x_172 = lean_ctor_get_uint8(x_15, 18);
lean_dec(x_15);
x_173 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_174 = lean_ctor_get(x_5, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_5, 4);
lean_inc(x_177);
x_178 = lean_ctor_get(x_5, 5);
lean_inc(x_178);
x_179 = lean_ctor_get(x_5, 6);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_181 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_182 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
lean_inc_ref(x_1);
x_183 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; uint64_t x_187; lean_object* x_188; uint64_t x_189; uint64_t x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = 3;
x_186 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_186, 0, x_155);
lean_ctor_set_uint8(x_186, 1, x_156);
lean_ctor_set_uint8(x_186, 2, x_157);
lean_ctor_set_uint8(x_186, 3, x_158);
lean_ctor_set_uint8(x_186, 4, x_159);
lean_ctor_set_uint8(x_186, 5, x_160);
lean_ctor_set_uint8(x_186, 6, x_161);
lean_ctor_set_uint8(x_186, 7, x_162);
lean_ctor_set_uint8(x_186, 8, x_163);
lean_ctor_set_uint8(x_186, 9, x_185);
lean_ctor_set_uint8(x_186, 10, x_164);
lean_ctor_set_uint8(x_186, 11, x_165);
lean_ctor_set_uint8(x_186, 12, x_166);
lean_ctor_set_uint8(x_186, 13, x_167);
lean_ctor_set_uint8(x_186, 14, x_168);
lean_ctor_set_uint8(x_186, 15, x_169);
lean_ctor_set_uint8(x_186, 16, x_170);
lean_ctor_set_uint8(x_186, 17, x_171);
lean_ctor_set_uint8(x_186, 18, x_172);
x_187 = l_Lean_Meta_Context_configKey(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_188 = x_5;
} else {
 lean_dec_ref(x_5);
 x_188 = lean_box(0);
}
x_189 = 2;
x_190 = lean_uint64_shift_right(x_187, x_189);
x_191 = lean_uint64_shift_left(x_190, x_189);
x_192 = l_reduceCtorEq___closed__0;
x_193 = lean_uint64_lor(x_191, x_192);
x_194 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_194, 0, x_186);
lean_ctor_set_uint64(x_194, sizeof(void*)*1, x_193);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(0, 7, 4);
} else {
 x_195 = x_188;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_174);
lean_ctor_set(x_195, 2, x_175);
lean_ctor_set(x_195, 3, x_176);
lean_ctor_set(x_195, 4, x_177);
lean_ctor_set(x_195, 5, x_178);
lean_ctor_set(x_195, 6, x_179);
lean_ctor_set_uint8(x_195, sizeof(void*)*7, x_173);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 1, x_180);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 2, x_181);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 3, x_182);
x_196 = l_Lean_Expr_cleanupAnnotations(x_184);
x_197 = l_Lean_Expr_isApp(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_196);
lean_dec_ref(x_1);
x_198 = lean_box(0);
x_199 = l_reduceCtorEq___lam__0(x_198, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_199;
goto block_14;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_196, 1);
lean_inc_ref(x_200);
x_201 = l_Lean_Expr_appFnCleanup___redArg(x_196);
x_202 = l_Lean_Expr_isApp(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec_ref(x_1);
x_203 = lean_box(0);
x_204 = l_reduceCtorEq___lam__0(x_203, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_204;
goto block_14;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc_ref(x_205);
x_206 = l_Lean_Expr_appFnCleanup___redArg(x_201);
x_207 = l_Lean_Expr_isApp(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_200);
lean_dec_ref(x_1);
x_208 = lean_box(0);
x_209 = l_reduceCtorEq___lam__0(x_208, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_209;
goto block_14;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_Expr_appFnCleanup___redArg(x_206);
x_211 = ((lean_object*)(l_reduceCtorEq___closed__2));
x_212 = l_Lean_Expr_isConstOf(x_210, x_211);
lean_dec_ref(x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_205);
lean_dec_ref(x_200);
lean_dec_ref(x_1);
x_213 = lean_box(0);
x_214 = l_reduceCtorEq___lam__0(x_213, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = x_214;
goto block_14;
}
else
{
lean_object* x_215; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_195);
x_215 = l_Lean_Meta_constructorApp_x27_x3f(x_205, x_195, x_6, x_7, x_8);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_195);
x_217 = l_Lean_Meta_constructorApp_x27_x3f(x_200, x_195, x_6, x_7, x_8);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_obj_tag(x_216) == 1)
{
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_223 = lean_ctor_get(x_216, 0);
lean_inc(x_223);
lean_dec_ref(x_216);
x_224 = lean_ctor_get(x_218, 0);
lean_inc(x_224);
lean_dec_ref(x_218);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc_ref(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_ctor_get(x_227, 0);
lean_inc_ref(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
lean_dec_ref(x_226);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec_ref(x_228);
x_231 = lean_name_eq(x_229, x_230);
lean_dec(x_230);
lean_dec(x_229);
if (x_231 == 0)
{
if (x_212 == 0)
{
lean_dec_ref(x_195);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_222;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_219);
x_232 = lean_box(x_231);
x_233 = lean_box(x_212);
x_234 = l_reduceCtorEq___boxed__const__1;
x_235 = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 12, 3);
lean_closure_set(x_235, 0, x_232);
lean_closure_set(x_235, 1, x_233);
lean_closure_set(x_235, 2, x_234);
x_236 = ((lean_object*)(l_reduceCtorEq___closed__4));
x_237 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(x_236, x_1, x_235, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
x_10 = x_237;
goto block_14;
}
}
else
{
lean_dec_ref(x_195);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_222;
}
}
else
{
lean_object* x_238; 
lean_dec(x_219);
lean_dec_ref(x_1);
x_238 = l_reduceCtorEq___lam__1(x_216, x_218, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_218);
lean_dec_ref(x_216);
x_10 = x_238;
goto block_14;
}
}
else
{
lean_object* x_239; 
lean_dec(x_219);
lean_dec_ref(x_1);
x_239 = l_reduceCtorEq___lam__1(x_216, x_218, x_2, x_3, x_4, x_195, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_195);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_218);
lean_dec(x_216);
x_10 = x_239;
goto block_14;
}
block_222:
{
lean_object* x_220; lean_object* x_221; 
x_220 = ((lean_object*)(l_reduceIte___closed__0));
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_216);
lean_dec_ref(x_195);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_217, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_241 = x_217;
} else {
 lean_dec_ref(x_217);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec_ref(x_200);
lean_dec_ref(x_195);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_243 = lean_ctor_get(x_215, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_244 = x_215;
} else {
 lean_dec_ref(x_215);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
}
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_246 = lean_ctor_get(x_183, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_247 = x_183;
} else {
 lean_dec_ref(x_183);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
block_14:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_reduceCtorEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
x_4 = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
return x_2;
}
}
static lean_object* _init_l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
x_3 = 1;
x_4 = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_;
x_5 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
x_3 = 1;
x_4 = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_;
x_5 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
return x_2;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_ = _init_l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
lean_mark_persistent(l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
if (builtin) {res = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_reduceDIte___closed__4 = _init_l_reduceDIte___closed__4();
lean_mark_persistent(l_reduceDIte___closed__4);
l_reduceDIte___closed__9 = _init_l_reduceDIte___closed__9();
lean_mark_persistent(l_reduceDIte___closed__9);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_ = _init_l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
lean_mark_persistent(l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
if (builtin) {res = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_ = _init_l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_();
lean_mark_persistent(l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_);
if (builtin) {res = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_704010674____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_ = _init_l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_();
lean_mark_persistent(l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_);
if (builtin) {res = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1104411687____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_reduceCtorEq___lam__2___closed__2 = _init_l_reduceCtorEq___lam__2___closed__2();
lean_mark_persistent(l_reduceCtorEq___lam__2___closed__2);
l_reduceCtorEq___lam__2___closed__3 = _init_l_reduceCtorEq___lam__2___closed__3();
lean_mark_persistent(l_reduceCtorEq___lam__2___closed__3);
l_reduceCtorEq___lam__2___closed__4 = _init_l_reduceCtorEq___lam__2___closed__4();
l_reduceCtorEq___closed__0 = _init_l_reduceCtorEq___closed__0();
l_reduceCtorEq___boxed__const__1 = _init_l_reduceCtorEq___boxed__const__1();
lean_mark_persistent(l_reduceCtorEq___boxed__const__1);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_ = _init_l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
lean_mark_persistent(l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
if (builtin) {res = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
