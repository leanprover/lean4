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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_reduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_reduceIte___closed__0 = (const lean_object*)&l_reduceIte___closed__0_value;
static const lean_string_object l_reduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_reduceIte___closed__1 = (const lean_object*)&l_reduceIte___closed__1_value;
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
LEAN_EXPORT lean_object* l_reduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(1, 182, 106, 10, 77, 189, 166, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceIte___closed__2_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l_reduceDIte___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceDIte___closed__4;
static const lean_string_object l_reduceDIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l_reduceDIte___closed__5 = (const lean_object*)&l_reduceDIte___closed__5_value;
static const lean_ctor_object l_reduceDIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l_reduceDIte___closed__6 = (const lean_object*)&l_reduceDIte___closed__6_value;
static const lean_string_object l_reduceDIte___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_eq_true"};
static const lean_object* l_reduceDIte___closed__7 = (const lean_object*)&l_reduceDIte___closed__7_value;
static const lean_ctor_object l_reduceDIte___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__7_value),LEAN_SCALAR_PTR_LITERAL(180, 216, 190, 52, 49, 30, 207, 178)}};
static const lean_object* l_reduceDIte___closed__8 = (const lean_object*)&l_reduceDIte___closed__8_value;
static lean_once_cell_t l_reduceDIte___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceDIte___closed__9;
static const lean_string_object l_reduceDIte___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l_reduceDIte___closed__10 = (const lean_object*)&l_reduceDIte___closed__10_value;
static const lean_ctor_object l_reduceDIte___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__10_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l_reduceDIte___closed__11 = (const lean_object*)&l_reduceDIte___closed__11_value;
LEAN_EXPORT lean_object* l_reduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(30, 101, 22, 109, 248, 175, 82, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceDIte___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object*);
static const lean_ctor_object l_dreduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_dreduceIte___closed__0 = (const lean_object*)&l_dreduceIte___closed__0_value;
static const lean_string_object l_dreduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_dreduceIte___closed__1 = (const lean_object*)&l_dreduceIte___closed__1_value;
static const lean_string_object l_dreduceIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_dreduceIte___closed__2 = (const lean_object*)&l_dreduceIte___closed__2_value;
static const lean_ctor_object l_dreduceIte___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_dreduceIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__3_value_aux_0),((lean_object*)&l_dreduceIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_dreduceIte___closed__3 = (const lean_object*)&l_dreduceIte___closed__3_value;
static const lean_string_object l_dreduceIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_dreduceIte___closed__4 = (const lean_object*)&l_dreduceIte___closed__4_value;
static const lean_ctor_object l_dreduceIte___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_dreduceIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__5_value_aux_0),((lean_object*)&l_dreduceIte___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_dreduceIte___closed__5 = (const lean_object*)&l_dreduceIte___closed__5_value;
LEAN_EXPORT lean_object* l_dreduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dreduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(20, 216, 99, 140, 103, 209, 78, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dreduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(222, 220, 170, 50, 32, 2, 19, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_reduceCtorEq___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_reduceCtorEq___lam__2___closed__0 = (const lean_object*)&l_reduceCtorEq___lam__2___closed__0_value;
static const lean_ctor_object l_reduceCtorEq___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_reduceCtorEq___lam__2___closed__1 = (const lean_object*)&l_reduceCtorEq___lam__2___closed__1_value;
static lean_once_cell_t l_reduceCtorEq___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceCtorEq___lam__2___closed__2;
static lean_once_cell_t l_reduceCtorEq___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_reduceCtorEq___lam__2___closed__3;
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t, uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_reduceCtorEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_reduceCtorEq___closed__0;
static const lean_string_object l_reduceCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_reduceCtorEq___closed__1 = (const lean_object*)&l_reduceCtorEq___closed__1_value;
static const lean_ctor_object l_reduceCtorEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_reduceCtorEq___closed__2 = (const lean_object*)&l_reduceCtorEq___closed__2_value;
static const lean_string_object l_reduceCtorEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_reduceCtorEq___closed__3 = (const lean_object*)&l_reduceCtorEq___closed__3_value;
static const lean_ctor_object l_reduceCtorEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_reduceCtorEq___closed__4 = (const lean_object*)&l_reduceCtorEq___closed__4_value;
static const lean_ctor_object l_reduceCtorEq___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_reduceCtorEq___boxed__const__1 = (const lean_object*)&l_reduceCtorEq___boxed__const__1_value;
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
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object*);
LEAN_EXPORT lean_object* l_reduceIte(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_12_, v_a_17_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_120_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_120_ == 0)
{
v___x_24_ = v___x_21_;
v_isShared_25_ = v_isSharedCheck_120_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_120_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = l_Lean_Expr_cleanupAnnotations(v_a_22_);
v___x_32_ = l_Lean_Expr_isApp(v___x_31_);
if (v___x_32_ == 0)
{
lean_dec_ref(v___x_31_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_arg_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc_ref(v_arg_33_);
v___x_34_ = l_Lean_Expr_appFnCleanup___redArg(v___x_31_);
v___x_35_ = l_Lean_Expr_isApp(v___x_34_);
if (v___x_35_ == 0)
{
lean_dec_ref(v___x_34_);
lean_dec_ref(v_arg_33_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_arg_36_ = lean_ctor_get(v___x_34_, 1);
lean_inc_ref(v_arg_36_);
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_34_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_arg_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_arg_39_);
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_41_ = l_Lean_Expr_isApp(v___x_40_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___x_40_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_arg_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_arg_42_);
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_40_);
v___x_44_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_43_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
goto v___jp_26_;
}
else
{
lean_object* v_arg_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_arg_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc_ref(v_arg_45_);
v___x_46_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
v___x_47_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_48_ = l_Lean_Expr_isConstOf(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
goto v___jp_26_;
}
else
{
lean_object* v___x_49_; 
lean_del_object(v___x_24_);
lean_inc(v_a_19_);
lean_inc_ref(v_a_18_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_arg_42_);
v___x_49_ = lean_simp(v_arg_42_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_111_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_111_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_111_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_111_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_expr_54_; uint8_t v___x_55_; 
v_expr_54_ = lean_ctor_get(v_a_50_, 0);
lean_inc_ref(v_expr_54_);
v___x_55_ = l_Lean_Expr_isTrue(v_expr_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
lean_inc_ref(v_expr_54_);
v___x_56_ = l_Lean_Expr_isFalse(v_expr_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_59_; 
lean_dec(v_a_50_);
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
v___x_57_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_57_);
v___x_59_ = v___x_52_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
else
{
lean_object* v___x_61_; 
lean_del_object(v___x_52_);
v___x_61_ = l_Lean_Meta_Simp_Result_getProof(v_a_50_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_77_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_77_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_77_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_77_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_66_ = ((lean_object*)(l_reduceIte___closed__4));
v___x_67_ = l_Lean_Expr_constLevels_x21(v___x_46_);
lean_dec_ref(v___x_46_);
v___x_68_ = l_Lean_mkConst(v___x_66_, v___x_67_);
lean_inc_ref(v_arg_33_);
v___x_69_ = l_Lean_mkApp5(v___x_68_, v_arg_45_, v_arg_42_, v_arg_39_, v_arg_36_, v_arg_33_);
v___x_70_ = l_Lean_Expr_app___override(v___x_69_, v_a_62_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_72_, 0, v_arg_33_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2, v___x_48_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_73_);
v___x_75_ = v___x_64_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
v_a_78_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_61_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_61_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
else
{
lean_object* v___x_86_; 
lean_del_object(v___x_52_);
v___x_86_ = l_Lean_Meta_Simp_Result_getProof(v_a_50_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_102_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_102_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_102_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_102_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_91_ = ((lean_object*)(l_reduceIte___closed__6));
v___x_92_ = l_Lean_Expr_constLevels_x21(v___x_46_);
lean_dec_ref(v___x_46_);
v___x_93_ = l_Lean_mkConst(v___x_91_, v___x_92_);
lean_inc_ref(v_arg_36_);
v___x_94_ = l_Lean_mkApp5(v___x_93_, v_arg_45_, v_arg_42_, v_arg_39_, v_arg_36_, v_arg_33_);
v___x_95_ = l_Lean_Expr_app___override(v___x_94_, v_a_87_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_97_, 0, v_arg_36_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*2, v___x_48_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_98_);
v___x_100_ = v___x_89_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
v_a_103_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_86_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_86_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_33_);
v_a_112_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_49_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_49_);
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
}
}
}
}
v___jp_26_:
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_27_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_21_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_21_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_reduceIte(v_e_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_158_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_159_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_156_, v___x_157_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
return v_res_161_;
}
}
static lean_object* _init_l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_166_ = 0;
v___x_167_ = lean_obj_once(&l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_, &l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once, _init_l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
v___x_168_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_173_ = 0;
v___x_174_ = lean_obj_once(&l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_, &l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once, _init_l_reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
v___x_175_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_172_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
return v_res_177_;
}
}
static lean_object* _init_l_reduceDIte___closed__4(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_box(0);
v___x_185_ = ((lean_object*)(l_reduceDIte___closed__3));
v___x_186_ = l_Lean_mkConst(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_reduceDIte___closed__9(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_reduceDIte___closed__8));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte(lean_object* v_e_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_199_, v_a_204_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_315_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_315_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_315_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_315_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Lean_Expr_cleanupAnnotations(v_a_209_);
v___x_219_ = l_Lean_Expr_isApp(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_218_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_arg_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_arg_220_);
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_218_);
v___x_222_ = l_Lean_Expr_isApp(v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v___x_221_);
lean_dec_ref(v_arg_220_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_arg_223_ = lean_ctor_get(v___x_221_, 1);
lean_inc_ref(v_arg_223_);
v___x_224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_221_);
v___x_225_ = l_Lean_Expr_isApp(v___x_224_);
if (v___x_225_ == 0)
{
lean_dec_ref(v___x_224_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_arg_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc_ref(v_arg_226_);
v___x_227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_224_);
v___x_228_ = l_Lean_Expr_isApp(v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v___x_227_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_arg_229_ = lean_ctor_get(v___x_227_, 1);
lean_inc_ref(v_arg_229_);
v___x_230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_227_);
v___x_231_ = l_Lean_Expr_isApp(v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v___x_230_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_arg_232_ = lean_ctor_get(v___x_230_, 1);
lean_inc_ref(v_arg_232_);
v___x_233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_230_);
v___x_234_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_235_ = l_Lean_Expr_isConstOf(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
goto v___jp_213_;
}
else
{
lean_object* v___x_236_; 
lean_del_object(v___x_211_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc_ref(v_arg_229_);
v___x_236_ = lean_simp(v_arg_229_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_306_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_306_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_306_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_306_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_expr_241_; uint8_t v___x_242_; 
v_expr_241_ = lean_ctor_get(v_a_237_, 0);
lean_inc_ref(v_expr_241_);
v___x_242_ = l_Lean_Expr_isTrue(v_expr_241_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
lean_inc_ref(v_expr_241_);
v___x_243_ = l_Lean_Expr_isFalse(v_expr_241_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v_a_237_);
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
v___x_244_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_244_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v___x_248_; 
lean_del_object(v___x_239_);
v___x_248_ = l_Lean_Meta_Simp_Result_getProof(v_a_237_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_268_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_268_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_268_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_268_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_253_ = lean_obj_once(&l_reduceDIte___closed__4, &l_reduceDIte___closed__4_once, _init_l_reduceDIte___closed__4);
lean_inc(v_a_249_);
lean_inc_ref(v_arg_229_);
v___x_254_ = l_Lean_mkAppB(v___x_253_, v_arg_229_, v_a_249_);
lean_inc_ref(v_arg_220_);
v___x_255_ = l_Lean_Expr_app___override(v_arg_220_, v___x_254_);
v___x_256_ = l_Lean_Expr_headBeta(v___x_255_);
v___x_257_ = ((lean_object*)(l_reduceDIte___closed__6));
v___x_258_ = l_Lean_Expr_constLevels_x21(v___x_233_);
lean_dec_ref(v___x_233_);
v___x_259_ = l_Lean_mkConst(v___x_257_, v___x_258_);
v___x_260_ = l_Lean_mkApp5(v___x_259_, v_arg_232_, v_arg_229_, v_arg_226_, v_arg_223_, v_arg_220_);
v___x_261_ = l_Lean_Expr_app___override(v___x_260_, v_a_249_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_263_, 0, v___x_256_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*2, v___x_235_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_264_);
v___x_266_ = v___x_251_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
v_a_269_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_248_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_248_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
else
{
lean_object* v___x_277_; 
lean_del_object(v___x_239_);
v___x_277_ = l_Lean_Meta_Simp_Result_getProof(v_a_237_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_297_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_297_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_297_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_282_ = lean_obj_once(&l_reduceDIte___closed__9, &l_reduceDIte___closed__9_once, _init_l_reduceDIte___closed__9);
lean_inc(v_a_278_);
lean_inc_ref(v_arg_229_);
v___x_283_ = l_Lean_mkAppB(v___x_282_, v_arg_229_, v_a_278_);
lean_inc_ref(v_arg_223_);
v___x_284_ = l_Lean_Expr_app___override(v_arg_223_, v___x_283_);
v___x_285_ = l_Lean_Expr_headBeta(v___x_284_);
v___x_286_ = ((lean_object*)(l_reduceDIte___closed__11));
v___x_287_ = l_Lean_Expr_constLevels_x21(v___x_233_);
lean_dec_ref(v___x_233_);
v___x_288_ = l_Lean_mkConst(v___x_286_, v___x_287_);
v___x_289_ = l_Lean_mkApp5(v___x_288_, v_arg_232_, v_arg_229_, v_arg_226_, v_arg_223_, v_arg_220_);
v___x_290_ = l_Lean_Expr_app___override(v___x_289_, v_a_278_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_292_, 0, v___x_285_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*2, v___x_235_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_293_);
v___x_295_ = v___x_280_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
v_a_298_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_277_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_277_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v_arg_226_);
lean_dec_ref(v_arg_223_);
lean_dec_ref(v_arg_220_);
v_a_307_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_236_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_236_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
}
}
}
v___jp_213_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_214_);
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_208_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_208_);
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
}
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object* v_e_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_reduceDIte(v_e_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_353_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_354_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_351_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
return v_res_356_;
}
}
static lean_object* _init_l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_361_ = 0;
v___x_362_ = lean_obj_once(&l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_, &l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once, _init_l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
v___x_363_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_360_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_368_ = 0;
v___x_369_ = lean_obj_once(&l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_, &l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once, _init_l_reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
v___x_370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Simp_inDSimp___redArg(v_a_386_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_505_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_505_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_505_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_505_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; 
v___x_401_ = lean_unbox(v_a_397_);
lean_dec(v_a_397_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec_ref(v_e_384_);
v___x_402_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v___x_406_; 
lean_del_object(v___x_399_);
v___x_406_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_384_, v_a_389_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_496_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_496_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_496_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_496_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = l_Lean_Expr_cleanupAnnotations(v_a_407_);
v___x_417_ = l_Lean_Expr_isApp(v___x_416_);
if (v___x_417_ == 0)
{
lean_dec_ref(v___x_416_);
goto v___jp_411_;
}
else
{
lean_object* v_arg_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_arg_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc_ref(v_arg_418_);
v___x_419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_416_);
v___x_420_ = l_Lean_Expr_isApp(v___x_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v___x_419_);
lean_dec_ref(v_arg_418_);
goto v___jp_411_;
}
else
{
lean_object* v_arg_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_arg_421_ = lean_ctor_get(v___x_419_, 1);
lean_inc_ref(v_arg_421_);
v___x_422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_419_);
v___x_423_ = l_Lean_Expr_isApp(v___x_422_);
if (v___x_423_ == 0)
{
lean_dec_ref(v___x_422_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_411_;
}
else
{
lean_object* v_arg_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_arg_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc_ref(v_arg_424_);
v___x_425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_422_);
v___x_426_ = l_Lean_Expr_isApp(v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v___x_425_);
lean_dec_ref(v_arg_424_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_411_;
}
else
{
lean_object* v_arg_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_arg_427_ = lean_ctor_get(v___x_425_, 1);
lean_inc_ref(v_arg_427_);
v___x_428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_425_);
v___x_429_ = l_Lean_Expr_isApp(v___x_428_);
if (v___x_429_ == 0)
{
lean_dec_ref(v___x_428_);
lean_dec_ref(v_arg_427_);
lean_dec_ref(v_arg_424_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_411_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_428_);
v___x_431_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_432_ = l_Lean_Expr_isConstOf(v___x_430_, v___x_431_);
lean_dec_ref(v___x_430_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_arg_427_);
lean_dec_ref(v_arg_424_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_411_;
}
else
{
lean_object* v___x_433_; 
lean_del_object(v___x_409_);
lean_inc(v_a_391_);
lean_inc_ref(v_a_390_);
lean_inc(v_a_389_);
lean_inc_ref(v_a_388_);
lean_inc(v_a_387_);
lean_inc_ref(v_a_386_);
lean_inc(v_a_385_);
v___x_433_ = lean_simp(v_arg_427_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_487_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_487_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_487_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_487_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_expr_480_; uint8_t v___x_481_; 
v_expr_480_ = lean_ctor_get(v_a_434_, 0);
lean_inc_ref(v_expr_480_);
lean_dec(v_a_434_);
lean_inc_ref(v_expr_480_);
v___x_481_ = l_Lean_Expr_isTrue(v_expr_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
v___x_482_ = l_Lean_Expr_isFalse(v_expr_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec_ref(v_arg_424_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
v___x_483_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_483_);
v___x_485_ = v___x_436_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_del_object(v___x_436_);
goto v___jp_438_;
}
}
else
{
lean_dec_ref(v_expr_480_);
lean_del_object(v___x_436_);
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_whnfD(v_arg_424_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v___x_441_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_440_, v_a_389_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_463_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_463_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_463_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_463_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = l_Lean_Expr_cleanupAnnotations(v_a_442_);
v___x_447_ = l_Lean_Expr_isApp(v___x_446_);
if (v___x_447_ == 0)
{
lean_dec_ref(v___x_446_);
lean_del_object(v___x_444_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_393_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_446_);
v___x_449_ = l_Lean_Expr_isApp(v___x_448_);
if (v___x_449_ == 0)
{
lean_dec_ref(v___x_448_);
lean_del_object(v___x_444_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
goto v___jp_393_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_448_);
v___x_451_ = ((lean_object*)(l_dreduceIte___closed__3));
v___x_452_ = l_Lean_Expr_isConstOf(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
lean_dec_ref(v_arg_418_);
v___x_453_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_454_ = l_Lean_Expr_isConstOf(v___x_450_, v___x_453_);
lean_dec_ref(v___x_450_);
if (v___x_454_ == 0)
{
lean_del_object(v___x_444_);
lean_dec_ref(v_arg_421_);
goto v___jp_393_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_arg_421_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_455_);
v___x_457_ = v___x_444_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec_ref(v___x_450_);
lean_dec_ref(v_arg_421_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_arg_418_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_459_);
v___x_461_ = v___x_444_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
v_a_464_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_441_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_441_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
v_a_472_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_439_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_439_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_arg_424_);
lean_dec_ref(v_arg_421_);
lean_dec_ref(v_arg_418_);
v_a_488_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_433_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_433_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
}
}
}
v___jp_411_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_406_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_406_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_e_384_);
v_a_506_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_396_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_396_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
v___jp_393_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* v_e_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_dreduceIte(v_e_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_530_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_531_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_528_, v___x_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15____boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
return v_res_533_;
}
}
static lean_object* _init_l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_538_ = 0;
v___x_539_ = lean_obj_once(&l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_, &l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once, _init_l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
v___x_540_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_537_, v___x_538_, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_545_ = 0;
v___x_546_ = lean_obj_once(&l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_, &l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once, _init_l_dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
v___x_547_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_544_, v___x_545_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object* v_e_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Simp_inDSimp___redArg(v_a_552_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_676_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_676_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_676_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_676_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = lean_unbox(v_a_563_);
lean_dec(v_a_563_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec_ref(v_e_550_);
v___x_568_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_572_; 
lean_del_object(v___x_565_);
v___x_572_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_550_, v_a_555_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_667_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_667_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_667_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_667_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = l_Lean_Expr_cleanupAnnotations(v_a_573_);
v___x_583_ = l_Lean_Expr_isApp(v___x_582_);
if (v___x_583_ == 0)
{
lean_dec_ref(v___x_582_);
goto v___jp_577_;
}
else
{
lean_object* v_arg_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_arg_584_ = lean_ctor_get(v___x_582_, 1);
lean_inc_ref(v_arg_584_);
v___x_585_ = l_Lean_Expr_appFnCleanup___redArg(v___x_582_);
v___x_586_ = l_Lean_Expr_isApp(v___x_585_);
if (v___x_586_ == 0)
{
lean_dec_ref(v___x_585_);
lean_dec_ref(v_arg_584_);
goto v___jp_577_;
}
else
{
lean_object* v_arg_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_arg_587_ = lean_ctor_get(v___x_585_, 1);
lean_inc_ref(v_arg_587_);
v___x_588_ = l_Lean_Expr_appFnCleanup___redArg(v___x_585_);
v___x_589_ = l_Lean_Expr_isApp(v___x_588_);
if (v___x_589_ == 0)
{
lean_dec_ref(v___x_588_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_577_;
}
else
{
lean_object* v_arg_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_arg_590_ = lean_ctor_get(v___x_588_, 1);
lean_inc_ref(v_arg_590_);
v___x_591_ = l_Lean_Expr_appFnCleanup___redArg(v___x_588_);
v___x_592_ = l_Lean_Expr_isApp(v___x_591_);
if (v___x_592_ == 0)
{
lean_dec_ref(v___x_591_);
lean_dec_ref(v_arg_590_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_577_;
}
else
{
lean_object* v_arg_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_arg_593_ = lean_ctor_get(v___x_591_, 1);
lean_inc_ref(v_arg_593_);
v___x_594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_591_);
v___x_595_ = l_Lean_Expr_isApp(v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v___x_594_);
lean_dec_ref(v_arg_593_);
lean_dec_ref(v_arg_590_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_577_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = l_Lean_Expr_appFnCleanup___redArg(v___x_594_);
v___x_597_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_598_ = l_Lean_Expr_isConstOf(v___x_596_, v___x_597_);
lean_dec_ref(v___x_596_);
if (v___x_598_ == 0)
{
lean_dec_ref(v_arg_593_);
lean_dec_ref(v_arg_590_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_577_;
}
else
{
lean_object* v___x_599_; 
lean_del_object(v___x_575_);
lean_inc(v_a_557_);
lean_inc_ref(v_a_556_);
lean_inc(v_a_555_);
lean_inc_ref(v_a_554_);
lean_inc(v_a_553_);
lean_inc_ref(v_a_552_);
lean_inc(v_a_551_);
v___x_599_ = lean_simp(v_arg_593_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_658_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_658_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_658_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_658_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_expr_651_; uint8_t v___x_652_; 
v_expr_651_ = lean_ctor_get(v_a_600_, 0);
lean_inc_ref(v_expr_651_);
lean_dec(v_a_600_);
lean_inc_ref(v_expr_651_);
v___x_652_ = l_Lean_Expr_isTrue(v_expr_651_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = l_Lean_Expr_isFalse(v_expr_651_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_dec_ref(v_arg_590_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
v___x_654_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_654_);
v___x_656_ = v___x_602_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_del_object(v___x_602_);
goto v___jp_604_;
}
}
else
{
lean_dec_ref(v_expr_651_);
lean_del_object(v___x_602_);
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_whnfD(v_arg_590_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref(v___x_605_);
v___x_607_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_606_, v_a_555_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_634_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_634_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_634_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_634_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_Lean_Expr_cleanupAnnotations(v_a_608_);
v___x_613_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v___x_612_);
lean_del_object(v___x_610_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_559_;
}
else
{
lean_object* v_arg_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_arg_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc_ref(v_arg_614_);
v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
v___x_616_ = l_Lean_Expr_isApp(v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_615_);
lean_dec_ref(v_arg_614_);
lean_del_object(v___x_610_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
goto v___jp_559_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_615_);
v___x_618_ = ((lean_object*)(l_dreduceIte___closed__3));
v___x_619_ = l_Lean_Expr_isConstOf(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
lean_dec_ref(v_arg_584_);
v___x_620_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_621_ = l_Lean_Expr_isConstOf(v___x_617_, v___x_620_);
lean_dec_ref(v___x_617_);
if (v___x_621_ == 0)
{
lean_dec_ref(v_arg_614_);
lean_del_object(v___x_610_);
lean_dec_ref(v_arg_587_);
goto v___jp_559_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_622_ = l_Lean_Expr_app___override(v_arg_587_, v_arg_614_);
v___x_623_ = l_Lean_Expr_headBeta(v___x_622_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_624_);
v___x_626_ = v___x_610_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec_ref(v___x_617_);
lean_dec_ref(v_arg_587_);
v___x_628_ = l_Lean_Expr_app___override(v_arg_584_, v_arg_614_);
v___x_629_ = l_Lean_Expr_headBeta(v___x_628_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_630_);
v___x_632_ = v___x_610_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
v_a_635_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_607_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_607_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
v_a_643_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_605_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_605_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_arg_590_);
lean_dec_ref(v_arg_587_);
lean_dec_ref(v_arg_584_);
v_a_659_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_599_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_599_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
}
}
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_572_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_572_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_e_550_);
v_a_677_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_562_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_562_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
v___jp_559_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_dreduceDIte(v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_701_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_702_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_699_, v___x_700_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
return v_res_704_;
}
}
static lean_object* _init_l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_709_ = 0;
v___x_710_ = lean_obj_once(&l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_, &l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once, _init_l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
v___x_711_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_716_ = 0;
v___x_717_ = lean_obj_once(&l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_, &l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once, _init_l_dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
v___x_718_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object* v_x_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_reduceCtorEq___lam__0(v_x_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_reduceCtorEq___lam__1(v_x_754_, v_x_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v_x_755_);
lean_dec(v_x_754_);
return v_res_764_;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_box(0);
v___x_769_ = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
v___x_770_ = l_Lean_mkConst(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static uint64_t _init_l_reduceCtorEq___lam__2___closed__3(void){
_start:
{
uint8_t v___x_771_; uint64_t v___x_772_; 
v___x_771_ = 1;
v___x_772_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t v___x_773_, uint8_t v___x_774_, uint64_t v___x_775_, lean_object* v_h_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_a_787_; lean_object* v___x_792_; 
v___x_785_ = lean_obj_once(&l_reduceCtorEq___lam__2___closed__2, &l_reduceCtorEq___lam__2___closed__2_once, _init_l_reduceCtorEq___lam__2___closed__2);
lean_inc_ref(v_h_776_);
v___x_792_ = l_Lean_Meta_mkNoConfusion(v___x_785_, v_h_776_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_792_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_mk_empty_array_with_capacity(v___x_794_);
v___x_796_ = lean_array_push(v___x_795_, v_h_776_);
v___x_797_ = 1;
v___x_798_ = l_Lean_Meta_mkLambdaFVars(v___x_796_, v_a_793_, v___x_773_, v___x_774_, v___x_773_, v___x_774_, v___x_797_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___x_796_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; uint8_t v_foApprox_801_; uint8_t v_ctxApprox_802_; uint8_t v_quasiPatternApprox_803_; uint8_t v_constApprox_804_; uint8_t v_isDefEqStuckEx_805_; uint8_t v_unificationHints_806_; uint8_t v_proofIrrelevance_807_; uint8_t v_assignSyntheticOpaque_808_; uint8_t v_offsetCnstrs_809_; uint8_t v_etaStruct_810_; uint8_t v_univApprox_811_; uint8_t v_iota_812_; uint8_t v_beta_813_; uint8_t v_proj_814_; uint8_t v_zeta_815_; uint8_t v_zetaDelta_816_; uint8_t v_zetaUnused_817_; uint8_t v_zetaHave_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_854_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Lean_Meta_Context_config(v___y_780_);
v_foApprox_801_ = lean_ctor_get_uint8(v___x_800_, 0);
v_ctxApprox_802_ = lean_ctor_get_uint8(v___x_800_, 1);
v_quasiPatternApprox_803_ = lean_ctor_get_uint8(v___x_800_, 2);
v_constApprox_804_ = lean_ctor_get_uint8(v___x_800_, 3);
v_isDefEqStuckEx_805_ = lean_ctor_get_uint8(v___x_800_, 4);
v_unificationHints_806_ = lean_ctor_get_uint8(v___x_800_, 5);
v_proofIrrelevance_807_ = lean_ctor_get_uint8(v___x_800_, 6);
v_assignSyntheticOpaque_808_ = lean_ctor_get_uint8(v___x_800_, 7);
v_offsetCnstrs_809_ = lean_ctor_get_uint8(v___x_800_, 8);
v_etaStruct_810_ = lean_ctor_get_uint8(v___x_800_, 10);
v_univApprox_811_ = lean_ctor_get_uint8(v___x_800_, 11);
v_iota_812_ = lean_ctor_get_uint8(v___x_800_, 12);
v_beta_813_ = lean_ctor_get_uint8(v___x_800_, 13);
v_proj_814_ = lean_ctor_get_uint8(v___x_800_, 14);
v_zeta_815_ = lean_ctor_get_uint8(v___x_800_, 15);
v_zetaDelta_816_ = lean_ctor_get_uint8(v___x_800_, 16);
v_zetaUnused_817_ = lean_ctor_get_uint8(v___x_800_, 17);
v_zetaHave_818_ = lean_ctor_get_uint8(v___x_800_, 18);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_854_ == 0)
{
v___x_820_ = v___x_800_;
v_isShared_821_ = v_isSharedCheck_854_;
goto v_resetjp_819_;
}
else
{
lean_dec(v___x_800_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_854_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v_trackZetaDelta_822_; lean_object* v_zetaDeltaSet_823_; lean_object* v_lctx_824_; lean_object* v_localInstances_825_; lean_object* v_defEqCtx_x3f_826_; lean_object* v_synthPendingDepth_827_; lean_object* v_canUnfold_x3f_828_; uint8_t v_univApprox_829_; uint8_t v_inTypeClassResolution_830_; uint8_t v_cacheInferType_831_; uint8_t v___x_832_; lean_object* v_config_834_; 
v_trackZetaDelta_822_ = lean_ctor_get_uint8(v___y_780_, sizeof(void*)*7);
v_zetaDeltaSet_823_ = lean_ctor_get(v___y_780_, 1);
v_lctx_824_ = lean_ctor_get(v___y_780_, 2);
v_localInstances_825_ = lean_ctor_get(v___y_780_, 3);
v_defEqCtx_x3f_826_ = lean_ctor_get(v___y_780_, 4);
v_synthPendingDepth_827_ = lean_ctor_get(v___y_780_, 5);
v_canUnfold_x3f_828_ = lean_ctor_get(v___y_780_, 6);
v_univApprox_829_ = lean_ctor_get_uint8(v___y_780_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_830_ = lean_ctor_get_uint8(v___y_780_, sizeof(void*)*7 + 2);
v_cacheInferType_831_ = lean_ctor_get_uint8(v___y_780_, sizeof(void*)*7 + 3);
v___x_832_ = 1;
if (v_isShared_821_ == 0)
{
v_config_834_ = v___x_820_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 0, v_foApprox_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 1, v_ctxApprox_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 2, v_quasiPatternApprox_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 3, v_constApprox_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 4, v_isDefEqStuckEx_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 5, v_unificationHints_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 6, v_proofIrrelevance_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 7, v_assignSyntheticOpaque_808_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 8, v_offsetCnstrs_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 10, v_etaStruct_810_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 11, v_univApprox_811_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 12, v_iota_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 13, v_beta_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 14, v_proj_814_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 15, v_zeta_815_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 16, v_zetaDelta_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 17, v_zetaUnused_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, 18, v_zetaHave_818_);
v_config_834_ = v_reuseFailAlloc_853_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; uint64_t v_key_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_ctor_set_uint8(v_config_834_, 9, v___x_832_);
v___x_835_ = l_Lean_Meta_Context_configKey(v___y_780_);
v___x_836_ = lean_uint64_shift_right(v___x_835_, v___x_775_);
v___x_837_ = lean_uint64_shift_left(v___x_836_, v___x_775_);
v___x_838_ = lean_uint64_once(&l_reduceCtorEq___lam__2___closed__3, &l_reduceCtorEq___lam__2___closed__3_once, _init_l_reduceCtorEq___lam__2___closed__3);
v_key_839_ = lean_uint64_lor(v___x_837_, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_840_, 0, v_config_834_);
lean_ctor_set_uint64(v___x_840_, sizeof(void*)*1, v_key_839_);
lean_inc(v_canUnfold_x3f_828_);
lean_inc(v_synthPendingDepth_827_);
lean_inc(v_defEqCtx_x3f_826_);
lean_inc_ref(v_localInstances_825_);
lean_inc_ref(v_lctx_824_);
lean_inc(v_zetaDeltaSet_823_);
v___x_841_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_zetaDeltaSet_823_);
lean_ctor_set(v___x_841_, 2, v_lctx_824_);
lean_ctor_set(v___x_841_, 3, v_localInstances_825_);
lean_ctor_set(v___x_841_, 4, v_defEqCtx_x3f_826_);
lean_ctor_set(v___x_841_, 5, v_synthPendingDepth_827_);
lean_ctor_set(v___x_841_, 6, v_canUnfold_x3f_828_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7, v_trackZetaDelta_822_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 1, v_univApprox_829_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 2, v_inTypeClassResolution_830_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 3, v_cacheInferType_831_);
v___x_842_ = l_Lean_Meta_mkEqFalse_x27(v_a_799_, v___x_841_, v___y_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v___x_842_);
v_a_787_ = v_a_843_;
goto v___jp_786_;
}
else
{
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_842_);
v_a_787_ = v_a_844_;
goto v___jp_786_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_842_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_842_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_798_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_798_);
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
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v_h_776_);
v_a_863_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_792_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_792_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_a_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_789_, 0, v___x_785_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*2, v___x_774_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_h_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_26663__boxed_883_; uint8_t v___x_26664__boxed_884_; uint64_t v___x_26665__boxed_885_; lean_object* v_res_886_; 
v___x_26663__boxed_883_ = lean_unbox(v___x_871_);
v___x_26664__boxed_884_ = lean_unbox(v___x_872_);
v___x_26665__boxed_885_ = lean_unbox_uint64(v___x_873_);
lean_dec_ref(v___x_873_);
v_res_886_ = l_reduceCtorEq___lam__2(v___x_26663__boxed_883_, v___x_26664__boxed_884_, v___x_26665__boxed_885_, v_h_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
v___x_897_ = lean_apply_9(v_k_887_, v_b_891_, v___y_888_, v___y_889_, v___y_890_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, lean_box(0));
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_898_, v___y_899_, v___y_900_, v___y_901_, v_b_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_909_, uint8_t v_bi_910_, lean_object* v_type_911_, lean_object* v_k_912_, uint8_t v_kind_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___f_922_; lean_object* v___x_923_; 
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_922_, 0, v_k_912_);
lean_closure_set(v___f_922_, 1, v___y_914_);
lean_closure_set(v___f_922_, 2, v___y_915_);
lean_closure_set(v___f_922_, 3, v___y_916_);
v___x_923_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_909_, v_bi_910_, v_type_911_, v___f_922_, v_kind_913_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_923_) == 0)
{
return v___x_923_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_932_, lean_object* v_bi_933_, lean_object* v_type_934_, lean_object* v_k_935_, lean_object* v_kind_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v_bi_boxed_945_; uint8_t v_kind_boxed_946_; lean_object* v_res_947_; 
v_bi_boxed_945_ = lean_unbox(v_bi_933_);
v_kind_boxed_946_ = lean_unbox(v_kind_936_);
v_res_947_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_932_, v_bi_boxed_945_, v_type_934_, v_k_935_, v_kind_boxed_946_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* v_name_948_, lean_object* v_type_949_, lean_object* v_k_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = 0;
v___x_960_ = 0;
v___x_961_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_948_, v___x_959_, v_type_949_, v_k_950_, v___x_960_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_962_, lean_object* v_type_963_, lean_object* v_k_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_962_, v_type_963_, v_k_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
return v_res_973_;
}
}
static uint64_t _init_l_reduceCtorEq___closed__0(void){
_start:
{
uint8_t v___x_974_; uint64_t v___x_975_; 
v___x_974_ = 3;
v___x_975_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___y_994_; lean_object* v___x_1003_; uint8_t v_foApprox_1004_; uint8_t v_ctxApprox_1005_; uint8_t v_quasiPatternApprox_1006_; uint8_t v_constApprox_1007_; uint8_t v_isDefEqStuckEx_1008_; uint8_t v_unificationHints_1009_; uint8_t v_proofIrrelevance_1010_; uint8_t v_assignSyntheticOpaque_1011_; uint8_t v_offsetCnstrs_1012_; uint8_t v_etaStruct_1013_; uint8_t v_univApprox_1014_; uint8_t v_iota_1015_; uint8_t v_beta_1016_; uint8_t v_proj_1017_; uint8_t v_zeta_1018_; uint8_t v_zetaDelta_1019_; uint8_t v_zetaUnused_1020_; uint8_t v_zetaHave_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1122_; 
v___x_1003_ = l_Lean_Meta_Context_config(v_a_988_);
v_foApprox_1004_ = lean_ctor_get_uint8(v___x_1003_, 0);
v_ctxApprox_1005_ = lean_ctor_get_uint8(v___x_1003_, 1);
v_quasiPatternApprox_1006_ = lean_ctor_get_uint8(v___x_1003_, 2);
v_constApprox_1007_ = lean_ctor_get_uint8(v___x_1003_, 3);
v_isDefEqStuckEx_1008_ = lean_ctor_get_uint8(v___x_1003_, 4);
v_unificationHints_1009_ = lean_ctor_get_uint8(v___x_1003_, 5);
v_proofIrrelevance_1010_ = lean_ctor_get_uint8(v___x_1003_, 6);
v_assignSyntheticOpaque_1011_ = lean_ctor_get_uint8(v___x_1003_, 7);
v_offsetCnstrs_1012_ = lean_ctor_get_uint8(v___x_1003_, 8);
v_etaStruct_1013_ = lean_ctor_get_uint8(v___x_1003_, 10);
v_univApprox_1014_ = lean_ctor_get_uint8(v___x_1003_, 11);
v_iota_1015_ = lean_ctor_get_uint8(v___x_1003_, 12);
v_beta_1016_ = lean_ctor_get_uint8(v___x_1003_, 13);
v_proj_1017_ = lean_ctor_get_uint8(v___x_1003_, 14);
v_zeta_1018_ = lean_ctor_get_uint8(v___x_1003_, 15);
v_zetaDelta_1019_ = lean_ctor_get_uint8(v___x_1003_, 16);
v_zetaUnused_1020_ = lean_ctor_get_uint8(v___x_1003_, 17);
v_zetaHave_1021_ = lean_ctor_get_uint8(v___x_1003_, 18);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1023_ = v___x_1003_;
v_isShared_1024_ = v_isSharedCheck_1122_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v___x_1003_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1122_;
goto v_resetjp_1022_;
}
v___jp_993_:
{
if (lean_obj_tag(v___y_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_a_995_ = lean_ctor_get(v___y_994_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___y_994_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___y_994_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___y_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
return v___y_994_;
}
}
v_resetjp_1022_:
{
uint8_t v_trackZetaDelta_1025_; lean_object* v_zetaDeltaSet_1026_; lean_object* v_lctx_1027_; lean_object* v_localInstances_1028_; lean_object* v_defEqCtx_x3f_1029_; lean_object* v_synthPendingDepth_1030_; lean_object* v_canUnfold_x3f_1031_; uint8_t v_univApprox_1032_; uint8_t v_inTypeClassResolution_1033_; uint8_t v_cacheInferType_1034_; lean_object* v___x_1035_; 
v_trackZetaDelta_1025_ = lean_ctor_get_uint8(v_a_988_, sizeof(void*)*7);
v_zetaDeltaSet_1026_ = lean_ctor_get(v_a_988_, 1);
v_lctx_1027_ = lean_ctor_get(v_a_988_, 2);
v_localInstances_1028_ = lean_ctor_get(v_a_988_, 3);
v_defEqCtx_x3f_1029_ = lean_ctor_get(v_a_988_, 4);
v_synthPendingDepth_1030_ = lean_ctor_get(v_a_988_, 5);
v_canUnfold_x3f_1031_ = lean_ctor_get(v_a_988_, 6);
v_univApprox_1032_ = lean_ctor_get_uint8(v_a_988_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1033_ = lean_ctor_get_uint8(v_a_988_, sizeof(void*)*7 + 2);
v_cacheInferType_1034_ = lean_ctor_get_uint8(v_a_988_, sizeof(void*)*7 + 3);
lean_inc_ref(v_e_984_);
v___x_1035_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_984_, v_a_989_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; uint8_t v___x_1037_; lean_object* v_config_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = 3;
if (v_isShared_1024_ == 0)
{
v_config_1039_ = v___x_1023_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 0, v_foApprox_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 1, v_ctxApprox_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 2, v_quasiPatternApprox_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 3, v_constApprox_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 4, v_isDefEqStuckEx_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 5, v_unificationHints_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 6, v_proofIrrelevance_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 7, v_assignSyntheticOpaque_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 8, v_offsetCnstrs_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 10, v_etaStruct_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 11, v_univApprox_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 12, v_iota_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 13, v_beta_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 14, v_proj_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 15, v_zeta_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 16, v_zetaDelta_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 17, v_zetaUnused_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, 18, v_zetaHave_1021_);
v_config_1039_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; uint64_t v_key_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
lean_ctor_set_uint8(v_config_1039_, 9, v___x_1037_);
v___x_1040_ = l_Lean_Meta_Context_configKey(v_a_988_);
v___x_1041_ = 2ULL;
v___x_1042_ = lean_uint64_shift_right(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_uint64_shift_left(v___x_1042_, v___x_1041_);
v___x_1044_ = lean_uint64_once(&l_reduceCtorEq___closed__0, &l_reduceCtorEq___closed__0_once, _init_l_reduceCtorEq___closed__0);
v_key_1045_ = lean_uint64_lor(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1046_, 0, v_config_1039_);
lean_ctor_set_uint64(v___x_1046_, sizeof(void*)*1, v_key_1045_);
lean_inc(v_canUnfold_x3f_1031_);
lean_inc(v_synthPendingDepth_1030_);
lean_inc(v_defEqCtx_x3f_1029_);
lean_inc_ref(v_localInstances_1028_);
lean_inc_ref(v_lctx_1027_);
lean_inc(v_zetaDeltaSet_1026_);
v___x_1047_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_zetaDeltaSet_1026_);
lean_ctor_set(v___x_1047_, 2, v_lctx_1027_);
lean_ctor_set(v___x_1047_, 3, v_localInstances_1028_);
lean_ctor_set(v___x_1047_, 4, v_defEqCtx_x3f_1029_);
lean_ctor_set(v___x_1047_, 5, v_synthPendingDepth_1030_);
lean_ctor_set(v___x_1047_, 6, v_canUnfold_x3f_1031_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*7, v_trackZetaDelta_1025_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*7 + 1, v_univApprox_1032_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1033_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*7 + 3, v_cacheInferType_1034_);
v___x_1048_ = l_Lean_Expr_cleanupAnnotations(v_a_1036_);
v___x_1049_ = l_Lean_Expr_isApp(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_e_984_);
v___x_1050_ = lean_box(0);
v___x_1051_ = l_reduceCtorEq___lam__0(v___x_1050_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
v___y_994_ = v___x_1051_;
goto v___jp_993_;
}
else
{
lean_object* v_arg_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_arg_1052_ = lean_ctor_get(v___x_1048_, 1);
lean_inc_ref(v_arg_1052_);
v___x_1053_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1048_);
v___x_1054_ = l_Lean_Expr_isApp(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref(v___x_1053_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_e_984_);
v___x_1055_ = lean_box(0);
v___x_1056_ = l_reduceCtorEq___lam__0(v___x_1055_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
v___y_994_ = v___x_1056_;
goto v___jp_993_;
}
else
{
lean_object* v_arg_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_arg_1057_ = lean_ctor_get(v___x_1053_, 1);
lean_inc_ref(v_arg_1057_);
v___x_1058_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1053_);
v___x_1059_ = l_Lean_Expr_isApp(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_e_984_);
v___x_1060_ = lean_box(0);
v___x_1061_ = l_reduceCtorEq___lam__0(v___x_1060_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
v___y_994_ = v___x_1061_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1058_);
v___x_1063_ = ((lean_object*)(l_reduceCtorEq___closed__2));
v___x_1064_ = l_Lean_Expr_isConstOf(v___x_1062_, v___x_1063_);
lean_dec_ref(v___x_1062_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_e_984_);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_reduceCtorEq___lam__0(v___x_1065_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
v___y_994_ = v___x_1066_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1057_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1052_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1096_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1096_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1096_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
if (lean_obj_tag(v_a_1068_) == 1)
{
if (lean_obj_tag(v_a_1070_) == 1)
{
lean_object* v_val_1079_; lean_object* v_val_1080_; lean_object* v_fst_1081_; lean_object* v_toConstantVal_1082_; lean_object* v_fst_1083_; lean_object* v_toConstantVal_1084_; lean_object* v_name_1085_; lean_object* v_name_1086_; uint8_t v___x_1087_; 
v_val_1079_ = lean_ctor_get(v_a_1068_, 0);
lean_inc(v_val_1079_);
lean_dec_ref(v_a_1068_);
v_val_1080_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v_a_1070_);
v_fst_1081_ = lean_ctor_get(v_val_1079_, 0);
lean_inc(v_fst_1081_);
lean_dec(v_val_1079_);
v_toConstantVal_1082_ = lean_ctor_get(v_fst_1081_, 0);
lean_inc_ref(v_toConstantVal_1082_);
lean_dec(v_fst_1081_);
v_fst_1083_ = lean_ctor_get(v_val_1080_, 0);
lean_inc(v_fst_1083_);
lean_dec(v_val_1080_);
v_toConstantVal_1084_ = lean_ctor_get(v_fst_1083_, 0);
lean_inc_ref(v_toConstantVal_1084_);
lean_dec(v_fst_1083_);
v_name_1085_ = lean_ctor_get(v_toConstantVal_1082_, 0);
lean_inc(v_name_1085_);
lean_dec_ref(v_toConstantVal_1082_);
v_name_1086_ = lean_ctor_get(v_toConstantVal_1084_, 0);
lean_inc(v_name_1086_);
lean_dec_ref(v_toConstantVal_1084_);
v___x_1087_ = lean_name_eq(v_name_1085_, v_name_1086_);
lean_dec(v_name_1086_);
lean_dec(v_name_1085_);
if (v___x_1087_ == 0)
{
if (v___x_1064_ == 0)
{
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_984_);
goto v___jp_1074_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1072_);
v___x_1088_ = lean_box(v___x_1087_);
v___x_1089_ = lean_box(v___x_1064_);
v___x_1090_ = ((lean_object*)(l_reduceCtorEq___boxed__const__1));
v___f_1091_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1091_, 0, v___x_1088_);
lean_closure_set(v___f_1091_, 1, v___x_1089_);
lean_closure_set(v___f_1091_, 2, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_reduceCtorEq___closed__4));
v___x_1093_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1092_, v_e_984_, v___f_1091_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
v___y_994_ = v___x_1093_;
goto v___jp_993_;
}
}
else
{
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_984_);
goto v___jp_1074_;
}
}
else
{
lean_object* v___x_1094_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_e_984_);
v___x_1094_ = l_reduceCtorEq___lam__1(v_a_1068_, v_a_1070_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1068_);
v___y_994_ = v___x_1094_;
goto v___jp_993_;
}
}
else
{
lean_object* v___x_1095_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_e_984_);
v___x_1095_ = l_reduceCtorEq___lam__1(v_a_1068_, v_a_1070_, v_a_985_, v_a_986_, v_a_987_, v___x_1047_, v_a_989_, v_a_990_, v_a_991_);
lean_dec_ref(v___x_1047_);
lean_dec(v_a_1070_);
lean_dec(v_a_1068_);
v___y_994_ = v___x_1095_;
goto v___jp_993_;
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_1068_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_984_);
v_a_1097_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1069_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1069_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_984_);
v_a_1105_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1067_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1067_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
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
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1023_);
lean_dec_ref(v_e_984_);
v_a_1114_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1035_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1035_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* v_e_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_reduceCtorEq(v_e_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_1133_, lean_object* v_name_1134_, uint8_t v_bi_1135_, lean_object* v_type_1136_, lean_object* v_k_1137_, uint8_t v_kind_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_1134_, v_bi_1135_, v_type_1136_, v_k_1137_, v_kind_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_name_1149_, lean_object* v_bi_1150_, lean_object* v_type_1151_, lean_object* v_k_1152_, lean_object* v_kind_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v_bi_boxed_1162_; uint8_t v_kind_boxed_1163_; lean_object* v_res_1164_; 
v_bi_boxed_1162_ = lean_unbox(v_bi_1150_);
v_kind_boxed_1163_ = lean_unbox(v_kind_1153_);
v_res_1164_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_1148_, v_name_1149_, v_bi_boxed_1162_, v_type_1151_, v_k_1152_, v_kind_boxed_1163_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* v_00_u03b1_1165_, lean_object* v_name_1166_, lean_object* v_type_1167_, lean_object* v_k_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_1166_, v_type_1167_, v_k_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_name_1179_, lean_object* v_type_1180_, lean_object* v_k_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(v_00_u03b1_1178_, v_name_1179_, v_type_1180_, v_k_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1208_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1209_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1206_, v___x_1207_, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
return v_res_1211_;
}
}
static lean_object* _init_l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1216_ = 1;
v___x_1217_ = lean_obj_once(&l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_, &l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once, _init_l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
v___x_1218_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1215_, v___x_1216_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1223_ = 1;
v___x_1224_ = lean_obj_once(&l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_, &l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once, _init_l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
v___x_1225_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1222_, v___x_1223_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
return v_res_1227_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
}
#ifdef __cplusplus
}
#endif
