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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dreduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(222, 220, 170, 50, 32, 2, 19, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_reduceCtorEq___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_166_ = 0;
v___x_167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
v___x_168_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_173_ = 0;
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
v___x_175_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_172_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_361_ = 0;
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
v___x_363_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_360_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_368_ = 0;
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
v___x_370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_inDSimp_396_; 
v_inDSimp_396_ = lean_ctor_get_uint8(v_a_386_, sizeof(void*)*10 + 8);
if (v_inDSimp_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_e_384_);
v___x_397_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_384_, v_a_389_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_489_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_489_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_489_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_489_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = l_Lean_Expr_cleanupAnnotations(v_a_400_);
v___x_410_ = l_Lean_Expr_isApp(v___x_409_);
if (v___x_410_ == 0)
{
lean_dec_ref(v___x_409_);
goto v___jp_404_;
}
else
{
lean_object* v_arg_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_arg_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc_ref(v_arg_411_);
v___x_412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_409_);
v___x_413_ = l_Lean_Expr_isApp(v___x_412_);
if (v___x_413_ == 0)
{
lean_dec_ref(v___x_412_);
lean_dec_ref(v_arg_411_);
goto v___jp_404_;
}
else
{
lean_object* v_arg_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_arg_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc_ref(v_arg_414_);
v___x_415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_412_);
v___x_416_ = l_Lean_Expr_isApp(v___x_415_);
if (v___x_416_ == 0)
{
lean_dec_ref(v___x_415_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_404_;
}
else
{
lean_object* v_arg_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_arg_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc_ref(v_arg_417_);
v___x_418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_415_);
v___x_419_ = l_Lean_Expr_isApp(v___x_418_);
if (v___x_419_ == 0)
{
lean_dec_ref(v___x_418_);
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_404_;
}
else
{
lean_object* v_arg_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_arg_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc_ref(v_arg_420_);
v___x_421_ = l_Lean_Expr_appFnCleanup___redArg(v___x_418_);
v___x_422_ = l_Lean_Expr_isApp(v___x_421_);
if (v___x_422_ == 0)
{
lean_dec_ref(v___x_421_);
lean_dec_ref(v_arg_420_);
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_404_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_421_);
v___x_424_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_425_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_424_);
lean_dec_ref(v___x_423_);
if (v___x_425_ == 0)
{
lean_dec_ref(v_arg_420_);
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_404_;
}
else
{
lean_object* v___x_426_; 
lean_del_object(v___x_402_);
lean_inc(v_a_391_);
lean_inc_ref(v_a_390_);
lean_inc(v_a_389_);
lean_inc_ref(v_a_388_);
lean_inc(v_a_387_);
lean_inc_ref(v_a_386_);
lean_inc(v_a_385_);
v___x_426_ = lean_simp(v_arg_420_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_480_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_480_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_480_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_480_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_expr_473_; uint8_t v___x_474_; 
v_expr_473_ = lean_ctor_get(v_a_427_, 0);
lean_inc_ref_n(v_expr_473_, 2);
lean_dec(v_a_427_);
v___x_474_ = l_Lean_Expr_isTrue(v_expr_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_Expr_isFalse(v_expr_473_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v___x_476_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_476_);
v___x_478_ = v___x_429_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_del_object(v___x_429_);
goto v___jp_431_;
}
}
else
{
lean_dec_ref(v_expr_473_);
lean_del_object(v___x_429_);
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_whnfD(v_arg_417_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_433_, v_a_389_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_456_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_456_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_456_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_456_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = l_Lean_Expr_cleanupAnnotations(v_a_435_);
v___x_440_ = l_Lean_Expr_isApp(v___x_439_);
if (v___x_440_ == 0)
{
lean_dec_ref(v___x_439_);
lean_del_object(v___x_437_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_393_;
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = l_Lean_Expr_appFnCleanup___redArg(v___x_439_);
v___x_442_ = l_Lean_Expr_isApp(v___x_441_);
if (v___x_442_ == 0)
{
lean_dec_ref(v___x_441_);
lean_del_object(v___x_437_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
goto v___jp_393_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_441_);
v___x_444_ = ((lean_object*)(l_dreduceIte___closed__3));
v___x_445_ = l_Lean_Expr_isConstOf(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
lean_dec_ref(v_arg_411_);
v___x_446_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_447_ = l_Lean_Expr_isConstOf(v___x_443_, v___x_446_);
lean_dec_ref(v___x_443_);
if (v___x_447_ == 0)
{
lean_del_object(v___x_437_);
lean_dec_ref(v_arg_414_);
goto v___jp_393_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_arg_414_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_448_);
v___x_450_ = v___x_437_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref(v___x_443_);
lean_dec_ref(v_arg_414_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_arg_411_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_452_);
v___x_454_ = v___x_437_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_457_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_434_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_434_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_465_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_432_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_432_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_481_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_426_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_426_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
}
}
}
v___jp_404_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_399_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_399_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
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
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* v_e_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_dreduceIte(v_e_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_));
v___x_514_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_515_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_512_, v___x_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15____boxed(lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
return v_res_517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_522_ = 0;
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
v___x_524_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_521_, v___x_522_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_));
v___x_529_ = 0;
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
v___x_531_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_528_, v___x_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object* v_e_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
uint8_t v_inDSimp_546_; 
v_inDSimp_546_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*10 + 8);
if (v_inDSimp_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_e_534_);
v___x_547_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_534_, v_a_539_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_644_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_644_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_644_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_644_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = l_Lean_Expr_cleanupAnnotations(v_a_550_);
v___x_560_ = l_Lean_Expr_isApp(v___x_559_);
if (v___x_560_ == 0)
{
lean_dec_ref(v___x_559_);
goto v___jp_554_;
}
else
{
lean_object* v_arg_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_arg_561_ = lean_ctor_get(v___x_559_, 1);
lean_inc_ref(v_arg_561_);
v___x_562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_559_);
v___x_563_ = l_Lean_Expr_isApp(v___x_562_);
if (v___x_563_ == 0)
{
lean_dec_ref(v___x_562_);
lean_dec_ref(v_arg_561_);
goto v___jp_554_;
}
else
{
lean_object* v_arg_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_arg_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc_ref(v_arg_564_);
v___x_565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_562_);
v___x_566_ = l_Lean_Expr_isApp(v___x_565_);
if (v___x_566_ == 0)
{
lean_dec_ref(v___x_565_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_554_;
}
else
{
lean_object* v_arg_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_arg_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc_ref(v_arg_567_);
v___x_568_ = l_Lean_Expr_appFnCleanup___redArg(v___x_565_);
v___x_569_ = l_Lean_Expr_isApp(v___x_568_);
if (v___x_569_ == 0)
{
lean_dec_ref(v___x_568_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_554_;
}
else
{
lean_object* v_arg_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_arg_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc_ref(v_arg_570_);
v___x_571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_568_);
v___x_572_ = l_Lean_Expr_isApp(v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v___x_571_);
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_554_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_571_);
v___x_574_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_575_ = l_Lean_Expr_isConstOf(v___x_573_, v___x_574_);
lean_dec_ref(v___x_573_);
if (v___x_575_ == 0)
{
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_554_;
}
else
{
lean_object* v___x_576_; 
lean_del_object(v___x_552_);
lean_inc(v_a_541_);
lean_inc_ref(v_a_540_);
lean_inc(v_a_539_);
lean_inc_ref(v_a_538_);
lean_inc(v_a_537_);
lean_inc_ref(v_a_536_);
lean_inc(v_a_535_);
v___x_576_ = lean_simp(v_arg_570_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_635_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_635_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_635_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_635_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_expr_628_; uint8_t v___x_629_; 
v_expr_628_ = lean_ctor_get(v_a_577_, 0);
lean_inc_ref_n(v_expr_628_, 2);
lean_dec(v_a_577_);
v___x_629_ = l_Lean_Expr_isTrue(v_expr_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = l_Lean_Expr_isFalse(v_expr_628_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v___x_631_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_631_);
v___x_633_ = v___x_579_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_del_object(v___x_579_);
goto v___jp_581_;
}
}
else
{
lean_dec_ref(v_expr_628_);
lean_del_object(v___x_579_);
goto v___jp_581_;
}
v___jp_581_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_whnfD(v_arg_567_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_583_, v_a_539_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_611_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_611_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_611_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_611_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Expr_cleanupAnnotations(v_a_585_);
v___x_590_ = l_Lean_Expr_isApp(v___x_589_);
if (v___x_590_ == 0)
{
lean_dec_ref(v___x_589_);
lean_del_object(v___x_587_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_543_;
}
else
{
lean_object* v_arg_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_arg_591_ = lean_ctor_get(v___x_589_, 1);
lean_inc_ref(v_arg_591_);
v___x_592_ = l_Lean_Expr_appFnCleanup___redArg(v___x_589_);
v___x_593_ = l_Lean_Expr_isApp(v___x_592_);
if (v___x_593_ == 0)
{
lean_dec_ref(v___x_592_);
lean_dec_ref(v_arg_591_);
lean_del_object(v___x_587_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
goto v___jp_543_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_592_);
v___x_595_ = ((lean_object*)(l_dreduceIte___closed__3));
v___x_596_ = l_Lean_Expr_isConstOf(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
lean_dec_ref(v_arg_561_);
v___x_597_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_598_ = l_Lean_Expr_isConstOf(v___x_594_, v___x_597_);
lean_dec_ref(v___x_594_);
if (v___x_598_ == 0)
{
lean_dec_ref(v_arg_591_);
lean_del_object(v___x_587_);
lean_dec_ref(v_arg_564_);
goto v___jp_543_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_599_ = l_Lean_Expr_app___override(v_arg_564_, v_arg_591_);
v___x_600_ = l_Lean_Expr_headBeta(v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_601_);
v___x_603_ = v___x_587_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec_ref(v___x_594_);
lean_dec_ref(v_arg_564_);
v___x_605_ = l_Lean_Expr_app___override(v_arg_561_, v_arg_591_);
v___x_606_ = l_Lean_Expr_headBeta(v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_607_);
v___x_609_ = v___x_587_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_612_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_584_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_584_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_620_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_582_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_582_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_636_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_576_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_576_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
}
}
v___jp_554_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_549_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_549_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* v_e_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_dreduceDIte(v_e_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_));
v___x_669_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_670_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_667_, v___x_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_677_ = 0;
v___x_678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
v___x_679_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_676_, v___x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_));
v___x_684_ = 0;
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
v___x_686_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_683_, v___x_684_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object* v_x_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_reduceCtorEq___lam__0(v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_reduceCtorEq___lam__1(v_x_722_, v_x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v_x_723_);
lean_dec(v_x_722_);
return v_res_732_;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_box(0);
v___x_737_ = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
v___x_738_ = l_Lean_mkConst(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static uint64_t _init_l_reduceCtorEq___lam__2___closed__3(void){
_start:
{
uint8_t v___x_739_; uint64_t v___x_740_; 
v___x_739_ = 1;
v___x_740_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t v___x_741_, uint64_t v___x_742_, lean_object* v_h_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v_a_754_; lean_object* v___x_759_; 
v___x_752_ = lean_obj_once(&l_reduceCtorEq___lam__2___closed__2, &l_reduceCtorEq___lam__2___closed__2_once, _init_l_reduceCtorEq___lam__2___closed__2);
lean_inc_ref(v_h_743_);
v___x_759_ = l_Lean_Meta_mkNoConfusion(v___x_752_, v_h_743_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
v___x_763_ = lean_array_push(v___x_762_, v_h_743_);
v___x_764_ = 0;
v___x_765_ = 1;
v___x_766_ = l_Lean_Meta_mkLambdaFVars(v___x_763_, v_a_760_, v___x_764_, v___x_741_, v___x_764_, v___x_741_, v___x_765_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; uint8_t v_foApprox_769_; uint8_t v_ctxApprox_770_; uint8_t v_quasiPatternApprox_771_; uint8_t v_constApprox_772_; uint8_t v_isDefEqStuckEx_773_; uint8_t v_unificationHints_774_; uint8_t v_proofIrrelevance_775_; uint8_t v_assignSyntheticOpaque_776_; uint8_t v_offsetCnstrs_777_; uint8_t v_etaStruct_778_; uint8_t v_univApprox_779_; uint8_t v_iota_780_; uint8_t v_beta_781_; uint8_t v_proj_782_; uint8_t v_zeta_783_; uint8_t v_zetaDelta_784_; uint8_t v_zetaUnused_785_; uint8_t v_zetaHave_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_822_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Meta_Context_config(v___y_747_);
v_foApprox_769_ = lean_ctor_get_uint8(v___x_768_, 0);
v_ctxApprox_770_ = lean_ctor_get_uint8(v___x_768_, 1);
v_quasiPatternApprox_771_ = lean_ctor_get_uint8(v___x_768_, 2);
v_constApprox_772_ = lean_ctor_get_uint8(v___x_768_, 3);
v_isDefEqStuckEx_773_ = lean_ctor_get_uint8(v___x_768_, 4);
v_unificationHints_774_ = lean_ctor_get_uint8(v___x_768_, 5);
v_proofIrrelevance_775_ = lean_ctor_get_uint8(v___x_768_, 6);
v_assignSyntheticOpaque_776_ = lean_ctor_get_uint8(v___x_768_, 7);
v_offsetCnstrs_777_ = lean_ctor_get_uint8(v___x_768_, 8);
v_etaStruct_778_ = lean_ctor_get_uint8(v___x_768_, 10);
v_univApprox_779_ = lean_ctor_get_uint8(v___x_768_, 11);
v_iota_780_ = lean_ctor_get_uint8(v___x_768_, 12);
v_beta_781_ = lean_ctor_get_uint8(v___x_768_, 13);
v_proj_782_ = lean_ctor_get_uint8(v___x_768_, 14);
v_zeta_783_ = lean_ctor_get_uint8(v___x_768_, 15);
v_zetaDelta_784_ = lean_ctor_get_uint8(v___x_768_, 16);
v_zetaUnused_785_ = lean_ctor_get_uint8(v___x_768_, 17);
v_zetaHave_786_ = lean_ctor_get_uint8(v___x_768_, 18);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_822_ == 0)
{
v___x_788_ = v___x_768_;
v_isShared_789_ = v_isSharedCheck_822_;
goto v_resetjp_787_;
}
else
{
lean_dec(v___x_768_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_822_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v_trackZetaDelta_790_; lean_object* v_zetaDeltaSet_791_; lean_object* v_lctx_792_; lean_object* v_localInstances_793_; lean_object* v_defEqCtx_x3f_794_; lean_object* v_synthPendingDepth_795_; lean_object* v_canUnfold_x3f_796_; uint8_t v_univApprox_797_; uint8_t v_inTypeClassResolution_798_; uint8_t v_cacheInferType_799_; uint8_t v___x_800_; lean_object* v_config_802_; 
v_trackZetaDelta_790_ = lean_ctor_get_uint8(v___y_747_, sizeof(void*)*7);
v_zetaDeltaSet_791_ = lean_ctor_get(v___y_747_, 1);
v_lctx_792_ = lean_ctor_get(v___y_747_, 2);
v_localInstances_793_ = lean_ctor_get(v___y_747_, 3);
v_defEqCtx_x3f_794_ = lean_ctor_get(v___y_747_, 4);
v_synthPendingDepth_795_ = lean_ctor_get(v___y_747_, 5);
v_canUnfold_x3f_796_ = lean_ctor_get(v___y_747_, 6);
v_univApprox_797_ = lean_ctor_get_uint8(v___y_747_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_798_ = lean_ctor_get_uint8(v___y_747_, sizeof(void*)*7 + 2);
v_cacheInferType_799_ = lean_ctor_get_uint8(v___y_747_, sizeof(void*)*7 + 3);
v___x_800_ = 1;
if (v_isShared_789_ == 0)
{
v_config_802_ = v___x_788_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 0, v_foApprox_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 1, v_ctxApprox_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 2, v_quasiPatternApprox_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 3, v_constApprox_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 4, v_isDefEqStuckEx_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 5, v_unificationHints_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 6, v_proofIrrelevance_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 7, v_assignSyntheticOpaque_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 8, v_offsetCnstrs_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 10, v_etaStruct_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 11, v_univApprox_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 12, v_iota_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 13, v_beta_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 14, v_proj_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 15, v_zeta_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 16, v_zetaDelta_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 17, v_zetaUnused_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_821_, 18, v_zetaHave_786_);
v_config_802_ = v_reuseFailAlloc_821_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_key_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_ctor_set_uint8(v_config_802_, 9, v___x_800_);
v___x_803_ = l_Lean_Meta_Context_configKey(v___y_747_);
v___x_804_ = lean_uint64_shift_right(v___x_803_, v___x_742_);
v___x_805_ = lean_uint64_shift_left(v___x_804_, v___x_742_);
v___x_806_ = lean_uint64_once(&l_reduceCtorEq___lam__2___closed__3, &l_reduceCtorEq___lam__2___closed__3_once, _init_l_reduceCtorEq___lam__2___closed__3);
v_key_807_ = lean_uint64_lor(v___x_805_, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_808_, 0, v_config_802_);
lean_ctor_set_uint64(v___x_808_, sizeof(void*)*1, v_key_807_);
lean_inc(v_canUnfold_x3f_796_);
lean_inc(v_synthPendingDepth_795_);
lean_inc(v_defEqCtx_x3f_794_);
lean_inc_ref(v_localInstances_793_);
lean_inc_ref(v_lctx_792_);
lean_inc(v_zetaDeltaSet_791_);
v___x_809_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_zetaDeltaSet_791_);
lean_ctor_set(v___x_809_, 2, v_lctx_792_);
lean_ctor_set(v___x_809_, 3, v_localInstances_793_);
lean_ctor_set(v___x_809_, 4, v_defEqCtx_x3f_794_);
lean_ctor_set(v___x_809_, 5, v_synthPendingDepth_795_);
lean_ctor_set(v___x_809_, 6, v_canUnfold_x3f_796_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7, v_trackZetaDelta_790_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 1, v_univApprox_797_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 2, v_inTypeClassResolution_798_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 3, v_cacheInferType_799_);
v___x_810_ = l_Lean_Meta_mkEqFalse_x27(v_a_767_, v___x_809_, v___y_748_, v___y_749_, v___y_750_);
lean_dec_ref_known(v___x_809_, 7);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v_a_754_ = v_a_811_;
goto v___jp_753_;
}
else
{
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_810_, 1);
v_a_754_ = v_a_812_;
goto v___jp_753_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_810_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_810_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_766_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_766_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_h_743_);
v_a_831_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_759_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_759_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_a_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_756_, 0, v___x_752_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*2, v___x_741_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v_h_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_26307__boxed_850_; uint64_t v___x_26308__boxed_851_; lean_object* v_res_852_; 
v___x_26307__boxed_850_ = lean_unbox(v___x_839_);
v___x_26308__boxed_851_ = lean_unbox_uint64(v___x_840_);
lean_dec_ref(v___x_840_);
v_res_852_ = l_reduceCtorEq___lam__2(v___x_26307__boxed_850_, v___x_26308__boxed_851_, v_h_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
v___x_863_ = lean_apply_9(v_k_853_, v_b_857_, v___y_854_, v___y_855_, v___y_856_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, lean_box(0));
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v_b_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_864_, v___y_865_, v___y_866_, v___y_867_, v_b_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_875_, uint8_t v_bi_876_, lean_object* v_type_877_, lean_object* v_k_878_, uint8_t v_kind_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___f_888_; lean_object* v___x_889_; 
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_888_, 0, v_k_878_);
lean_closure_set(v___f_888_, 1, v___y_880_);
lean_closure_set(v___f_888_, 2, v___y_881_);
lean_closure_set(v___f_888_, 3, v___y_882_);
v___x_889_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_875_, v_bi_876_, v_type_877_, v___f_888_, v_kind_879_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_889_) == 0)
{
return v___x_889_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_898_, lean_object* v_bi_899_, lean_object* v_type_900_, lean_object* v_k_901_, lean_object* v_kind_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_bi_boxed_911_; uint8_t v_kind_boxed_912_; lean_object* v_res_913_; 
v_bi_boxed_911_ = lean_unbox(v_bi_899_);
v_kind_boxed_912_ = lean_unbox(v_kind_902_);
v_res_913_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_898_, v_bi_boxed_911_, v_type_900_, v_k_901_, v_kind_boxed_912_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* v_name_914_, lean_object* v_type_915_, lean_object* v_k_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = 0;
v___x_926_ = 0;
v___x_927_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_914_, v___x_925_, v_type_915_, v_k_916_, v___x_926_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_928_, lean_object* v_type_929_, lean_object* v_k_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_928_, v_type_929_, v_k_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
return v_res_939_;
}
}
static uint64_t _init_l_reduceCtorEq___closed__0(void){
_start:
{
uint8_t v___x_940_; uint64_t v___x_941_; 
v___x_940_ = 3;
v___x_941_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object* v_e_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___y_960_; lean_object* v___x_969_; uint8_t v_foApprox_970_; uint8_t v_ctxApprox_971_; uint8_t v_quasiPatternApprox_972_; uint8_t v_constApprox_973_; uint8_t v_isDefEqStuckEx_974_; uint8_t v_unificationHints_975_; uint8_t v_proofIrrelevance_976_; uint8_t v_assignSyntheticOpaque_977_; uint8_t v_offsetCnstrs_978_; uint8_t v_etaStruct_979_; uint8_t v_univApprox_980_; uint8_t v_iota_981_; uint8_t v_beta_982_; uint8_t v_proj_983_; uint8_t v_zeta_984_; uint8_t v_zetaDelta_985_; uint8_t v_zetaUnused_986_; uint8_t v_zetaHave_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1088_; 
v___x_969_ = l_Lean_Meta_Context_config(v_a_954_);
v_foApprox_970_ = lean_ctor_get_uint8(v___x_969_, 0);
v_ctxApprox_971_ = lean_ctor_get_uint8(v___x_969_, 1);
v_quasiPatternApprox_972_ = lean_ctor_get_uint8(v___x_969_, 2);
v_constApprox_973_ = lean_ctor_get_uint8(v___x_969_, 3);
v_isDefEqStuckEx_974_ = lean_ctor_get_uint8(v___x_969_, 4);
v_unificationHints_975_ = lean_ctor_get_uint8(v___x_969_, 5);
v_proofIrrelevance_976_ = lean_ctor_get_uint8(v___x_969_, 6);
v_assignSyntheticOpaque_977_ = lean_ctor_get_uint8(v___x_969_, 7);
v_offsetCnstrs_978_ = lean_ctor_get_uint8(v___x_969_, 8);
v_etaStruct_979_ = lean_ctor_get_uint8(v___x_969_, 10);
v_univApprox_980_ = lean_ctor_get_uint8(v___x_969_, 11);
v_iota_981_ = lean_ctor_get_uint8(v___x_969_, 12);
v_beta_982_ = lean_ctor_get_uint8(v___x_969_, 13);
v_proj_983_ = lean_ctor_get_uint8(v___x_969_, 14);
v_zeta_984_ = lean_ctor_get_uint8(v___x_969_, 15);
v_zetaDelta_985_ = lean_ctor_get_uint8(v___x_969_, 16);
v_zetaUnused_986_ = lean_ctor_get_uint8(v___x_969_, 17);
v_zetaHave_987_ = lean_ctor_get_uint8(v___x_969_, 18);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_989_ = v___x_969_;
v_isShared_990_ = v_isSharedCheck_1088_;
goto v_resetjp_988_;
}
else
{
lean_dec(v___x_969_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1088_;
goto v_resetjp_988_;
}
v___jp_959_:
{
if (lean_obj_tag(v___y_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___y_960_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___y_960_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___y_960_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___y_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
return v___y_960_;
}
}
v_resetjp_988_:
{
uint8_t v_trackZetaDelta_991_; lean_object* v_zetaDeltaSet_992_; lean_object* v_lctx_993_; lean_object* v_localInstances_994_; lean_object* v_defEqCtx_x3f_995_; lean_object* v_synthPendingDepth_996_; lean_object* v_canUnfold_x3f_997_; uint8_t v_univApprox_998_; uint8_t v_inTypeClassResolution_999_; uint8_t v_cacheInferType_1000_; lean_object* v___x_1001_; 
v_trackZetaDelta_991_ = lean_ctor_get_uint8(v_a_954_, sizeof(void*)*7);
v_zetaDeltaSet_992_ = lean_ctor_get(v_a_954_, 1);
v_lctx_993_ = lean_ctor_get(v_a_954_, 2);
v_localInstances_994_ = lean_ctor_get(v_a_954_, 3);
v_defEqCtx_x3f_995_ = lean_ctor_get(v_a_954_, 4);
v_synthPendingDepth_996_ = lean_ctor_get(v_a_954_, 5);
v_canUnfold_x3f_997_ = lean_ctor_get(v_a_954_, 6);
v_univApprox_998_ = lean_ctor_get_uint8(v_a_954_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_999_ = lean_ctor_get_uint8(v_a_954_, sizeof(void*)*7 + 2);
v_cacheInferType_1000_ = lean_ctor_get_uint8(v_a_954_, sizeof(void*)*7 + 3);
lean_inc_ref(v_e_950_);
v___x_1001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_950_, v_a_955_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; uint8_t v___x_1003_; lean_object* v_config_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = 3;
if (v_isShared_990_ == 0)
{
v_config_1005_ = v___x_989_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 0, v_foApprox_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 1, v_ctxApprox_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 2, v_quasiPatternApprox_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 3, v_constApprox_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 4, v_isDefEqStuckEx_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 5, v_unificationHints_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 6, v_proofIrrelevance_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 7, v_assignSyntheticOpaque_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 8, v_offsetCnstrs_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 10, v_etaStruct_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 11, v_univApprox_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 12, v_iota_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 13, v_beta_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 14, v_proj_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 15, v_zeta_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 16, v_zetaDelta_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 17, v_zetaUnused_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, 18, v_zetaHave_987_);
v_config_1005_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
uint64_t v___x_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; uint64_t v___x_1010_; uint64_t v_key_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
lean_ctor_set_uint8(v_config_1005_, 9, v___x_1003_);
v___x_1006_ = l_Lean_Meta_Context_configKey(v_a_954_);
v___x_1007_ = 3ULL;
v___x_1008_ = lean_uint64_shift_right(v___x_1006_, v___x_1007_);
v___x_1009_ = lean_uint64_shift_left(v___x_1008_, v___x_1007_);
v___x_1010_ = lean_uint64_once(&l_reduceCtorEq___closed__0, &l_reduceCtorEq___closed__0_once, _init_l_reduceCtorEq___closed__0);
v_key_1011_ = lean_uint64_lor(v___x_1009_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1012_, 0, v_config_1005_);
lean_ctor_set_uint64(v___x_1012_, sizeof(void*)*1, v_key_1011_);
lean_inc(v_canUnfold_x3f_997_);
lean_inc(v_synthPendingDepth_996_);
lean_inc(v_defEqCtx_x3f_995_);
lean_inc_ref(v_localInstances_994_);
lean_inc_ref(v_lctx_993_);
lean_inc(v_zetaDeltaSet_992_);
v___x_1013_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_zetaDeltaSet_992_);
lean_ctor_set(v___x_1013_, 2, v_lctx_993_);
lean_ctor_set(v___x_1013_, 3, v_localInstances_994_);
lean_ctor_set(v___x_1013_, 4, v_defEqCtx_x3f_995_);
lean_ctor_set(v___x_1013_, 5, v_synthPendingDepth_996_);
lean_ctor_set(v___x_1013_, 6, v_canUnfold_x3f_997_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*7, v_trackZetaDelta_991_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*7 + 1, v_univApprox_998_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*7 + 2, v_inTypeClassResolution_999_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*7 + 3, v_cacheInferType_1000_);
v___x_1014_ = l_Lean_Expr_cleanupAnnotations(v_a_1002_);
v___x_1015_ = l_Lean_Expr_isApp(v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_1014_);
lean_dec_ref(v_e_950_);
v___x_1016_ = lean_box(0);
v___x_1017_ = l_reduceCtorEq___lam__0(v___x_1016_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
v___y_960_ = v___x_1017_;
goto v___jp_959_;
}
else
{
lean_object* v_arg_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_arg_1018_ = lean_ctor_get(v___x_1014_, 1);
lean_inc_ref(v_arg_1018_);
v___x_1019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1014_);
v___x_1020_ = l_Lean_Expr_isApp(v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v___x_1019_);
lean_dec_ref(v_arg_1018_);
lean_dec_ref(v_e_950_);
v___x_1021_ = lean_box(0);
v___x_1022_ = l_reduceCtorEq___lam__0(v___x_1021_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
v___y_960_ = v___x_1022_;
goto v___jp_959_;
}
else
{
lean_object* v_arg_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_arg_1023_ = lean_ctor_get(v___x_1019_, 1);
lean_inc_ref(v_arg_1023_);
v___x_1024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1019_);
v___x_1025_ = l_Lean_Expr_isApp(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1018_);
lean_dec_ref(v_e_950_);
v___x_1026_ = lean_box(0);
v___x_1027_ = l_reduceCtorEq___lam__0(v___x_1026_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
v___y_960_ = v___x_1027_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1024_);
v___x_1029_ = ((lean_object*)(l_reduceCtorEq___closed__2));
v___x_1030_ = l_Lean_Expr_isConstOf(v___x_1028_, v___x_1029_);
lean_dec_ref(v___x_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_arg_1023_);
lean_dec_ref(v_arg_1018_);
lean_dec_ref(v_e_950_);
v___x_1031_ = lean_box(0);
v___x_1032_ = l_reduceCtorEq___lam__0(v___x_1031_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
v___y_960_ = v___x_1032_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1023_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1018_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_1035_) == 0)
{
if (lean_obj_tag(v_a_1034_) == 1)
{
lean_object* v_val_1036_; lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1060_; 
v_val_1036_ = lean_ctor_get(v_a_1034_, 0);
v_a_1037_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1039_ = v___x_1035_;
v_isShared_1040_ = v_isSharedCheck_1060_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1060_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
if (lean_obj_tag(v_a_1037_) == 1)
{
lean_object* v_val_1041_; lean_object* v_fst_1042_; lean_object* v_toConstantVal_1043_; lean_object* v_fst_1044_; lean_object* v_toConstantVal_1045_; lean_object* v_name_1046_; lean_object* v_name_1047_; uint8_t v___x_1048_; uint8_t v___x_1049_; 
lean_inc(v_val_1036_);
lean_dec_ref_known(v_a_1034_, 1);
v_val_1041_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_val_1041_);
lean_dec_ref_known(v_a_1037_, 1);
v_fst_1042_ = lean_ctor_get(v_val_1036_, 0);
lean_inc(v_fst_1042_);
lean_dec(v_val_1036_);
v_toConstantVal_1043_ = lean_ctor_get(v_fst_1042_, 0);
lean_inc_ref(v_toConstantVal_1043_);
lean_dec(v_fst_1042_);
v_fst_1044_ = lean_ctor_get(v_val_1041_, 0);
lean_inc(v_fst_1044_);
lean_dec(v_val_1041_);
v_toConstantVal_1045_ = lean_ctor_get(v_fst_1044_, 0);
lean_inc_ref(v_toConstantVal_1045_);
lean_dec(v_fst_1044_);
v_name_1046_ = lean_ctor_get(v_toConstantVal_1043_, 0);
lean_inc(v_name_1046_);
lean_dec_ref(v_toConstantVal_1043_);
v_name_1047_ = lean_ctor_get(v_toConstantVal_1045_, 0);
lean_inc(v_name_1047_);
lean_dec_ref(v_toConstantVal_1045_);
v___x_1048_ = lean_name_eq(v_name_1046_, v_name_1047_);
lean_dec(v_name_1047_);
lean_dec(v_name_1046_);
v___x_1049_ = lean_bool_not(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1013_, 7);
lean_dec_ref(v_e_950_);
v___x_1050_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1050_);
v___x_1052_ = v___x_1039_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_del_object(v___x_1039_);
v___x_1054_ = lean_box(v___x_1030_);
v___x_1055_ = ((lean_object*)(l_reduceCtorEq___boxed__const__1));
v___f_1056_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1056_, 0, v___x_1054_);
lean_closure_set(v___f_1056_, 1, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_reduceCtorEq___closed__4));
v___x_1058_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1057_, v_e_950_, v___f_1056_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
v___y_960_ = v___x_1058_;
goto v___jp_959_;
}
}
else
{
lean_object* v___x_1059_; 
lean_del_object(v___x_1039_);
lean_dec_ref(v_e_950_);
v___x_1059_ = l_reduceCtorEq___lam__1(v_a_1034_, v_a_1037_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
lean_dec(v_a_1037_);
lean_dec_ref_known(v_a_1034_, 1);
v___y_960_ = v___x_1059_;
goto v___jp_959_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
lean_dec_ref(v_e_950_);
v_a_1061_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1062_ = l_reduceCtorEq___lam__1(v_a_1034_, v_a_1061_, v_a_951_, v_a_952_, v_a_953_, v___x_1013_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref_known(v___x_1013_, 7);
lean_dec(v_a_1061_);
lean_dec(v_a_1034_);
v___y_960_ = v___x_1062_;
goto v___jp_959_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_1034_);
lean_dec_ref_known(v___x_1013_, 7);
lean_dec_ref(v_e_950_);
v_a_1063_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1035_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1035_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v_arg_1018_);
lean_dec_ref_known(v___x_1013_, 7);
lean_dec_ref(v_e_950_);
v_a_1071_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1033_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1033_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
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
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_989_);
lean_dec_ref(v_e_950_);
v_a_1080_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1001_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1001_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_reduceCtorEq(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_1099_, lean_object* v_name_1100_, uint8_t v_bi_1101_, lean_object* v_type_1102_, lean_object* v_k_1103_, uint8_t v_kind_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_1100_, v_bi_1101_, v_type_1102_, v_k_1103_, v_kind_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_name_1115_, lean_object* v_bi_1116_, lean_object* v_type_1117_, lean_object* v_k_1118_, lean_object* v_kind_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_bi_boxed_1128_; uint8_t v_kind_boxed_1129_; lean_object* v_res_1130_; 
v_bi_boxed_1128_ = lean_unbox(v_bi_1116_);
v_kind_boxed_1129_ = lean_unbox(v_kind_1119_);
v_res_1130_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_1114_, v_name_1115_, v_bi_boxed_1128_, v_type_1117_, v_k_1118_, v_kind_boxed_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* v_00_u03b1_1131_, lean_object* v_name_1132_, lean_object* v_type_1133_, lean_object* v_k_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_1132_, v_type_1133_, v_k_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_name_1145_, lean_object* v_type_1146_, lean_object* v_k_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(v_00_u03b1_1144_, v_name_1145_, v_type_1146_, v_k_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1174_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1175_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1172_, v___x_1173_, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
return v_res_1177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1182_ = 1;
v___x_1183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
v___x_1184_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1181_, v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_));
v___x_1189_ = 1;
v___x_1190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
v___x_1191_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1188_, v___x_1189_, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
return v_res_1193_;
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
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
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
