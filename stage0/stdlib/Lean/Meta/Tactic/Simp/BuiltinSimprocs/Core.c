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
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static const lean_ctor_object l_reduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_reduceIte___closed__0 = (const lean_object*)&l_reduceIte___closed__0_value;
static const lean_string_object l_reduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_reduceIte___closed__1 = (const lean_object*)&l_reduceIte___closed__1_value;
static const lean_ctor_object l_reduceIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_reduceIte___closed__2 = (const lean_object*)&l_reduceIte___closed__2_value;
static const lean_string_object l_reduceIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ite_eq_right_of_eq_false"};
static const lean_object* l_reduceIte___closed__3 = (const lean_object*)&l_reduceIte___closed__3_value;
static const lean_ctor_object l_reduceIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 223, 35, 242, 130, 83, 13)}};
static const lean_object* l_reduceIte___closed__4 = (const lean_object*)&l_reduceIte___closed__4_value;
static const lean_string_object l_reduceIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_eq_left_of_eq_true"};
static const lean_object* l_reduceIte___closed__5 = (const lean_object*)&l_reduceIte___closed__5_value;
static const lean_ctor_object l_reduceIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceIte___closed__5_value),LEAN_SCALAR_PTR_LITERAL(73, 84, 15, 184, 226, 12, 142, 9)}};
static const lean_object* l_reduceIte___closed__6 = (const lean_object*)&l_reduceIte___closed__6_value;
LEAN_EXPORT lean_object* l_reduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(1, 182, 106, 10, 77, 189, 166, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceIte___closed__2_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l_reduceDIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "dite_eq_right_of_eq_false"};
static const lean_object* l_reduceDIte___closed__5 = (const lean_object*)&l_reduceDIte___closed__5_value;
static const lean_ctor_object l_reduceDIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 72, 248, 145, 136, 9, 228, 221)}};
static const lean_object* l_reduceDIte___closed__6 = (const lean_object*)&l_reduceDIte___closed__6_value;
static const lean_string_object l_reduceDIte___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_eq_true"};
static const lean_object* l_reduceDIte___closed__7 = (const lean_object*)&l_reduceDIte___closed__7_value;
static const lean_ctor_object l_reduceDIte___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__7_value),LEAN_SCALAR_PTR_LITERAL(180, 216, 190, 52, 49, 30, 207, 178)}};
static const lean_object* l_reduceDIte___closed__8 = (const lean_object*)&l_reduceDIte___closed__8_value;
static lean_once_cell_t l_reduceDIte___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_reduceDIte___closed__9;
static const lean_string_object l_reduceDIte___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "dite_eq_left_of_eq_true"};
static const lean_object* l_reduceDIte___closed__10 = (const lean_object*)&l_reduceDIte___closed__10_value;
static const lean_ctor_object l_reduceDIte___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceDIte___closed__10_value),LEAN_SCALAR_PTR_LITERAL(36, 253, 19, 136, 170, 78, 36, 13)}};
static const lean_object* l_reduceDIte___closed__11 = (const lean_object*)&l_reduceDIte___closed__11_value;
LEAN_EXPORT lean_object* l_reduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(30, 101, 22, 109, 248, 175, 82, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceDIte___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26____boxed(lean_object*);
static const lean_ctor_object l_dreduceIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_dreduceIte___closed__0 = (const lean_object*)&l_dreduceIte___closed__0_value;
static const lean_string_object l_dreduceIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_dreduceIte___closed__1 = (const lean_object*)&l_dreduceIte___closed__1_value;
static const lean_ctor_object l_dreduceIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_dreduceIte___closed__2 = (const lean_object*)&l_dreduceIte___closed__2_value;
static const lean_string_object l_dreduceIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_dreduceIte___closed__3 = (const lean_object*)&l_dreduceIte___closed__3_value;
static const lean_string_object l_dreduceIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_dreduceIte___closed__4 = (const lean_object*)&l_dreduceIte___closed__4_value;
static const lean_ctor_object l_dreduceIte___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_dreduceIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__5_value_aux_0),((lean_object*)&l_dreduceIte___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_dreduceIte___closed__5 = (const lean_object*)&l_dreduceIte___closed__5_value;
static const lean_string_object l_dreduceIte___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_dreduceIte___closed__6 = (const lean_object*)&l_dreduceIte___closed__6_value;
static const lean_ctor_object l_dreduceIte___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_dreduceIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_dreduceIte___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_dreduceIte___closed__7_value_aux_0),((lean_object*)&l_dreduceIte___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_dreduceIte___closed__7 = (const lean_object*)&l_dreduceIte___closed__7_value;
LEAN_EXPORT lean_object* l_dreduceIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dreduceIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(20, 216, 99, 140, 103, 209, 78, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26____boxed(lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dreduceDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(222, 220, 170, 50, 32, 2, 19, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_reduceCtorEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_reduceCtorEq___closed__0 = (const lean_object*)&l_reduceCtorEq___closed__0_value;
static const lean_ctor_object l_reduceCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_reduceCtorEq___closed__1 = (const lean_object*)&l_reduceCtorEq___closed__1_value;
static const lean_string_object l_reduceCtorEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_reduceCtorEq___closed__2 = (const lean_object*)&l_reduceCtorEq___closed__2_value;
static const lean_ctor_object l_reduceCtorEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_reduceCtorEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_reduceCtorEq___closed__3 = (const lean_object*)&l_reduceCtorEq___closed__3_value;
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_reduceCtorEq___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27____boxed(lean_object*);
lean_object* l_reduceIte(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_12_, v_a_17_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_24_, 1);
v___x_26_ = l_Lean_Expr_cleanupAnnotations(v_a_25_);
v___x_27_ = l_Lean_Expr_isApp(v___x_26_);
if (v___x_27_ == 0)
{
lean_dec_ref(v___x_26_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_arg_28_ = lean_ctor_get(v___x_26_, 1);
lean_inc_ref(v_arg_28_);
v___x_29_ = l_Lean_Expr_appFnCleanup___redArg(v___x_26_);
v___x_30_ = l_Lean_Expr_isApp(v___x_29_);
if (v___x_30_ == 0)
{
lean_dec_ref(v___x_29_);
lean_dec_ref(v_arg_28_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_arg_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc_ref(v_arg_31_);
v___x_32_ = l_Lean_Expr_appFnCleanup___redArg(v___x_29_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v___x_32_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_arg_34_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_arg_34_);
v___x_35_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_arg_37_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_arg_37_);
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_21_;
}
else
{
lean_object* v_arg_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_arg_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_arg_40_);
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_42_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_43_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
goto v___jp_21_;
}
else
{
lean_object* v___x_44_; 
lean_inc(v_a_19_);
lean_inc_ref(v_a_18_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_arg_37_);
v___x_44_ = lean_simp(v_arg_37_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_106_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_106_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_106_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_106_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_expr_49_; uint8_t v___x_50_; 
v_expr_49_ = lean_ctor_get(v_a_45_, 0);
lean_inc_ref(v_expr_49_);
v___x_50_ = l_Lean_Expr_isTrue(v_expr_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
lean_inc_ref(v_expr_49_);
v___x_51_ = l_Lean_Expr_isFalse(v_expr_49_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_dec(v_a_45_);
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
v___x_52_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_52_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
lean_object* v___x_56_; 
lean_del_object(v___x_47_);
v___x_56_ = l_Lean_Meta_Simp_Result_getProof(v_a_45_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_72_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_72_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_72_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_72_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_61_ = ((lean_object*)(l_reduceIte___closed__4));
v___x_62_ = l_Lean_Expr_constLevels_x21(v___x_41_);
lean_dec_ref(v___x_41_);
v___x_63_ = l_Lean_mkConst(v___x_61_, v___x_62_);
lean_inc_ref(v_arg_28_);
v___x_64_ = l_Lean_mkApp5(v___x_63_, v_arg_40_, v_arg_37_, v_arg_34_, v_arg_31_, v_arg_28_);
v___x_65_ = l_Lean_Expr_app___override(v___x_64_, v_a_57_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_67_, 0, v_arg_28_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*2, v___x_43_);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_68_);
v___x_70_ = v___x_59_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
v_a_73_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_56_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_56_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
else
{
lean_object* v___x_81_; 
lean_del_object(v___x_47_);
v___x_81_ = l_Lean_Meta_Simp_Result_getProof(v_a_45_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_97_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_97_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_97_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_97_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_86_ = ((lean_object*)(l_reduceIte___closed__6));
v___x_87_ = l_Lean_Expr_constLevels_x21(v___x_41_);
lean_dec_ref(v___x_41_);
v___x_88_ = l_Lean_mkConst(v___x_86_, v___x_87_);
lean_inc_ref(v_arg_31_);
v___x_89_ = l_Lean_mkApp5(v___x_88_, v_arg_40_, v_arg_37_, v_arg_34_, v_arg_31_, v_arg_28_);
v___x_90_ = l_Lean_Expr_app___override(v___x_89_, v_a_82_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_92_, 0, v_arg_31_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*2, v___x_43_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_93_);
v___x_95_ = v___x_84_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
v_a_98_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_81_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_81_);
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
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_31_);
lean_dec_ref(v_arg_28_);
v_a_107_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_44_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_44_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
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
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_115_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_24_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_24_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
v___jp_21_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT void l_reduceIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_12_ = stack[0].m_obj;
lean_object* v_a_13_ = stack[1].m_obj;
lean_object* v_a_14_ = stack[2].m_obj;
lean_object* v_a_15_ = stack[3].m_obj;
lean_object* v_a_16_ = stack[4].m_obj;
lean_object* v_a_17_ = stack[5].m_obj;
lean_object* v_a_18_ = stack[6].m_obj;
lean_object* v_a_19_ = stack[7].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_reduceIte(v_e_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_reduceIte(v_e_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
return v_res_133_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_153_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_154_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_151_, v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_155_;
v_res_155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22____boxed(lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
return v_res_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_162_ = 0;
v___x_163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_164_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_165_;
v_res_165_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24____boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
return v_res_167_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_170_ = 0;
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_172_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_169_, v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_173_;
v_res_173_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26____boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
return v_res_175_;
}
}
static lean_object* _init_l_reduceDIte___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_box(0);
v___x_183_ = ((lean_object*)(l_reduceDIte___closed__3));
v___x_184_ = l_Lean_mkConst(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_reduceDIte___closed__9(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_box(0);
v___x_192_ = ((lean_object*)(l_reduceDIte___closed__8));
v___x_193_ = l_Lean_mkConst(v___x_192_, v___x_191_);
return v___x_193_;
}
}
lean_object* l_reduceDIte(lean_object* v_e_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_197_, v_a_202_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = l_Lean_Expr_cleanupAnnotations(v_a_210_);
v___x_212_ = l_Lean_Expr_isApp(v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v___x_211_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_arg_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc_ref(v_arg_213_);
v___x_214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_211_);
v___x_215_ = l_Lean_Expr_isApp(v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_213_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_arg_216_ = lean_ctor_get(v___x_214_, 1);
lean_inc_ref(v_arg_216_);
v___x_217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_214_);
v___x_218_ = l_Lean_Expr_isApp(v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___x_217_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_arg_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc_ref(v_arg_219_);
v___x_220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_217_);
v___x_221_ = l_Lean_Expr_isApp(v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v___x_220_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_arg_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc_ref(v_arg_222_);
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_220_);
v___x_224_ = l_Lean_Expr_isApp(v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v___x_223_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
goto v___jp_206_;
}
else
{
lean_object* v_arg_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_arg_225_ = lean_ctor_get(v___x_223_, 1);
lean_inc_ref(v_arg_225_);
v___x_226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_223_);
v___x_227_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_228_ = l_Lean_Expr_isConstOf(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
goto v___jp_206_;
}
else
{
lean_object* v___x_229_; 
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
lean_inc_ref(v_arg_222_);
v___x_229_ = lean_simp(v_arg_222_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_299_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_299_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_299_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_299_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_expr_234_; uint8_t v___x_235_; 
v_expr_234_ = lean_ctor_get(v_a_230_, 0);
lean_inc_ref(v_expr_234_);
v___x_235_ = l_Lean_Expr_isTrue(v_expr_234_);
if (v___x_235_ == 0)
{
uint8_t v___x_236_; 
lean_inc_ref(v_expr_234_);
v___x_236_ = l_Lean_Expr_isFalse(v_expr_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v_a_230_);
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
v___x_237_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_237_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_object* v___x_241_; 
lean_del_object(v___x_232_);
v___x_241_ = l_Lean_Meta_Simp_Result_getProof(v_a_230_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_261_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_246_ = lean_obj_once(&l_reduceDIte___closed__4, &l_reduceDIte___closed__4_once, _init_l_reduceDIte___closed__4);
lean_inc(v_a_242_);
lean_inc_ref(v_arg_222_);
v___x_247_ = l_Lean_mkAppB(v___x_246_, v_arg_222_, v_a_242_);
lean_inc_ref(v_arg_213_);
v___x_248_ = l_Lean_Expr_app___override(v_arg_213_, v___x_247_);
v___x_249_ = l_Lean_Expr_headBeta(v___x_248_);
v___x_250_ = ((lean_object*)(l_reduceDIte___closed__6));
v___x_251_ = l_Lean_Expr_constLevels_x21(v___x_226_);
lean_dec_ref(v___x_226_);
v___x_252_ = l_Lean_mkConst(v___x_250_, v___x_251_);
v___x_253_ = l_Lean_mkApp5(v___x_252_, v_arg_225_, v_arg_222_, v_arg_219_, v_arg_216_, v_arg_213_);
v___x_254_ = l_Lean_Expr_app___override(v___x_253_, v_a_242_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_256_, 0, v___x_249_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*2, v___x_228_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_257_);
v___x_259_ = v___x_244_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
v_a_262_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_241_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_241_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v___x_270_; 
lean_del_object(v___x_232_);
v___x_270_ = l_Lean_Meta_Simp_Result_getProof(v_a_230_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_290_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_290_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_290_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_290_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_275_ = lean_obj_once(&l_reduceDIte___closed__9, &l_reduceDIte___closed__9_once, _init_l_reduceDIte___closed__9);
lean_inc(v_a_271_);
lean_inc_ref(v_arg_222_);
v___x_276_ = l_Lean_mkAppB(v___x_275_, v_arg_222_, v_a_271_);
lean_inc_ref(v_arg_216_);
v___x_277_ = l_Lean_Expr_app___override(v_arg_216_, v___x_276_);
v___x_278_ = l_Lean_Expr_headBeta(v___x_277_);
v___x_279_ = ((lean_object*)(l_reduceDIte___closed__11));
v___x_280_ = l_Lean_Expr_constLevels_x21(v___x_226_);
lean_dec_ref(v___x_226_);
v___x_281_ = l_Lean_mkConst(v___x_279_, v___x_280_);
v___x_282_ = l_Lean_mkApp5(v___x_281_, v_arg_225_, v_arg_222_, v_arg_219_, v_arg_216_, v_arg_213_);
v___x_283_ = l_Lean_Expr_app___override(v___x_282_, v_a_271_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_285_, 0, v___x_278_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*2, v___x_228_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_286_);
v___x_288_ = v___x_273_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
v_a_291_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_270_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_270_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
lean_dec_ref(v_arg_222_);
lean_dec_ref(v_arg_219_);
lean_dec_ref(v_arg_216_);
lean_dec_ref(v_arg_213_);
v_a_300_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_229_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_229_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
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
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_209_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_209_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
v___jp_206_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT void l_reduceDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_197_ = stack[0].m_obj;
lean_object* v_a_198_ = stack[1].m_obj;
lean_object* v_a_199_ = stack[2].m_obj;
lean_object* v_a_200_ = stack[3].m_obj;
lean_object* v_a_201_ = stack[4].m_obj;
lean_object* v_a_202_ = stack[5].m_obj;
lean_object* v_a_203_ = stack[6].m_obj;
lean_object* v_a_204_ = stack[7].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_reduceDIte(v_e_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object* v_e_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_reduceDIte(v_e_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
return v_res_326_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_346_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_347_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_344_, v___x_345_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_348_;
v_res_348_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22____boxed(lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
return v_res_350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_355_ = 0;
v___x_356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_357_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_354_, v___x_355_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_358_;
v_res_358_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
return v_res_360_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_363_ = 0;
v___x_364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_365_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_362_, v___x_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_366_;
v_res_366_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26____boxed(lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
return v_res_368_;
}
}
lean_object* l_dreduceIte(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
uint8_t v_inDSimp_395_; 
v_inDSimp_395_ = lean_ctor_get_uint8(v_a_385_, sizeof(void*)*10 + 8);
if (v_inDSimp_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_e_383_);
v___x_396_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_383_, v_a_388_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Expr_cleanupAnnotations(v_a_399_);
v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v___x_400_);
goto v___jp_392_;
}
else
{
lean_object* v_arg_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_arg_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc_ref(v_arg_402_);
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_402_);
goto v___jp_392_;
}
else
{
lean_object* v_arg_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_arg_405_ = lean_ctor_get(v___x_403_, 1);
lean_inc_ref(v_arg_405_);
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_407_ = l_Lean_Expr_isApp(v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v___x_406_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_392_;
}
else
{
lean_object* v_arg_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_arg_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc_ref(v_arg_408_);
v___x_409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_406_);
v___x_410_ = l_Lean_Expr_isApp(v___x_409_);
if (v___x_410_ == 0)
{
lean_dec_ref(v___x_409_);
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_392_;
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
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_392_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_412_);
v___x_415_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_416_ = l_Lean_Expr_isConstOf(v___x_414_, v___x_415_);
lean_dec_ref(v___x_414_);
if (v___x_416_ == 0)
{
lean_dec_ref(v_arg_411_);
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
goto v___jp_392_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
v___x_417_ = lean_simp(v_arg_411_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_474_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_474_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_474_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_474_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_expr_467_; uint8_t v___x_468_; 
v_expr_467_ = lean_ctor_get(v_a_418_, 0);
lean_inc_ref_n(v_expr_467_, 2);
lean_dec(v_a_418_);
v___x_468_ = l_Lean_Expr_isTrue(v_expr_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_Expr_isFalse(v_expr_467_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
v___x_470_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_470_);
v___x_472_ = v___x_420_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
else
{
lean_del_object(v___x_420_);
goto v___jp_422_;
}
}
else
{
lean_dec_ref(v_expr_467_);
lean_del_object(v___x_420_);
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Lean_Expr_proj___override(v___x_423_, v___x_424_, v_arg_408_);
v___x_426_ = l_Lean_Meta_whnfD(v___x_425_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_427_, v_a_388_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_450_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_450_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_450_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_450_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = l_Lean_Expr_cleanupAnnotations(v_a_429_);
v___x_434_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_435_ = l_Lean_Expr_isConstOf(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
lean_dec_ref(v_arg_402_);
v___x_436_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_437_ = l_Lean_Expr_isConstOf(v___x_433_, v___x_436_);
lean_dec_ref(v___x_433_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec_ref(v_arg_405_);
v___x_438_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_438_);
v___x_440_ = v___x_431_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_arg_405_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_442_);
v___x_444_ = v___x_431_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec_ref(v___x_433_);
lean_dec_ref(v_arg_405_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_arg_402_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_446_);
v___x_448_ = v___x_431_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
v_a_451_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_428_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_428_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
v_a_459_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_426_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_426_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_arg_405_);
lean_dec_ref(v_arg_402_);
v_a_475_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_417_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_417_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
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
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_398_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_398_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT void l_dreduceIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_383_ = stack[0].m_obj;
lean_object* v_a_384_ = stack[1].m_obj;
lean_object* v_a_385_ = stack[2].m_obj;
lean_object* v_a_386_ = stack[3].m_obj;
lean_object* v_a_387_ = stack[4].m_obj;
lean_object* v_a_388_ = stack[5].m_obj;
lean_object* v_a_389_ = stack[6].m_obj;
lean_object* v_a_390_ = stack[7].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_dreduceIte(v_e_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* v_e_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_dreduceIte(v_e_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
return v_res_501_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_508_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_509_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_510_;
v_res_510_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22____boxed(lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
return v_res_512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_517_ = 0;
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_519_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_516_, v___x_517_, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_520_;
v_res_520_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24____boxed(lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
return v_res_522_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_525_ = 0;
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_527_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_524_, v___x_525_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_528_;
v_res_528_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26____boxed(lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
return v_res_530_;
}
}
lean_object* l_dreduceDIte(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
uint8_t v_inDSimp_543_; 
v_inDSimp_543_ = lean_ctor_get_uint8(v_a_533_, sizeof(void*)*10 + 8);
if (v_inDSimp_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_e_531_);
v___x_544_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_531_, v_a_536_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = l_Lean_Expr_cleanupAnnotations(v_a_547_);
v___x_549_ = l_Lean_Expr_isApp(v___x_548_);
if (v___x_549_ == 0)
{
lean_dec_ref(v___x_548_);
goto v___jp_540_;
}
else
{
lean_object* v_arg_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_arg_550_ = lean_ctor_get(v___x_548_, 1);
lean_inc_ref(v_arg_550_);
v___x_551_ = l_Lean_Expr_appFnCleanup___redArg(v___x_548_);
v___x_552_ = l_Lean_Expr_isApp(v___x_551_);
if (v___x_552_ == 0)
{
lean_dec_ref(v___x_551_);
lean_dec_ref(v_arg_550_);
goto v___jp_540_;
}
else
{
lean_object* v_arg_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_arg_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc_ref(v_arg_553_);
v___x_554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_551_);
v___x_555_ = l_Lean_Expr_isApp(v___x_554_);
if (v___x_555_ == 0)
{
lean_dec_ref(v___x_554_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
goto v___jp_540_;
}
else
{
lean_object* v_arg_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_arg_556_ = lean_ctor_get(v___x_554_, 1);
lean_inc_ref(v_arg_556_);
v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_554_);
v___x_558_ = l_Lean_Expr_isApp(v___x_557_);
if (v___x_558_ == 0)
{
lean_dec_ref(v___x_557_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
goto v___jp_540_;
}
else
{
lean_object* v_arg_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_arg_559_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_arg_559_);
v___x_560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_557_);
v___x_561_ = l_Lean_Expr_isApp(v___x_560_);
if (v___x_561_ == 0)
{
lean_dec_ref(v___x_560_);
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
goto v___jp_540_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_560_);
v___x_563_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_564_ = l_Lean_Expr_isConstOf(v___x_562_, v___x_563_);
lean_dec_ref(v___x_562_);
if (v___x_564_ == 0)
{
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
goto v___jp_540_;
}
else
{
lean_object* v___x_565_; 
lean_inc(v_a_538_);
lean_inc_ref(v_a_537_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_arg_559_);
v___x_565_ = lean_simp(v_arg_559_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_633_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_633_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_633_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_633_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_expr_626_; uint8_t v___x_627_; 
v_expr_626_ = lean_ctor_get(v_a_566_, 0);
lean_inc_ref_n(v_expr_626_, 2);
lean_dec(v_a_566_);
v___x_627_ = l_Lean_Expr_isTrue(v_expr_626_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = l_Lean_Expr_isFalse(v_expr_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
v___x_629_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_629_);
v___x_631_ = v___x_568_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_del_object(v___x_568_);
goto v___jp_570_;
}
}
else
{
lean_dec_ref(v_expr_626_);
lean_del_object(v___x_568_);
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_572_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_arg_556_);
v___x_573_ = l_Lean_Expr_proj___override(v___x_571_, v___x_572_, v_arg_556_);
v___x_574_ = l_Lean_Meta_whnfD(v___x_573_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_575_, v_a_536_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_609_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_609_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = l_Lean_Expr_cleanupAnnotations(v_a_577_);
v___x_582_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_583_ = l_Lean_Expr_isConstOf(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; uint8_t v___x_585_; 
lean_dec_ref(v_arg_550_);
v___x_584_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_585_ = l_Lean_Expr_isConstOf(v___x_581_, v___x_584_);
lean_dec_ref(v___x_581_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
v___x_586_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_586_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = l_Lean_Expr_proj___override(v___x_571_, v___x_590_, v_arg_556_);
v___x_592_ = l_Lean_Meta_mkExpectedPropHint(v___x_591_, v_arg_559_);
v___x_593_ = l_Lean_Expr_app___override(v_arg_553_, v___x_592_);
v___x_594_ = l_Lean_Expr_headBeta(v___x_593_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_595_);
v___x_597_ = v___x_579_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec_ref(v___x_581_);
lean_dec_ref(v_arg_553_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = l_Lean_Expr_proj___override(v___x_571_, v___x_599_, v_arg_556_);
v___x_601_ = l_Lean_mkNot(v_arg_559_);
v___x_602_ = l_Lean_Meta_mkExpectedPropHint(v___x_600_, v___x_601_);
v___x_603_ = l_Lean_Expr_app___override(v_arg_550_, v___x_602_);
v___x_604_ = l_Lean_Expr_headBeta(v___x_603_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_605_);
v___x_607_ = v___x_579_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
v_a_610_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_576_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_576_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
v_a_618_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_574_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_574_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_arg_559_);
lean_dec_ref(v_arg_556_);
lean_dec_ref(v_arg_553_);
lean_dec_ref(v_arg_550_);
v_a_634_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_565_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_565_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
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
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_546_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_546_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT void l_dreduceDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_531_ = stack[0].m_obj;
lean_object* v_a_532_ = stack[1].m_obj;
lean_object* v_a_533_ = stack[2].m_obj;
lean_object* v_a_534_ = stack[3].m_obj;
lean_object* v_a_535_ = stack[4].m_obj;
lean_object* v_a_536_ = stack[5].m_obj;
lean_object* v_a_537_ = stack[6].m_obj;
lean_object* v_a_538_ = stack[7].m_obj;
lean_object* v_res_650_;
v_res_650_ = l_dreduceDIte(v_e_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* v_e_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_dreduceDIte(v_e_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
return v_res_660_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_667_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_668_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_665_, v___x_666_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_669_;
v_res_669_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22____boxed(lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
return v_res_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_676_ = 0;
v___x_677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_678_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_675_, v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_679_;
v_res_679_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24____boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
return v_res_681_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_684_ = 0;
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_686_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_683_, v___x_684_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_687_;
v_res_687_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26____boxed(lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
return v_res_689_;
}
}
lean_object* l_reduceCtorEq___lam__0(lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT void l_reduceCtorEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_690_ = stack[0].m_obj;
lean_object* v___y_691_ = stack[1].m_obj;
lean_object* v___y_692_ = stack[2].m_obj;
lean_object* v___y_693_ = stack[3].m_obj;
lean_object* v___y_694_ = stack[4].m_obj;
lean_object* v___y_695_ = stack[5].m_obj;
lean_object* v___y_696_ = stack[6].m_obj;
lean_object* v___y_697_ = stack[7].m_obj;
lean_object* v_res_701_;
v_res_701_ = l_reduceCtorEq___lam__0(v_x_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_reduceCtorEq___lam__0(v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
return v_res_711_;
}
}
lean_object* l_reduceCtorEq___lam__1(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT void l_reduceCtorEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_712_ = stack[0].m_obj;
lean_object* v_x_713_ = stack[1].m_obj;
lean_object* v___y_714_ = stack[2].m_obj;
lean_object* v___y_715_ = stack[3].m_obj;
lean_object* v___y_716_ = stack[4].m_obj;
lean_object* v___y_717_ = stack[5].m_obj;
lean_object* v___y_718_ = stack[6].m_obj;
lean_object* v___y_719_ = stack[7].m_obj;
lean_object* v___y_720_ = stack[8].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_reduceCtorEq___lam__1(v_x_712_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_reduceCtorEq___lam__1(v_x_725_, v_x_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec(v_x_726_);
lean_dec(v_x_725_);
return v_res_735_;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
return v___x_741_;
}
}
lean_object* l_reduceCtorEq___lam__2(uint8_t v___x_742_, uint8_t v___x_743_, lean_object* v_h_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; lean_object* v___y_755_; lean_object* v___x_775_; 
v___x_753_ = lean_obj_once(&l_reduceCtorEq___lam__2___closed__2, &l_reduceCtorEq___lam__2___closed__2_once, _init_l_reduceCtorEq___lam__2___closed__2);
lean_inc_ref(v_h_744_);
v___x_775_ = l_Lean_Meta_mkNoConfusion(v___x_753_, v_h_744_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_mk_empty_array_with_capacity(v___x_777_);
v___x_779_ = lean_array_push(v___x_778_, v_h_744_);
v___x_780_ = 1;
v___x_781_ = l_Lean_Meta_mkLambdaFVars(v___x_779_, v_a_776_, v___x_743_, v___x_742_, v___x_743_, v___x_742_, v___x_780_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec_ref(v___x_779_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; uint8_t v_transparency_784_; uint8_t v___x_785_; uint8_t v___x_786_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Meta_Context_config(v___y_748_);
v_transparency_784_ = lean_ctor_get_uint8(v___x_783_, 9);
lean_dec_ref(v___x_783_);
v___x_785_ = 1;
v___x_786_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v_keyedConfig_787_; uint8_t v_trackZetaDelta_788_; lean_object* v_zetaDeltaSet_789_; lean_object* v_lctx_790_; lean_object* v_localInstances_791_; lean_object* v_defEqCtx_x3f_792_; lean_object* v_synthPendingDepth_793_; lean_object* v_customCanUnfoldPredicate_x3f_794_; uint8_t v_univApprox_795_; uint8_t v_inTypeClassResolution_796_; uint8_t v_cacheInferType_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_keyedConfig_787_ = lean_ctor_get(v___y_748_, 0);
v_trackZetaDelta_788_ = lean_ctor_get_uint8(v___y_748_, sizeof(void*)*7);
v_zetaDeltaSet_789_ = lean_ctor_get(v___y_748_, 1);
v_lctx_790_ = lean_ctor_get(v___y_748_, 2);
v_localInstances_791_ = lean_ctor_get(v___y_748_, 3);
v_defEqCtx_x3f_792_ = lean_ctor_get(v___y_748_, 4);
v_synthPendingDepth_793_ = lean_ctor_get(v___y_748_, 5);
v_customCanUnfoldPredicate_x3f_794_ = lean_ctor_get(v___y_748_, 6);
v_univApprox_795_ = lean_ctor_get_uint8(v___y_748_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_796_ = lean_ctor_get_uint8(v___y_748_, sizeof(void*)*7 + 2);
v_cacheInferType_797_ = lean_ctor_get_uint8(v___y_748_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_787_);
v___x_798_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_785_, v_keyedConfig_787_);
lean_inc(v_customCanUnfoldPredicate_x3f_794_);
lean_inc(v_synthPendingDepth_793_);
lean_inc(v_defEqCtx_x3f_792_);
lean_inc_ref(v_localInstances_791_);
lean_inc_ref(v_lctx_790_);
lean_inc(v_zetaDeltaSet_789_);
v___x_799_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_zetaDeltaSet_789_);
lean_ctor_set(v___x_799_, 2, v_lctx_790_);
lean_ctor_set(v___x_799_, 3, v_localInstances_791_);
lean_ctor_set(v___x_799_, 4, v_defEqCtx_x3f_792_);
lean_ctor_set(v___x_799_, 5, v_synthPendingDepth_793_);
lean_ctor_set(v___x_799_, 6, v_customCanUnfoldPredicate_x3f_794_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*7, v_trackZetaDelta_788_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*7 + 1, v_univApprox_795_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*7 + 2, v_inTypeClassResolution_796_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*7 + 3, v_cacheInferType_797_);
v___x_800_ = l_Lean_Meta_mkEqFalse_x27(v_a_782_, v___x_799_, v___y_749_, v___y_750_, v___y_751_);
lean_dec_ref_known(v___x_799_, 7);
v___y_755_ = v___x_800_;
goto v___jp_754_;
}
else
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_mkEqFalse_x27(v_a_782_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
v___y_755_ = v___x_801_;
goto v___jp_754_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_781_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_781_);
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
lean_dec_ref(v_h_744_);
v_a_810_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_775_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_775_);
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
v___jp_754_:
{
if (lean_obj_tag(v___y_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_766_; 
v_a_756_ = lean_ctor_get(v___y_755_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_766_ == 0)
{
v___x_758_ = v___y_755_;
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___y_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v_a_756_);
v___x_761_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_761_, 0, v___x_753_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*2, v___x_742_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_762_);
v___x_764_ = v___x_758_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_767_ = lean_ctor_get(v___y_755_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___y_755_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___y_755_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___y_755_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT void l_reduceCtorEq___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_742_ = stack[0].m_num;
uint8_t v___x_743_ = stack[1].m_num;
lean_object* v_h_744_ = stack[2].m_obj;
lean_object* v___y_745_ = stack[3].m_obj;
lean_object* v___y_746_ = stack[4].m_obj;
lean_object* v___y_747_ = stack[5].m_obj;
lean_object* v___y_748_ = stack[6].m_obj;
lean_object* v___y_749_ = stack[7].m_obj;
lean_object* v___y_750_ = stack[8].m_obj;
lean_object* v___y_751_ = stack[9].m_obj;
lean_object* v_res_818_;
v_res_818_ = l_reduceCtorEq___lam__2(v___x_742_, v___x_743_, v_h_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* v___x_819_, lean_object* v___x_820_, lean_object* v_h_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_18342__boxed_830_; uint8_t v___x_18343__boxed_831_; lean_object* v_res_832_; 
v___x_18342__boxed_830_ = lean_unbox(v___x_819_);
v___x_18343__boxed_831_ = lean_unbox(v___x_820_);
v_res_832_ = l_reduceCtorEq___lam__2(v___x_18342__boxed_830_, v___x_18343__boxed_831_, v_h_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
return v_res_832_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
v___x_843_ = lean_apply_9(v_k_833_, v_b_837_, v___y_834_, v___y_835_, v___y_836_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, lean_box(0));
return v___x_843_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_833_ = stack[0].m_obj;
lean_object* v___y_834_ = stack[1].m_obj;
lean_object* v___y_835_ = stack[2].m_obj;
lean_object* v___y_836_ = stack[3].m_obj;
lean_object* v_b_837_ = stack[4].m_obj;
lean_object* v___y_838_ = stack[5].m_obj;
lean_object* v___y_839_ = stack[6].m_obj;
lean_object* v___y_840_ = stack[7].m_obj;
lean_object* v___y_841_ = stack[8].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_833_, v___y_834_, v___y_835_, v___y_836_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v_b_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_845_, v___y_846_, v___y_847_, v___y_848_, v_b_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
return v_res_855_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_856_, uint8_t v_bi_857_, lean_object* v_type_858_, lean_object* v_k_859_, uint8_t v_kind_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___f_869_; lean_object* v___x_870_; 
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_869_, 0, v_k_859_);
lean_closure_set(v___f_869_, 1, v___y_861_);
lean_closure_set(v___f_869_, 2, v___y_862_);
lean_closure_set(v___f_869_, 3, v___y_863_);
v___x_870_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_856_, v_bi_857_, v_type_858_, v___f_869_, v_kind_860_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_870_) == 0)
{
return v___x_870_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_856_ = stack[0].m_obj;
uint8_t v_bi_857_ = stack[1].m_num;
lean_object* v_type_858_ = stack[2].m_obj;
lean_object* v_k_859_ = stack[3].m_obj;
uint8_t v_kind_860_ = stack[4].m_num;
lean_object* v___y_861_ = stack[5].m_obj;
lean_object* v___y_862_ = stack[6].m_obj;
lean_object* v___y_863_ = stack[7].m_obj;
lean_object* v___y_864_ = stack[8].m_obj;
lean_object* v___y_865_ = stack[9].m_obj;
lean_object* v___y_866_ = stack[10].m_obj;
lean_object* v___y_867_ = stack[11].m_obj;
lean_object* v_res_879_;
v_res_879_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_856_, v_bi_857_, v_type_858_, v_k_859_, v_kind_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_880_, lean_object* v_bi_881_, lean_object* v_type_882_, lean_object* v_k_883_, lean_object* v_kind_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v_bi_boxed_893_; uint8_t v_kind_boxed_894_; lean_object* v_res_895_; 
v_bi_boxed_893_ = lean_unbox(v_bi_881_);
v_kind_boxed_894_ = lean_unbox(v_kind_884_);
v_res_895_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_880_, v_bi_boxed_893_, v_type_882_, v_k_883_, v_kind_boxed_894_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
return v_res_895_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* v_name_896_, lean_object* v_type_897_, lean_object* v_k_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = 0;
v___x_908_ = 0;
v___x_909_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_896_, v___x_907_, v_type_897_, v_k_898_, v___x_908_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_909_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_896_ = stack[0].m_obj;
lean_object* v_type_897_ = stack[1].m_obj;
lean_object* v_k_898_ = stack[2].m_obj;
lean_object* v___y_899_ = stack[3].m_obj;
lean_object* v___y_900_ = stack[4].m_obj;
lean_object* v___y_901_ = stack[5].m_obj;
lean_object* v___y_902_ = stack[6].m_obj;
lean_object* v___y_903_ = stack[7].m_obj;
lean_object* v___y_904_ = stack[8].m_obj;
lean_object* v___y_905_ = stack[9].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_896_, v_type_897_, v_k_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_911_, lean_object* v_type_912_, lean_object* v_k_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_911_, v_type_912_, v_k_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
return v_res_922_;
}
}
lean_object* l_reduceCtorEq(lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___y_939_; lean_object* v___x_948_; uint8_t v_transparency_949_; uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_948_ = l_Lean_Meta_Context_config(v_a_933_);
v_transparency_949_ = lean_ctor_get_uint8(v___x_948_, 9);
lean_dec_ref(v___x_948_);
v___x_950_ = 3;
v___x_951_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v_keyedConfig_952_; uint8_t v_trackZetaDelta_953_; lean_object* v_zetaDeltaSet_954_; lean_object* v_lctx_955_; lean_object* v_localInstances_956_; lean_object* v_defEqCtx_x3f_957_; lean_object* v_synthPendingDepth_958_; lean_object* v_customCanUnfoldPredicate_x3f_959_; uint8_t v_univApprox_960_; uint8_t v_inTypeClassResolution_961_; uint8_t v_cacheInferType_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_keyedConfig_952_ = lean_ctor_get(v_a_933_, 0);
v_trackZetaDelta_953_ = lean_ctor_get_uint8(v_a_933_, sizeof(void*)*7);
v_zetaDeltaSet_954_ = lean_ctor_get(v_a_933_, 1);
v_lctx_955_ = lean_ctor_get(v_a_933_, 2);
v_localInstances_956_ = lean_ctor_get(v_a_933_, 3);
v_defEqCtx_x3f_957_ = lean_ctor_get(v_a_933_, 4);
v_synthPendingDepth_958_ = lean_ctor_get(v_a_933_, 5);
v_customCanUnfoldPredicate_x3f_959_ = lean_ctor_get(v_a_933_, 6);
v_univApprox_960_ = lean_ctor_get_uint8(v_a_933_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_961_ = lean_ctor_get_uint8(v_a_933_, sizeof(void*)*7 + 2);
v_cacheInferType_962_ = lean_ctor_get_uint8(v_a_933_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_952_);
v___x_963_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_950_, v_keyedConfig_952_);
lean_inc(v_customCanUnfoldPredicate_x3f_959_);
lean_inc(v_synthPendingDepth_958_);
lean_inc(v_defEqCtx_x3f_957_);
lean_inc_ref(v_localInstances_956_);
lean_inc_ref(v_lctx_955_);
lean_inc(v_zetaDeltaSet_954_);
v___x_964_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_zetaDeltaSet_954_);
lean_ctor_set(v___x_964_, 2, v_lctx_955_);
lean_ctor_set(v___x_964_, 3, v_localInstances_956_);
lean_ctor_set(v___x_964_, 4, v_defEqCtx_x3f_957_);
lean_ctor_set(v___x_964_, 5, v_synthPendingDepth_958_);
lean_ctor_set(v___x_964_, 6, v_customCanUnfoldPredicate_x3f_959_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7, v_trackZetaDelta_953_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 1, v_univApprox_960_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 2, v_inTypeClassResolution_961_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 3, v_cacheInferType_962_);
lean_inc_ref(v_e_929_);
v___x_965_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_929_, v_a_934_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Expr_cleanupAnnotations(v_a_966_);
v___x_968_ = l_Lean_Expr_isApp(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref(v___x_967_);
lean_dec_ref(v_e_929_);
v___x_969_ = lean_box(0);
v___x_970_ = l_reduceCtorEq___lam__0(v___x_969_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
v___y_939_ = v___x_970_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_arg_971_ = lean_ctor_get(v___x_967_, 1);
lean_inc_ref(v_arg_971_);
v___x_972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_967_);
v___x_973_ = l_Lean_Expr_isApp(v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v_arg_971_);
lean_dec_ref(v_e_929_);
v___x_974_ = lean_box(0);
v___x_975_ = l_reduceCtorEq___lam__0(v___x_974_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
v___y_939_ = v___x_975_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_arg_976_ = lean_ctor_get(v___x_972_, 1);
lean_inc_ref(v_arg_976_);
v___x_977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_972_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v___x_977_);
lean_dec_ref(v_arg_976_);
lean_dec_ref(v_arg_971_);
lean_dec_ref(v_e_929_);
v___x_979_ = lean_box(0);
v___x_980_ = l_reduceCtorEq___lam__0(v___x_979_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
v___y_939_ = v___x_980_;
goto v___jp_938_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_977_);
v___x_982_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_983_ = l_Lean_Expr_isConstOf(v___x_981_, v___x_982_);
lean_dec_ref(v___x_981_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v_arg_976_);
lean_dec_ref(v_arg_971_);
lean_dec_ref(v_e_929_);
v___x_984_ = lean_box(0);
v___x_985_ = l_reduceCtorEq___lam__0(v___x_984_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
v___y_939_ = v___x_985_;
goto v___jp_938_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v___x_986_ = lean_box(v___x_983_);
v___x_987_ = lean_box(v___x_951_);
v___f_988_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_988_, 0, v___x_986_);
lean_closure_set(v___f_988_, 1, v___x_987_);
v___x_989_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_976_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_971_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1015_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1015_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1015_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___y_997_; 
if (lean_obj_tag(v_a_990_) == 1)
{
if (lean_obj_tag(v_a_992_) == 1)
{
lean_object* v_val_1004_; lean_object* v_val_1005_; lean_object* v_fst_1006_; lean_object* v_toConstantVal_1007_; lean_object* v_fst_1008_; lean_object* v_toConstantVal_1009_; lean_object* v_name_1010_; lean_object* v_name_1011_; uint8_t v___x_1012_; 
v_val_1004_ = lean_ctor_get(v_a_990_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_a_990_, 1);
v_val_1005_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_a_992_, 1);
v_fst_1006_ = lean_ctor_get(v_val_1004_, 0);
lean_inc(v_fst_1006_);
lean_dec(v_val_1004_);
v_toConstantVal_1007_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc_ref(v_toConstantVal_1007_);
lean_dec(v_fst_1006_);
v_fst_1008_ = lean_ctor_get(v_val_1005_, 0);
lean_inc(v_fst_1008_);
lean_dec(v_val_1005_);
v_toConstantVal_1009_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc_ref(v_toConstantVal_1009_);
lean_dec(v_fst_1008_);
v_name_1010_ = lean_ctor_get(v_toConstantVal_1007_, 0);
lean_inc(v_name_1010_);
lean_dec_ref(v_toConstantVal_1007_);
v_name_1011_ = lean_ctor_get(v_toConstantVal_1009_, 0);
lean_inc(v_name_1011_);
lean_dec_ref(v_toConstantVal_1009_);
v___x_1012_ = lean_name_eq(v_name_1010_, v_name_1011_);
lean_dec(v_name_1011_);
lean_dec(v_name_1010_);
if (v___x_1012_ == 0)
{
v___y_997_ = v___x_983_;
goto v___jp_996_;
}
else
{
v___y_997_ = v___x_951_;
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1013_; 
lean_del_object(v___x_994_);
lean_dec_ref(v___f_988_);
lean_dec_ref(v_e_929_);
v___x_1013_ = l_reduceCtorEq___lam__1(v_a_990_, v_a_992_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
lean_dec(v_a_992_);
lean_dec_ref_known(v_a_990_, 1);
v___y_939_ = v___x_1013_;
goto v___jp_938_;
}
}
else
{
lean_object* v___x_1014_; 
lean_del_object(v___x_994_);
lean_dec_ref(v___f_988_);
lean_dec_ref(v_e_929_);
v___x_1014_ = l_reduceCtorEq___lam__1(v_a_990_, v_a_992_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
lean_dec(v_a_992_);
lean_dec(v_a_990_);
v___y_939_ = v___x_1014_;
goto v___jp_938_;
}
v___jp_996_:
{
if (v___y_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_dec_ref(v___f_988_);
lean_dec_ref_known(v___x_964_, 7);
lean_dec_ref(v_e_929_);
v___x_998_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_998_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_del_object(v___x_994_);
v___x_1002_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_1003_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1002_, v_e_929_, v___f_988_, v_a_930_, v_a_931_, v_a_932_, v___x_964_, v_a_934_, v_a_935_, v_a_936_);
lean_dec_ref_known(v___x_964_, 7);
v___y_939_ = v___x_1003_;
goto v___jp_938_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_990_);
lean_dec_ref(v___f_988_);
lean_dec_ref_known(v___x_964_, 7);
lean_dec_ref(v_e_929_);
v_a_1016_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_991_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_991_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v___f_988_);
lean_dec_ref(v_arg_971_);
lean_dec_ref_known(v___x_964_, 7);
lean_dec_ref(v_e_929_);
v_a_1024_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_989_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_989_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
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
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref_known(v___x_964_, 7);
lean_dec_ref(v_e_929_);
v_a_1032_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_965_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_965_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1040_; 
lean_inc_ref(v_e_929_);
v___x_1040_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_929_, v_a_934_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = l_Lean_Expr_cleanupAnnotations(v_a_1041_);
v___x_1043_ = l_Lean_Expr_isApp(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_e_929_);
v___x_1044_ = lean_box(0);
v___x_1045_ = l_reduceCtorEq___lam__0(v___x_1044_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
v___y_939_ = v___x_1045_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_arg_1046_ = lean_ctor_get(v___x_1042_, 1);
lean_inc_ref(v_arg_1046_);
v___x_1047_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1042_);
v___x_1048_ = l_Lean_Expr_isApp(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_arg_1046_);
lean_dec_ref(v_e_929_);
v___x_1049_ = lean_box(0);
v___x_1050_ = l_reduceCtorEq___lam__0(v___x_1049_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
v___y_939_ = v___x_1050_;
goto v___jp_938_;
}
else
{
lean_object* v_arg_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_arg_1051_ = lean_ctor_get(v___x_1047_, 1);
lean_inc_ref(v_arg_1051_);
v___x_1052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1047_);
v___x_1053_ = l_Lean_Expr_isApp(v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1046_);
lean_dec_ref(v_e_929_);
v___x_1054_ = lean_box(0);
v___x_1055_ = l_reduceCtorEq___lam__0(v___x_1054_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
v___y_939_ = v___x_1055_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1052_);
v___x_1057_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_1058_ = l_Lean_Expr_isConstOf(v___x_1056_, v___x_1057_);
lean_dec_ref(v___x_1056_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1046_);
lean_dec_ref(v_e_929_);
v___x_1059_ = lean_box(0);
v___x_1060_ = l_reduceCtorEq___lam__0(v___x_1059_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
v___y_939_ = v___x_1060_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1051_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1063_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1046_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_1063_) == 0)
{
if (lean_obj_tag(v_a_1062_) == 1)
{
lean_object* v_val_1064_; lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1087_; 
v_val_1064_ = lean_ctor_get(v_a_1062_, 0);
v_a_1065_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1087_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1087_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1069_; lean_object* v_fst_1070_; lean_object* v_toConstantVal_1071_; lean_object* v_fst_1072_; lean_object* v_toConstantVal_1073_; lean_object* v_name_1074_; lean_object* v_name_1075_; uint8_t v___x_1076_; 
lean_inc(v_val_1064_);
lean_dec_ref_known(v_a_1062_, 1);
v_val_1069_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_a_1065_, 1);
v_fst_1070_ = lean_ctor_get(v_val_1064_, 0);
lean_inc(v_fst_1070_);
lean_dec(v_val_1064_);
v_toConstantVal_1071_ = lean_ctor_get(v_fst_1070_, 0);
lean_inc_ref(v_toConstantVal_1071_);
lean_dec(v_fst_1070_);
v_fst_1072_ = lean_ctor_get(v_val_1069_, 0);
lean_inc(v_fst_1072_);
lean_dec(v_val_1069_);
v_toConstantVal_1073_ = lean_ctor_get(v_fst_1072_, 0);
lean_inc_ref(v_toConstantVal_1073_);
lean_dec(v_fst_1072_);
v_name_1074_ = lean_ctor_get(v_toConstantVal_1071_, 0);
lean_inc(v_name_1074_);
lean_dec_ref(v_toConstantVal_1071_);
v_name_1075_ = lean_ctor_get(v_toConstantVal_1073_, 0);
lean_inc(v_name_1075_);
lean_dec_ref(v_toConstantVal_1073_);
v___x_1076_ = lean_name_eq(v_name_1074_, v_name_1075_);
lean_dec(v_name_1075_);
lean_dec(v_name_1074_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_del_object(v___x_1067_);
v___x_1077_ = lean_box(v___x_1058_);
v___x_1078_ = lean_box(v___x_1076_);
v___f_1079_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1079_, 0, v___x_1077_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
v___x_1080_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_1081_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1080_, v_e_929_, v___f_1079_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
v___y_939_ = v___x_1081_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec_ref(v_e_929_);
v___x_1082_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1082_);
v___x_1084_ = v___x_1067_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v___x_1086_; 
lean_del_object(v___x_1067_);
lean_dec_ref(v_e_929_);
v___x_1086_ = l_reduceCtorEq___lam__1(v_a_1062_, v_a_1065_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_1065_);
lean_dec_ref_known(v_a_1062_, 1);
v___y_939_ = v___x_1086_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_e_929_);
v_a_1088_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1089_ = l_reduceCtorEq___lam__1(v_a_1062_, v_a_1088_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_1088_);
lean_dec(v_a_1062_);
v___y_939_ = v___x_1089_;
goto v___jp_938_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_e_929_);
v_a_1090_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1063_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1063_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_arg_1046_);
lean_dec_ref(v_e_929_);
v_a_1098_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1061_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1061_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
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
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_e_929_);
v_a_1106_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1040_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1040_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_938_:
{
if (lean_obj_tag(v___y_939_) == 0)
{
return v___y_939_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___y_939_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___y_939_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___y_939_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___y_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT void l_reduceCtorEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_929_ = stack[0].m_obj;
lean_object* v_a_930_ = stack[1].m_obj;
lean_object* v_a_931_ = stack[2].m_obj;
lean_object* v_a_932_ = stack[3].m_obj;
lean_object* v_a_933_ = stack[4].m_obj;
lean_object* v_a_934_ = stack[5].m_obj;
lean_object* v_a_935_ = stack[6].m_obj;
lean_object* v_a_936_ = stack[7].m_obj;
lean_object* v_res_1114_;
v_res_1114_ = l_reduceCtorEq(v_e_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
stack->m_obj
 = v_res_1114_;
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_reduceCtorEq(v_e_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
return v_res_1124_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_1125_, lean_object* v_name_1126_, uint8_t v_bi_1127_, lean_object* v_type_1128_, lean_object* v_k_1129_, uint8_t v_kind_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_1126_, v_bi_1127_, v_type_1128_, v_k_1129_, v_kind_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1126_ = stack[1].m_obj;
uint8_t v_bi_1127_ = stack[2].m_num;
lean_object* v_type_1128_ = stack[3].m_obj;
lean_object* v_k_1129_ = stack[4].m_obj;
uint8_t v_kind_1130_ = stack[5].m_num;
lean_object* v___y_1131_ = stack[6].m_obj;
lean_object* v___y_1132_ = stack[7].m_obj;
lean_object* v___y_1133_ = stack[8].m_obj;
lean_object* v___y_1134_ = stack[9].m_obj;
lean_object* v___y_1135_ = stack[10].m_obj;
lean_object* v___y_1136_ = stack[11].m_obj;
lean_object* v___y_1137_ = stack[12].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_box(0), v_name_1126_, v_bi_1127_, v_type_1128_, v_k_1129_, v_kind_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_name_1142_, lean_object* v_bi_1143_, lean_object* v_type_1144_, lean_object* v_k_1145_, lean_object* v_kind_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v_bi_boxed_1155_; uint8_t v_kind_boxed_1156_; lean_object* v_res_1157_; 
v_bi_boxed_1155_ = lean_unbox(v_bi_1143_);
v_kind_boxed_1156_ = lean_unbox(v_kind_1146_);
v_res_1157_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_1141_, v_name_1142_, v_bi_boxed_1155_, v_type_1144_, v_k_1145_, v_kind_boxed_1156_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
return v_res_1157_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* v_00_u03b1_1158_, lean_object* v_name_1159_, lean_object* v_type_1160_, lean_object* v_k_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_1159_, v_type_1160_, v_k_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1159_ = stack[1].m_obj;
lean_object* v_type_1160_ = stack[2].m_obj;
lean_object* v_k_1161_ = stack[3].m_obj;
lean_object* v___y_1162_ = stack[4].m_obj;
lean_object* v___y_1163_ = stack[5].m_obj;
lean_object* v___y_1164_ = stack[6].m_obj;
lean_object* v___y_1165_ = stack[7].m_obj;
lean_object* v___y_1166_ = stack[8].m_obj;
lean_object* v___y_1167_ = stack[9].m_obj;
lean_object* v___y_1168_ = stack[10].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_box(0), v_name_1159_, v_type_1160_, v_k_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_name_1173_, lean_object* v_type_1174_, lean_object* v_k_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(v_00_u03b1_1172_, v_name_1173_, v_type_1174_, v_k_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
return v_res_1184_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1202_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1203_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1200_, v___x_1201_, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1204_;
v_res_1204_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23____boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
return v_res_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1211_ = 1;
v___x_1212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1213_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1210_, v___x_1211_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1214_;
v_res_1214_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25____boxed(lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
return v_res_1216_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1219_ = 1;
v___x_1220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1221_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1218_, v___x_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1222_;
v_res_1222_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
stack->m_obj
 = v_res_1222_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27____boxed(lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
return v_res_1224_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
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
