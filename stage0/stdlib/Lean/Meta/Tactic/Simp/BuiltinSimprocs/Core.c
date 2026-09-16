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
LEAN_EXPORT lean_object* l_reduceIte(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
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
LEAN_EXPORT lean_object* l_reduceIte___boxed(lean_object* v_e_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_reduceIte(v_e_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_152_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_153_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_150_, v___x_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22____boxed(lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
return v_res_155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_160_ = 0;
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_162_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_159_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24____boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_167_ = 0;
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_169_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_166_, v___x_167_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26____boxed(lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
return v_res_171_;
}
}
static lean_object* _init_l_reduceDIte___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_reduceDIte___closed__3));
v___x_180_ = l_Lean_mkConst(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_reduceDIte___closed__9(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l_reduceDIte___closed__8));
v___x_189_ = l_Lean_mkConst(v___x_188_, v___x_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_reduceDIte(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_193_, v_a_198_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v___x_207_ = l_Lean_Expr_cleanupAnnotations(v_a_206_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v___x_207_);
goto v___jp_202_;
}
else
{
lean_object* v_arg_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_arg_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc_ref(v_arg_209_);
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = l_Lean_Expr_isApp(v___x_210_);
if (v___x_211_ == 0)
{
lean_dec_ref(v___x_210_);
lean_dec_ref(v_arg_209_);
goto v___jp_202_;
}
else
{
lean_object* v_arg_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_arg_212_ = lean_ctor_get(v___x_210_, 1);
lean_inc_ref(v_arg_212_);
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_210_);
v___x_214_ = l_Lean_Expr_isApp(v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v___x_213_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
goto v___jp_202_;
}
else
{
lean_object* v_arg_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_arg_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_arg_215_);
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_213_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
goto v___jp_202_;
}
else
{
lean_object* v_arg_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_arg_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_arg_218_);
v___x_219_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_220_ = l_Lean_Expr_isApp(v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_219_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
goto v___jp_202_;
}
else
{
lean_object* v_arg_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_arg_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc_ref(v_arg_221_);
v___x_222_ = l_Lean_Expr_appFnCleanup___redArg(v___x_219_);
v___x_223_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_224_ = l_Lean_Expr_isConstOf(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
goto v___jp_202_;
}
else
{
lean_object* v___x_225_; 
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
lean_inc_ref(v_a_197_);
lean_inc(v_a_196_);
lean_inc_ref(v_a_195_);
lean_inc(v_a_194_);
lean_inc_ref(v_arg_218_);
v___x_225_ = lean_simp(v_arg_218_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_295_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_295_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_295_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_295_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_expr_230_; uint8_t v___x_231_; 
v_expr_230_ = lean_ctor_get(v_a_226_, 0);
lean_inc_ref(v_expr_230_);
v___x_231_ = l_Lean_Expr_isTrue(v_expr_230_);
if (v___x_231_ == 0)
{
uint8_t v___x_232_; 
lean_inc_ref(v_expr_230_);
v___x_232_ = l_Lean_Expr_isFalse(v_expr_230_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_a_226_);
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
v___x_233_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_233_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
else
{
lean_object* v___x_237_; 
lean_del_object(v___x_228_);
v___x_237_ = l_Lean_Meta_Simp_Result_getProof(v_a_226_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_257_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_257_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_257_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_257_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_242_ = lean_obj_once(&l_reduceDIte___closed__4, &l_reduceDIte___closed__4_once, _init_l_reduceDIte___closed__4);
lean_inc(v_a_238_);
lean_inc_ref(v_arg_218_);
v___x_243_ = l_Lean_mkAppB(v___x_242_, v_arg_218_, v_a_238_);
lean_inc_ref(v_arg_209_);
v___x_244_ = l_Lean_Expr_app___override(v_arg_209_, v___x_243_);
v___x_245_ = l_Lean_Expr_headBeta(v___x_244_);
v___x_246_ = ((lean_object*)(l_reduceDIte___closed__6));
v___x_247_ = l_Lean_Expr_constLevels_x21(v___x_222_);
lean_dec_ref(v___x_222_);
v___x_248_ = l_Lean_mkConst(v___x_246_, v___x_247_);
v___x_249_ = l_Lean_mkApp5(v___x_248_, v_arg_221_, v_arg_218_, v_arg_215_, v_arg_212_, v_arg_209_);
v___x_250_ = l_Lean_Expr_app___override(v___x_249_, v_a_238_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_252_, 0, v___x_245_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*2, v___x_224_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_253_);
v___x_255_ = v___x_240_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
v_a_258_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_237_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_237_);
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
}
else
{
lean_object* v___x_266_; 
lean_del_object(v___x_228_);
v___x_266_ = l_Lean_Meta_Simp_Result_getProof(v_a_226_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_286_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_286_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_286_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_286_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_271_ = lean_obj_once(&l_reduceDIte___closed__9, &l_reduceDIte___closed__9_once, _init_l_reduceDIte___closed__9);
lean_inc(v_a_267_);
lean_inc_ref(v_arg_218_);
v___x_272_ = l_Lean_mkAppB(v___x_271_, v_arg_218_, v_a_267_);
lean_inc_ref(v_arg_212_);
v___x_273_ = l_Lean_Expr_app___override(v_arg_212_, v___x_272_);
v___x_274_ = l_Lean_Expr_headBeta(v___x_273_);
v___x_275_ = ((lean_object*)(l_reduceDIte___closed__11));
v___x_276_ = l_Lean_Expr_constLevels_x21(v___x_222_);
lean_dec_ref(v___x_222_);
v___x_277_ = l_Lean_mkConst(v___x_275_, v___x_276_);
v___x_278_ = l_Lean_mkApp5(v___x_277_, v_arg_221_, v_arg_218_, v_arg_215_, v_arg_212_, v_arg_209_);
v___x_279_ = l_Lean_Expr_app___override(v___x_278_, v_a_267_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_281_, 0, v___x_274_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*2, v___x_224_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_282_);
v___x_284_ = v___x_269_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
v_a_287_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_266_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_266_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v___x_222_);
lean_dec_ref(v_arg_221_);
lean_dec_ref(v_arg_218_);
lean_dec_ref(v_arg_215_);
lean_dec_ref(v_arg_212_);
lean_dec_ref(v_arg_209_);
v_a_296_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_225_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_225_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
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
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_a_304_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_205_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_205_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
v___jp_202_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_reduceDIte___boxed(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_reduceDIte(v_e_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_341_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_342_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_339_, v___x_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22____boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
return v_res_344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_349_ = 0;
v___x_350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_351_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_348_, v___x_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24____boxed(lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_356_ = 0;
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_358_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_355_, v___x_356_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte(lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_inDSimp_387_; 
v_inDSimp_387_ = lean_ctor_get_uint8(v_a_377_, sizeof(void*)*10 + 8);
if (v_inDSimp_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_e_375_);
v___x_388_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_375_, v_a_380_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = l_Lean_Expr_cleanupAnnotations(v_a_391_);
v___x_393_ = l_Lean_Expr_isApp(v___x_392_);
if (v___x_393_ == 0)
{
lean_dec_ref(v___x_392_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_arg_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc_ref(v_arg_394_);
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_392_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_395_);
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_arg_397_ = lean_ctor_get(v___x_395_, 1);
lean_inc_ref(v_arg_397_);
v___x_398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
v___x_399_ = l_Lean_Expr_isApp(v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v___x_398_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_arg_400_ = lean_ctor_get(v___x_398_, 1);
lean_inc_ref(v_arg_400_);
v___x_401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_398_);
v___x_402_ = l_Lean_Expr_isApp(v___x_401_);
if (v___x_402_ == 0)
{
lean_dec_ref(v___x_401_);
lean_dec_ref(v_arg_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
else
{
lean_object* v_arg_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_arg_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc_ref(v_arg_403_);
v___x_404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_401_);
v___x_405_ = l_Lean_Expr_isApp(v___x_404_);
if (v___x_405_ == 0)
{
lean_dec_ref(v___x_404_);
lean_dec_ref(v_arg_403_);
lean_dec_ref(v_arg_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_404_);
v___x_407_ = ((lean_object*)(l_reduceIte___closed__2));
v___x_408_ = l_Lean_Expr_isConstOf(v___x_406_, v___x_407_);
lean_dec_ref(v___x_406_);
if (v___x_408_ == 0)
{
lean_dec_ref(v_arg_403_);
lean_dec_ref(v_arg_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
else
{
lean_object* v___x_409_; 
lean_inc(v_a_382_);
lean_inc_ref(v_a_381_);
lean_inc(v_a_380_);
lean_inc_ref(v_a_379_);
lean_inc(v_a_378_);
lean_inc_ref(v_a_377_);
lean_inc(v_a_376_);
v___x_409_ = lean_simp(v_arg_403_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_466_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_466_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_466_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_466_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_expr_459_; uint8_t v___x_460_; 
v_expr_459_ = lean_ctor_get(v_a_410_, 0);
lean_inc_ref_n(v_expr_459_, 2);
lean_dec(v_a_410_);
v___x_460_ = l_Lean_Expr_isTrue(v_expr_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Expr_isFalse(v_expr_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec_ref(v_arg_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
v___x_462_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_462_);
v___x_464_ = v___x_412_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_del_object(v___x_412_);
goto v___jp_414_;
}
}
else
{
lean_dec_ref(v_expr_459_);
lean_del_object(v___x_412_);
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_Lean_Expr_proj___override(v___x_415_, v___x_416_, v_arg_400_);
v___x_418_ = l_Lean_Meta_whnfD(v___x_417_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_419_, v_a_380_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_442_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_442_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = l_Lean_Expr_cleanupAnnotations(v_a_421_);
v___x_426_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_427_ = l_Lean_Expr_isConstOf(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
lean_dec_ref(v_arg_394_);
v___x_428_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_429_ = l_Lean_Expr_isConstOf(v___x_425_, v___x_428_);
lean_dec_ref(v___x_425_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_arg_397_);
v___x_430_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_430_);
v___x_432_ = v___x_423_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_arg_397_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_434_);
v___x_436_ = v___x_423_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec_ref(v___x_425_);
lean_dec_ref(v_arg_397_);
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_arg_394_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_438_);
v___x_440_ = v___x_423_;
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
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
v_a_443_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_420_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_420_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
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
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
v_a_451_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_418_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_418_);
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
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_arg_400_);
lean_dec_ref(v_arg_397_);
lean_dec_ref(v_arg_394_);
v_a_467_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_409_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_409_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
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
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_390_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_390_);
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
v___jp_384_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* v_e_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_dreduceIte(v_e_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_499_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_500_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_497_, v___x_498_, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22____boxed(lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
return v_res_502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_507_ = 0;
v___x_508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_509_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24____boxed(lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_514_ = 0;
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_516_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_513_, v___x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26____boxed(lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
uint8_t v_inDSimp_531_; 
v_inDSimp_531_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*10 + 8);
if (v_inDSimp_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref(v_e_519_);
v___x_532_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_519_, v_a_524_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = l_Lean_Expr_cleanupAnnotations(v_a_535_);
v___x_537_ = l_Lean_Expr_isApp(v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v___x_536_);
goto v___jp_528_;
}
else
{
lean_object* v_arg_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_arg_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc_ref(v_arg_538_);
v___x_539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_536_);
v___x_540_ = l_Lean_Expr_isApp(v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v___x_539_);
lean_dec_ref(v_arg_538_);
goto v___jp_528_;
}
else
{
lean_object* v_arg_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_arg_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc_ref(v_arg_541_);
v___x_542_ = l_Lean_Expr_appFnCleanup___redArg(v___x_539_);
v___x_543_ = l_Lean_Expr_isApp(v___x_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
goto v___jp_528_;
}
else
{
lean_object* v_arg_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_arg_544_ = lean_ctor_get(v___x_542_, 1);
lean_inc_ref(v_arg_544_);
v___x_545_ = l_Lean_Expr_appFnCleanup___redArg(v___x_542_);
v___x_546_ = l_Lean_Expr_isApp(v___x_545_);
if (v___x_546_ == 0)
{
lean_dec_ref(v___x_545_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
goto v___jp_528_;
}
else
{
lean_object* v_arg_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_arg_547_ = lean_ctor_get(v___x_545_, 1);
lean_inc_ref(v_arg_547_);
v___x_548_ = l_Lean_Expr_appFnCleanup___redArg(v___x_545_);
v___x_549_ = l_Lean_Expr_isApp(v___x_548_);
if (v___x_549_ == 0)
{
lean_dec_ref(v___x_548_);
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
goto v___jp_528_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_548_);
v___x_551_ = ((lean_object*)(l_reduceDIte___closed__1));
v___x_552_ = l_Lean_Expr_isConstOf(v___x_550_, v___x_551_);
lean_dec_ref(v___x_550_);
if (v___x_552_ == 0)
{
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
goto v___jp_528_;
}
else
{
lean_object* v___x_553_; 
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
lean_inc_ref(v_a_523_);
lean_inc(v_a_522_);
lean_inc_ref(v_a_521_);
lean_inc(v_a_520_);
lean_inc_ref(v_arg_547_);
v___x_553_ = lean_simp(v_arg_547_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_621_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_621_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_621_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_621_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_expr_614_; uint8_t v___x_615_; 
v_expr_614_ = lean_ctor_get(v_a_554_, 0);
lean_inc_ref_n(v_expr_614_, 2);
lean_dec(v_a_554_);
v___x_615_ = l_Lean_Expr_isTrue(v_expr_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Expr_isFalse(v_expr_614_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_619_; 
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
v___x_617_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_617_);
v___x_619_ = v___x_556_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_del_object(v___x_556_);
goto v___jp_558_;
}
}
else
{
lean_dec_ref(v_expr_614_);
lean_del_object(v___x_556_);
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_560_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_arg_544_);
v___x_561_ = l_Lean_Expr_proj___override(v___x_559_, v___x_560_, v_arg_544_);
v___x_562_ = l_Lean_Meta_whnfD(v___x_561_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_563_, v_a_524_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_597_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_597_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_597_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_597_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_569_ = l_Lean_Expr_cleanupAnnotations(v_a_565_);
v___x_570_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_571_ = l_Lean_Expr_isConstOf(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
lean_dec_ref(v_arg_538_);
v___x_572_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_573_ = l_Lean_Expr_isConstOf(v___x_569_, v___x_572_);
lean_dec_ref(v___x_569_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
v___x_574_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_574_);
v___x_576_ = v___x_567_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = l_Lean_Expr_proj___override(v___x_559_, v___x_578_, v_arg_544_);
v___x_580_ = l_Lean_Meta_mkExpectedPropHint(v___x_579_, v_arg_547_);
v___x_581_ = l_Lean_Expr_app___override(v_arg_541_, v___x_580_);
v___x_582_ = l_Lean_Expr_headBeta(v___x_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_583_);
v___x_585_ = v___x_567_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec_ref(v___x_569_);
lean_dec_ref(v_arg_541_);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = l_Lean_Expr_proj___override(v___x_559_, v___x_587_, v_arg_544_);
v___x_589_ = l_Lean_mkNot(v_arg_547_);
v___x_590_ = l_Lean_Meta_mkExpectedPropHint(v___x_588_, v___x_589_);
v___x_591_ = l_Lean_Expr_app___override(v_arg_538_, v___x_590_);
v___x_592_ = l_Lean_Expr_headBeta(v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_593_);
v___x_595_ = v___x_567_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
v_a_598_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_564_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_564_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
v_a_606_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_562_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_562_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_arg_544_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
v_a_622_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_553_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_553_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
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
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_534_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_534_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_dreduceDIte(v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_654_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_655_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_652_, v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22____boxed(lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
return v_res_657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_662_ = 0;
v___x_663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_664_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_661_, v___x_662_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24____boxed(lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_669_ = 0;
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_671_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_668_, v___x_669_, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26____boxed(lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_reduceCtorEq___lam__0(v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_reduceCtorEq___lam__1(v_x_707_, v_x_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v_x_708_);
lean_dec(v_x_707_);
return v_res_717_;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
v___x_723_ = l_Lean_mkConst(v___x_722_, v___x_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t v___x_724_, uint8_t v___x_725_, lean_object* v_h_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___y_737_; lean_object* v___x_757_; 
v___x_735_ = lean_obj_once(&l_reduceCtorEq___lam__2___closed__2, &l_reduceCtorEq___lam__2___closed__2_once, _init_l_reduceCtorEq___lam__2___closed__2);
lean_inc_ref(v_h_726_);
v___x_757_ = l_Lean_Meta_mkNoConfusion(v___x_735_, v_h_726_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
v___x_761_ = lean_array_push(v___x_760_, v_h_726_);
v___x_762_ = 1;
v___x_763_ = l_Lean_Meta_mkLambdaFVars(v___x_761_, v_a_758_, v___x_725_, v___x_724_, v___x_725_, v___x_724_, v___x_762_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec_ref(v___x_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; uint8_t v_transparency_766_; uint8_t v___x_767_; uint8_t v___x_768_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_Meta_Context_config(v___y_730_);
v_transparency_766_ = lean_ctor_get_uint8(v___x_765_, 9);
lean_dec_ref(v___x_765_);
v___x_767_ = 1;
v___x_768_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v_keyedConfig_769_; uint8_t v_trackZetaDelta_770_; lean_object* v_zetaDeltaSet_771_; lean_object* v_lctx_772_; lean_object* v_localInstances_773_; lean_object* v_defEqCtx_x3f_774_; lean_object* v_synthPendingDepth_775_; lean_object* v_customCanUnfoldPredicate_x3f_776_; uint8_t v_univApprox_777_; uint8_t v_inTypeClassResolution_778_; uint8_t v_cacheInferType_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_keyedConfig_769_ = lean_ctor_get(v___y_730_, 0);
v_trackZetaDelta_770_ = lean_ctor_get_uint8(v___y_730_, sizeof(void*)*7);
v_zetaDeltaSet_771_ = lean_ctor_get(v___y_730_, 1);
v_lctx_772_ = lean_ctor_get(v___y_730_, 2);
v_localInstances_773_ = lean_ctor_get(v___y_730_, 3);
v_defEqCtx_x3f_774_ = lean_ctor_get(v___y_730_, 4);
v_synthPendingDepth_775_ = lean_ctor_get(v___y_730_, 5);
v_customCanUnfoldPredicate_x3f_776_ = lean_ctor_get(v___y_730_, 6);
v_univApprox_777_ = lean_ctor_get_uint8(v___y_730_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_778_ = lean_ctor_get_uint8(v___y_730_, sizeof(void*)*7 + 2);
v_cacheInferType_779_ = lean_ctor_get_uint8(v___y_730_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_769_);
v___x_780_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_767_, v_keyedConfig_769_);
lean_inc(v_customCanUnfoldPredicate_x3f_776_);
lean_inc(v_synthPendingDepth_775_);
lean_inc(v_defEqCtx_x3f_774_);
lean_inc_ref(v_localInstances_773_);
lean_inc_ref(v_lctx_772_);
lean_inc(v_zetaDeltaSet_771_);
v___x_781_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_zetaDeltaSet_771_);
lean_ctor_set(v___x_781_, 2, v_lctx_772_);
lean_ctor_set(v___x_781_, 3, v_localInstances_773_);
lean_ctor_set(v___x_781_, 4, v_defEqCtx_x3f_774_);
lean_ctor_set(v___x_781_, 5, v_synthPendingDepth_775_);
lean_ctor_set(v___x_781_, 6, v_customCanUnfoldPredicate_x3f_776_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7, v_trackZetaDelta_770_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 1, v_univApprox_777_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 2, v_inTypeClassResolution_778_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 3, v_cacheInferType_779_);
v___x_782_ = l_Lean_Meta_mkEqFalse_x27(v_a_764_, v___x_781_, v___y_731_, v___y_732_, v___y_733_);
lean_dec_ref_known(v___x_781_, 7);
v___y_737_ = v___x_782_;
goto v___jp_736_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_mkEqFalse_x27(v_a_764_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
v___y_737_ = v___x_783_;
goto v___jp_736_;
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_763_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_763_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_h_726_);
v_a_792_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_757_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_757_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
v___jp_736_:
{
if (lean_obj_tag(v___y_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_a_738_ = lean_ctor_get(v___y_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___y_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v___y_737_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___y_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_738_);
v___x_743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_743_, 0, v___x_735_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*2, v___x_724_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
v_a_749_ = lean_ctor_get(v___y_737_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___y_737_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___y_737_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___y_737_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v_h_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___x_18300__boxed_811_; uint8_t v___x_18301__boxed_812_; lean_object* v_res_813_; 
v___x_18300__boxed_811_ = lean_unbox(v___x_800_);
v___x_18301__boxed_812_ = lean_unbox(v___x_801_);
v_res_813_ = l_reduceCtorEq___lam__2(v___x_18300__boxed_811_, v___x_18301__boxed_812_, v_h_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
v___x_824_ = lean_apply_9(v_k_814_, v_b_818_, v___y_815_, v___y_816_, v___y_817_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_825_, v___y_826_, v___y_827_, v___y_828_, v_b_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_836_, uint8_t v_bi_837_, lean_object* v_type_838_, lean_object* v_k_839_, uint8_t v_kind_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___x_850_; 
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_849_, 0, v_k_839_);
lean_closure_set(v___f_849_, 1, v___y_841_);
lean_closure_set(v___f_849_, 2, v___y_842_);
lean_closure_set(v___f_849_, 3, v___y_843_);
v___x_850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_836_, v_bi_837_, v_type_838_, v___f_849_, v_kind_840_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_850_) == 0)
{
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_859_, lean_object* v_bi_860_, lean_object* v_type_861_, lean_object* v_k_862_, lean_object* v_kind_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_bi_boxed_872_; uint8_t v_kind_boxed_873_; lean_object* v_res_874_; 
v_bi_boxed_872_ = lean_unbox(v_bi_860_);
v_kind_boxed_873_ = lean_unbox(v_kind_863_);
v_res_874_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_859_, v_bi_boxed_872_, v_type_861_, v_k_862_, v_kind_boxed_873_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* v_name_875_, lean_object* v_type_876_, lean_object* v_k_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v___x_886_ = 0;
v___x_887_ = 0;
v___x_888_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_875_, v___x_886_, v_type_876_, v_k_877_, v___x_887_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_889_, lean_object* v_type_890_, lean_object* v_k_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_889_, v_type_890_, v_k_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___y_917_; lean_object* v___x_926_; uint8_t v_transparency_927_; uint8_t v___x_928_; uint8_t v___x_929_; 
v___x_926_ = l_Lean_Meta_Context_config(v_a_911_);
v_transparency_927_ = lean_ctor_get_uint8(v___x_926_, 9);
lean_dec_ref(v___x_926_);
v___x_928_ = 3;
v___x_929_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v_keyedConfig_930_; uint8_t v_trackZetaDelta_931_; lean_object* v_zetaDeltaSet_932_; lean_object* v_lctx_933_; lean_object* v_localInstances_934_; lean_object* v_defEqCtx_x3f_935_; lean_object* v_synthPendingDepth_936_; lean_object* v_customCanUnfoldPredicate_x3f_937_; uint8_t v_univApprox_938_; uint8_t v_inTypeClassResolution_939_; uint8_t v_cacheInferType_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_keyedConfig_930_ = lean_ctor_get(v_a_911_, 0);
v_trackZetaDelta_931_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*7);
v_zetaDeltaSet_932_ = lean_ctor_get(v_a_911_, 1);
v_lctx_933_ = lean_ctor_get(v_a_911_, 2);
v_localInstances_934_ = lean_ctor_get(v_a_911_, 3);
v_defEqCtx_x3f_935_ = lean_ctor_get(v_a_911_, 4);
v_synthPendingDepth_936_ = lean_ctor_get(v_a_911_, 5);
v_customCanUnfoldPredicate_x3f_937_ = lean_ctor_get(v_a_911_, 6);
v_univApprox_938_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_939_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*7 + 2);
v_cacheInferType_940_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_930_);
v___x_941_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_928_, v_keyedConfig_930_);
lean_inc(v_customCanUnfoldPredicate_x3f_937_);
lean_inc(v_synthPendingDepth_936_);
lean_inc(v_defEqCtx_x3f_935_);
lean_inc_ref(v_localInstances_934_);
lean_inc_ref(v_lctx_933_);
lean_inc(v_zetaDeltaSet_932_);
v___x_942_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_zetaDeltaSet_932_);
lean_ctor_set(v___x_942_, 2, v_lctx_933_);
lean_ctor_set(v___x_942_, 3, v_localInstances_934_);
lean_ctor_set(v___x_942_, 4, v_defEqCtx_x3f_935_);
lean_ctor_set(v___x_942_, 5, v_synthPendingDepth_936_);
lean_ctor_set(v___x_942_, 6, v_customCanUnfoldPredicate_x3f_937_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*7, v_trackZetaDelta_931_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*7 + 1, v_univApprox_938_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*7 + 2, v_inTypeClassResolution_939_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*7 + 3, v_cacheInferType_940_);
lean_inc_ref(v_e_907_);
v___x_943_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_907_, v_a_912_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = l_Lean_Expr_cleanupAnnotations(v_a_944_);
v___x_946_ = l_Lean_Expr_isApp(v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec_ref(v___x_945_);
lean_dec_ref(v_e_907_);
v___x_947_ = lean_box(0);
v___x_948_ = l_reduceCtorEq___lam__0(v___x_947_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
v___y_917_ = v___x_948_;
goto v___jp_916_;
}
else
{
lean_object* v_arg_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_arg_949_ = lean_ctor_get(v___x_945_, 1);
lean_inc_ref(v_arg_949_);
v___x_950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_945_);
v___x_951_ = l_Lean_Expr_isApp(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec_ref(v___x_950_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_907_);
v___x_952_ = lean_box(0);
v___x_953_ = l_reduceCtorEq___lam__0(v___x_952_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
v___y_917_ = v___x_953_;
goto v___jp_916_;
}
else
{
lean_object* v_arg_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_arg_954_ = lean_ctor_get(v___x_950_, 1);
lean_inc_ref(v_arg_954_);
v___x_955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_950_);
v___x_956_ = l_Lean_Expr_isApp(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v___x_955_);
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_907_);
v___x_957_ = lean_box(0);
v___x_958_ = l_reduceCtorEq___lam__0(v___x_957_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
v___y_917_ = v___x_958_;
goto v___jp_916_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_955_);
v___x_960_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_961_ = l_Lean_Expr_isConstOf(v___x_959_, v___x_960_);
lean_dec_ref(v___x_959_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v_arg_954_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_907_);
v___x_962_ = lean_box(0);
v___x_963_ = l_reduceCtorEq___lam__0(v___x_962_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
v___y_917_ = v___x_963_;
goto v___jp_916_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_967_; 
v___x_964_ = lean_box(v___x_961_);
v___x_965_ = lean_box(v___x_929_);
v___f_966_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_966_, 0, v___x_964_);
lean_closure_set(v___f_966_, 1, v___x_965_);
v___x_967_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_954_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_949_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_993_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_993_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint8_t v___y_975_; 
if (lean_obj_tag(v_a_968_) == 1)
{
if (lean_obj_tag(v_a_970_) == 1)
{
lean_object* v_val_982_; lean_object* v_val_983_; lean_object* v_fst_984_; lean_object* v_toConstantVal_985_; lean_object* v_fst_986_; lean_object* v_toConstantVal_987_; lean_object* v_name_988_; lean_object* v_name_989_; uint8_t v___x_990_; 
v_val_982_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_a_968_, 1);
v_val_983_ = lean_ctor_get(v_a_970_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_a_970_, 1);
v_fst_984_ = lean_ctor_get(v_val_982_, 0);
lean_inc(v_fst_984_);
lean_dec(v_val_982_);
v_toConstantVal_985_ = lean_ctor_get(v_fst_984_, 0);
lean_inc_ref(v_toConstantVal_985_);
lean_dec(v_fst_984_);
v_fst_986_ = lean_ctor_get(v_val_983_, 0);
lean_inc(v_fst_986_);
lean_dec(v_val_983_);
v_toConstantVal_987_ = lean_ctor_get(v_fst_986_, 0);
lean_inc_ref(v_toConstantVal_987_);
lean_dec(v_fst_986_);
v_name_988_ = lean_ctor_get(v_toConstantVal_985_, 0);
lean_inc(v_name_988_);
lean_dec_ref(v_toConstantVal_985_);
v_name_989_ = lean_ctor_get(v_toConstantVal_987_, 0);
lean_inc(v_name_989_);
lean_dec_ref(v_toConstantVal_987_);
v___x_990_ = lean_name_eq(v_name_988_, v_name_989_);
lean_dec(v_name_989_);
lean_dec(v_name_988_);
if (v___x_990_ == 0)
{
v___y_975_ = v___x_961_;
goto v___jp_974_;
}
else
{
v___y_975_ = v___x_929_;
goto v___jp_974_;
}
}
else
{
lean_object* v___x_991_; 
lean_del_object(v___x_972_);
lean_dec_ref(v___f_966_);
lean_dec_ref(v_e_907_);
v___x_991_ = l_reduceCtorEq___lam__1(v_a_968_, v_a_970_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
lean_dec(v_a_970_);
lean_dec_ref_known(v_a_968_, 1);
v___y_917_ = v___x_991_;
goto v___jp_916_;
}
}
else
{
lean_object* v___x_992_; 
lean_del_object(v___x_972_);
lean_dec_ref(v___f_966_);
lean_dec_ref(v_e_907_);
v___x_992_ = l_reduceCtorEq___lam__1(v_a_968_, v_a_970_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
lean_dec(v_a_970_);
lean_dec(v_a_968_);
v___y_917_ = v___x_992_;
goto v___jp_916_;
}
v___jp_974_:
{
if (v___y_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec_ref(v___f_966_);
lean_dec_ref_known(v___x_942_, 7);
lean_dec_ref(v_e_907_);
v___x_976_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_976_);
v___x_978_ = v___x_972_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_del_object(v___x_972_);
v___x_980_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_981_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_980_, v_e_907_, v___f_966_, v_a_908_, v_a_909_, v_a_910_, v___x_942_, v_a_912_, v_a_913_, v_a_914_);
lean_dec_ref_known(v___x_942_, 7);
v___y_917_ = v___x_981_;
goto v___jp_916_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_a_968_);
lean_dec_ref(v___f_966_);
lean_dec_ref_known(v___x_942_, 7);
lean_dec_ref(v_e_907_);
v_a_994_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_969_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_969_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v___f_966_);
lean_dec_ref(v_arg_949_);
lean_dec_ref_known(v___x_942_, 7);
lean_dec_ref(v_e_907_);
v_a_1002_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_967_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_967_);
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
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref_known(v___x_942_, 7);
lean_dec_ref(v_e_907_);
v_a_1010_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_943_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_943_);
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
lean_object* v___x_1018_; 
lean_inc_ref(v_e_907_);
v___x_1018_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_907_, v_a_912_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_Lean_Expr_cleanupAnnotations(v_a_1019_);
v___x_1021_ = l_Lean_Expr_isApp(v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v___x_1020_);
lean_dec_ref(v_e_907_);
v___x_1022_ = lean_box(0);
v___x_1023_ = l_reduceCtorEq___lam__0(v___x_1022_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
v___y_917_ = v___x_1023_;
goto v___jp_916_;
}
else
{
lean_object* v_arg_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_arg_1024_ = lean_ctor_get(v___x_1020_, 1);
lean_inc_ref(v_arg_1024_);
v___x_1025_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1020_);
v___x_1026_ = l_Lean_Expr_isApp(v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_e_907_);
v___x_1027_ = lean_box(0);
v___x_1028_ = l_reduceCtorEq___lam__0(v___x_1027_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
v___y_917_ = v___x_1028_;
goto v___jp_916_;
}
else
{
lean_object* v_arg_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_arg_1029_ = lean_ctor_get(v___x_1025_, 1);
lean_inc_ref(v_arg_1029_);
v___x_1030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1025_);
v___x_1031_ = l_Lean_Expr_isApp(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_e_907_);
v___x_1032_ = lean_box(0);
v___x_1033_ = l_reduceCtorEq___lam__0(v___x_1032_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
v___y_917_ = v___x_1033_;
goto v___jp_916_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1030_);
v___x_1035_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_1036_ = l_Lean_Expr_isConstOf(v___x_1034_, v___x_1035_);
lean_dec_ref(v___x_1034_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_e_907_);
v___x_1037_ = lean_box(0);
v___x_1038_ = l_reduceCtorEq___lam__0(v___x_1037_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
v___y_917_ = v___x_1038_;
goto v___jp_916_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1029_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1024_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1041_) == 0)
{
if (lean_obj_tag(v_a_1040_) == 1)
{
lean_object* v_val_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1065_; 
v_val_1042_ = lean_ctor_get(v_a_1040_, 0);
v_a_1043_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1045_ = v___x_1041_;
v_isShared_1046_ = v_isSharedCheck_1065_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1065_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
if (lean_obj_tag(v_a_1043_) == 1)
{
lean_object* v_val_1047_; lean_object* v_fst_1048_; lean_object* v_toConstantVal_1049_; lean_object* v_fst_1050_; lean_object* v_toConstantVal_1051_; lean_object* v_name_1052_; lean_object* v_name_1053_; uint8_t v___x_1054_; 
lean_inc(v_val_1042_);
lean_dec_ref_known(v_a_1040_, 1);
v_val_1047_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v_a_1043_, 1);
v_fst_1048_ = lean_ctor_get(v_val_1042_, 0);
lean_inc(v_fst_1048_);
lean_dec(v_val_1042_);
v_toConstantVal_1049_ = lean_ctor_get(v_fst_1048_, 0);
lean_inc_ref(v_toConstantVal_1049_);
lean_dec(v_fst_1048_);
v_fst_1050_ = lean_ctor_get(v_val_1047_, 0);
lean_inc(v_fst_1050_);
lean_dec(v_val_1047_);
v_toConstantVal_1051_ = lean_ctor_get(v_fst_1050_, 0);
lean_inc_ref(v_toConstantVal_1051_);
lean_dec(v_fst_1050_);
v_name_1052_ = lean_ctor_get(v_toConstantVal_1049_, 0);
lean_inc(v_name_1052_);
lean_dec_ref(v_toConstantVal_1049_);
v_name_1053_ = lean_ctor_get(v_toConstantVal_1051_, 0);
lean_inc(v_name_1053_);
lean_dec_ref(v_toConstantVal_1051_);
v___x_1054_ = lean_name_eq(v_name_1052_, v_name_1053_);
lean_dec(v_name_1053_);
lean_dec(v_name_1052_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_del_object(v___x_1045_);
v___x_1055_ = lean_box(v___x_1036_);
v___x_1056_ = lean_box(v___x_1054_);
v___f_1057_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1057_, 0, v___x_1055_);
lean_closure_set(v___f_1057_, 1, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_1059_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1058_, v_e_907_, v___f_1057_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
v___y_917_ = v___x_1059_;
goto v___jp_916_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v_e_907_);
v___x_1060_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1060_);
v___x_1062_ = v___x_1045_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v___x_1064_; 
lean_del_object(v___x_1045_);
lean_dec_ref(v_e_907_);
v___x_1064_ = l_reduceCtorEq___lam__1(v_a_1040_, v_a_1043_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_1043_);
lean_dec_ref_known(v_a_1040_, 1);
v___y_917_ = v___x_1064_;
goto v___jp_916_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
lean_dec_ref(v_e_907_);
v_a_1066_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1067_ = l_reduceCtorEq___lam__1(v_a_1040_, v_a_1066_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_1066_);
lean_dec(v_a_1040_);
v___y_917_ = v___x_1067_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1040_);
lean_dec_ref(v_e_907_);
v_a_1068_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1041_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1041_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_arg_1024_);
lean_dec_ref(v_e_907_);
v_a_1076_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1039_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1039_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
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
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_e_907_);
v_a_1084_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1018_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1018_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
v___jp_916_:
{
if (lean_obj_tag(v___y_917_) == 0)
{
return v___y_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v___y_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___y_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___y_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___y_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* v_e_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_reduceCtorEq(v_e_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_1102_, lean_object* v_name_1103_, uint8_t v_bi_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, uint8_t v_kind_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_1103_, v_bi_1104_, v_type_1105_, v_k_1106_, v_kind_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_name_1118_, lean_object* v_bi_1119_, lean_object* v_type_1120_, lean_object* v_k_1121_, lean_object* v_kind_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_bi_boxed_1131_; uint8_t v_kind_boxed_1132_; lean_object* v_res_1133_; 
v_bi_boxed_1131_ = lean_unbox(v_bi_1119_);
v_kind_boxed_1132_ = lean_unbox(v_kind_1122_);
v_res_1133_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_1117_, v_name_1118_, v_bi_boxed_1131_, v_type_1120_, v_k_1121_, v_kind_boxed_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* v_00_u03b1_1134_, lean_object* v_name_1135_, lean_object* v_type_1136_, lean_object* v_k_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_1135_, v_type_1136_, v_k_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_1147_, lean_object* v_name_1148_, lean_object* v_type_1149_, lean_object* v_k_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(v_00_u03b1_1147_, v_name_1148_, v_type_1149_, v_k_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1177_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1178_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1175_, v___x_1176_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23____boxed(lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
return v_res_1180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1185_ = 1;
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1187_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1184_, v___x_1185_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25____boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1192_ = 1;
v___x_1193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1194_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1191_, v___x_1192_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27____boxed(lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
return v_res_1196_;
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
