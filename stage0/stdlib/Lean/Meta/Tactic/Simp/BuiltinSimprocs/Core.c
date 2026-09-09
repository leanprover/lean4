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
lean_object* l_Lean_Meta_constructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_158_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_159_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_156_, v___x_157_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22____boxed(lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_();
return v_res_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_alloc_closure((void*)(l_reduceIte___boxed), 9, 0);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_166_ = 0;
v___x_167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_168_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24____boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_173_ = 0;
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_24_);
v___x_175_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_172_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_26_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_353_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_354_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_351_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_();
return v_res_356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_alloc_closure((void*)(l_reduceDIte___boxed), 9, 0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_361_ = 0;
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_363_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_360_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_368_ = 0;
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_24_);
v___x_370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26____boxed(lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_26_();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_dreduceIte(lean_object* v_e_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
uint8_t v_inDSimp_396_; 
v_inDSimp_396_ = lean_ctor_get_uint8(v_a_389_, sizeof(void*)*10 + 8);
if (v_inDSimp_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_e_387_);
v___x_397_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_387_, v_a_392_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_492_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_492_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_492_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_492_;
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
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
lean_inc(v_a_392_);
lean_inc_ref(v_a_391_);
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
v___x_426_ = lean_simp(v_arg_420_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_483_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_483_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_483_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_483_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_expr_476_; uint8_t v___x_477_; 
v_expr_476_ = lean_ctor_get(v_a_427_, 0);
lean_inc_ref_n(v_expr_476_, 2);
lean_dec(v_a_427_);
v___x_477_ = l_Lean_Expr_isTrue(v_expr_476_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_Expr_isFalse(v_expr_476_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v___x_479_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_479_);
v___x_481_ = v___x_429_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
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
lean_dec_ref(v_expr_476_);
lean_del_object(v___x_429_);
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = l_Lean_Expr_proj___override(v___x_432_, v___x_433_, v_arg_417_);
v___x_435_ = l_Lean_Meta_whnfD(v___x_434_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_436_, v_a_392_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_459_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_459_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = l_Lean_Expr_cleanupAnnotations(v_a_438_);
v___x_443_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_444_ = l_Lean_Expr_isConstOf(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
lean_dec_ref(v_arg_411_);
v___x_445_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_446_ = l_Lean_Expr_isConstOf(v___x_442_, v___x_445_);
lean_dec_ref(v___x_442_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec_ref(v_arg_414_);
v___x_447_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_447_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v_arg_414_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_451_);
v___x_453_ = v___x_440_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref(v___x_442_);
lean_dec_ref(v_arg_414_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_arg_411_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_455_);
v___x_457_ = v___x_440_;
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
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_460_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_437_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_437_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_468_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_435_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_435_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v_arg_417_);
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_arg_411_);
v_a_484_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_426_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_426_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
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
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_399_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_399_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_dreduceIte___boxed(lean_object* v_e_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_dreduceIte(v_e_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3740862664____hygCtx___hyg_22_));
v___x_517_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_518_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_515_, v___x_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22____boxed(lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_();
return v_res_520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_closure((void*)(l_dreduceIte___boxed), 9, 0);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_525_ = 0;
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_527_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_524_, v___x_525_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24____boxed(lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_();
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_22_));
v___x_532_ = 0;
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_24_);
v___x_534_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_531_, v___x_532_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26____boxed(lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_4172960257____hygCtx___hyg_26_();
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_dreduceDIte(lean_object* v_e_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
uint8_t v_inDSimp_546_; 
v_inDSimp_546_ = lean_ctor_get_uint8(v_a_539_, sizeof(void*)*10 + 8);
if (v_inDSimp_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_e_537_);
v___x_547_ = ((lean_object*)(l_dreduceIte___closed__0));
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_537_, v_a_542_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_653_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_653_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_653_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_653_;
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
lean_inc(v_a_544_);
lean_inc_ref(v_a_543_);
lean_inc(v_a_542_);
lean_inc_ref(v_a_541_);
lean_inc(v_a_540_);
lean_inc_ref(v_a_539_);
lean_inc(v_a_538_);
lean_inc_ref(v_arg_570_);
v___x_576_ = lean_simp(v_arg_570_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_644_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_644_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_644_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_644_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_expr_637_; uint8_t v___x_638_; 
v_expr_637_ = lean_ctor_get(v_a_577_, 0);
lean_inc_ref_n(v_expr_637_, 2);
lean_dec(v_a_577_);
v___x_638_ = l_Lean_Expr_isTrue(v_expr_637_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = l_Lean_Expr_isFalse(v_expr_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_642_; 
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v___x_640_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_640_);
v___x_642_ = v___x_579_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
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
lean_dec_ref(v_expr_637_);
lean_del_object(v___x_579_);
goto v___jp_581_;
}
v___jp_581_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l_dreduceIte___closed__2));
v___x_583_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_arg_567_);
v___x_584_ = l_Lean_Expr_proj___override(v___x_582_, v___x_583_, v_arg_567_);
v___x_585_ = l_Lean_Meta_whnfD(v___x_584_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_586_, v_a_542_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_620_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_620_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_Expr_cleanupAnnotations(v_a_588_);
v___x_593_ = ((lean_object*)(l_dreduceIte___closed__5));
v___x_594_ = l_Lean_Expr_isConstOf(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
lean_dec_ref(v_arg_561_);
v___x_595_ = ((lean_object*)(l_dreduceIte___closed__7));
v___x_596_ = l_Lean_Expr_isConstOf(v___x_592_, v___x_595_);
lean_dec_ref(v___x_592_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
v___x_597_ = ((lean_object*)(l_dreduceIte___closed__0));
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_599_ = v___x_590_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = l_Lean_Expr_proj___override(v___x_582_, v___x_601_, v_arg_567_);
v___x_603_ = l_Lean_Meta_mkExpectedPropHint(v___x_602_, v_arg_570_);
v___x_604_ = l_Lean_Expr_app___override(v_arg_564_, v___x_603_);
v___x_605_ = l_Lean_Expr_headBeta(v___x_604_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_606_);
v___x_608_ = v___x_590_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec_ref(v___x_592_);
lean_dec_ref(v_arg_564_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = l_Lean_Expr_proj___override(v___x_582_, v___x_610_, v_arg_567_);
v___x_612_ = l_Lean_mkNot(v_arg_570_);
v___x_613_ = l_Lean_Meta_mkExpectedPropHint(v___x_611_, v___x_612_);
v___x_614_ = l_Lean_Expr_app___override(v_arg_561_, v___x_613_);
v___x_615_ = l_Lean_Expr_headBeta(v___x_614_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_616_);
v___x_618_ = v___x_590_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_621_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_587_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_587_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_629_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_585_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_585_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_arg_570_);
lean_dec_ref(v_arg_567_);
lean_dec_ref(v_arg_564_);
lean_dec_ref(v_arg_561_);
v_a_645_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_576_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_576_);
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
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_a_654_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_549_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_549_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_dreduceDIte___boxed(lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_dreduceDIte(v_e_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3607572908____hygCtx___hyg_22_));
v___x_678_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_679_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_676_, v___x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22____boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_();
return v_res_681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_alloc_closure((void*)(l_dreduceDIte___boxed), 9, 0);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_686_ = 0;
v___x_687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_688_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_685_, v___x_686_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24____boxed(lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_();
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_22_));
v___x_693_ = 0;
v___x_694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_24_);
v___x_695_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_692_, v___x_693_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26____boxed(lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_2523473668____hygCtx___hyg_26_();
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0(lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__0___boxed(lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_reduceCtorEq___lam__0(v_x_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_reduceIte___closed__0));
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__1___boxed(lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_reduceCtorEq___lam__1(v_x_731_, v_x_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_x_732_);
lean_dec(v_x_731_);
return v_res_741_;
}
}
static lean_object* _init_l_reduceCtorEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = ((lean_object*)(l_reduceCtorEq___lam__2___closed__1));
v___x_747_ = l_Lean_mkConst(v___x_746_, v___x_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2(uint8_t v___x_748_, uint8_t v___x_749_, lean_object* v_h_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___y_761_; lean_object* v___x_781_; 
v___x_759_ = lean_obj_once(&l_reduceCtorEq___lam__2___closed__2, &l_reduceCtorEq___lam__2___closed__2_once, _init_l_reduceCtorEq___lam__2___closed__2);
lean_inc_ref(v_h_750_);
v___x_781_ = l_Lean_Meta_mkNoConfusion(v___x_759_, v_h_750_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_mk_empty_array_with_capacity(v___x_783_);
v___x_785_ = lean_array_push(v___x_784_, v_h_750_);
v___x_786_ = 1;
v___x_787_ = l_Lean_Meta_mkLambdaFVars(v___x_785_, v_a_782_, v___x_748_, v___x_749_, v___x_748_, v___x_749_, v___x_786_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v___x_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; uint8_t v_transparency_790_; uint8_t v___x_791_; uint8_t v___x_792_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = l_Lean_Meta_Context_config(v___y_754_);
v_transparency_790_ = lean_ctor_get_uint8(v___x_789_, 9);
lean_dec_ref(v___x_789_);
v___x_791_ = 1;
v___x_792_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v_keyedConfig_793_; uint8_t v_trackZetaDelta_794_; lean_object* v_zetaDeltaSet_795_; lean_object* v_lctx_796_; lean_object* v_localInstances_797_; lean_object* v_defEqCtx_x3f_798_; lean_object* v_synthPendingDepth_799_; lean_object* v_customCanUnfoldPredicate_x3f_800_; uint8_t v_univApprox_801_; uint8_t v_inTypeClassResolution_802_; uint8_t v_cacheInferType_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_keyedConfig_793_ = lean_ctor_get(v___y_754_, 0);
v_trackZetaDelta_794_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*7);
v_zetaDeltaSet_795_ = lean_ctor_get(v___y_754_, 1);
v_lctx_796_ = lean_ctor_get(v___y_754_, 2);
v_localInstances_797_ = lean_ctor_get(v___y_754_, 3);
v_defEqCtx_x3f_798_ = lean_ctor_get(v___y_754_, 4);
v_synthPendingDepth_799_ = lean_ctor_get(v___y_754_, 5);
v_customCanUnfoldPredicate_x3f_800_ = lean_ctor_get(v___y_754_, 6);
v_univApprox_801_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_802_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*7 + 2);
v_cacheInferType_803_ = lean_ctor_get_uint8(v___y_754_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_793_);
v___x_804_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_791_, v_keyedConfig_793_);
lean_inc(v_customCanUnfoldPredicate_x3f_800_);
lean_inc(v_synthPendingDepth_799_);
lean_inc(v_defEqCtx_x3f_798_);
lean_inc_ref(v_localInstances_797_);
lean_inc_ref(v_lctx_796_);
lean_inc(v_zetaDeltaSet_795_);
v___x_805_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_zetaDeltaSet_795_);
lean_ctor_set(v___x_805_, 2, v_lctx_796_);
lean_ctor_set(v___x_805_, 3, v_localInstances_797_);
lean_ctor_set(v___x_805_, 4, v_defEqCtx_x3f_798_);
lean_ctor_set(v___x_805_, 5, v_synthPendingDepth_799_);
lean_ctor_set(v___x_805_, 6, v_customCanUnfoldPredicate_x3f_800_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*7, v_trackZetaDelta_794_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*7 + 1, v_univApprox_801_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*7 + 2, v_inTypeClassResolution_802_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*7 + 3, v_cacheInferType_803_);
v___x_806_ = l_Lean_Meta_mkEqFalse_x27(v_a_788_, v___x_805_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref_known(v___x_805_, 7);
v___y_761_ = v___x_806_;
goto v___jp_760_;
}
else
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_mkEqFalse_x27(v_a_788_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
v___y_761_ = v___x_807_;
goto v___jp_760_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_787_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_787_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_h_750_);
v_a_816_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_781_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_781_);
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
v___jp_760_:
{
if (lean_obj_tag(v___y_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_772_; 
v_a_762_ = lean_ctor_get(v___y_761_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___y_761_);
if (v_isSharedCheck_772_ == 0)
{
v___x_764_ = v___y_761_;
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___y_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
v___x_767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_767_, 0, v___x_759_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*2, v___x_749_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_768_);
v___x_770_ = v___x_764_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v___y_761_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___y_761_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___y_761_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___y_761_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___lam__2___boxed(lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_h_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_18292__boxed_835_; uint8_t v___x_18293__boxed_836_; lean_object* v_res_837_; 
v___x_18292__boxed_835_ = lean_unbox(v___x_824_);
v___x_18293__boxed_836_ = lean_unbox(v___x_825_);
v_res_837_ = l_reduceCtorEq___lam__2(v___x_18292__boxed_835_, v___x_18293__boxed_836_, v_h_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
v___x_848_ = lean_apply_9(v_k_838_, v_b_842_, v___y_839_, v___y_840_, v___y_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_849_, v___y_850_, v___y_851_, v___y_852_, v_b_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_860_, uint8_t v_bi_861_, lean_object* v_type_862_, lean_object* v_k_863_, uint8_t v_kind_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; 
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_873_, 0, v_k_863_);
lean_closure_set(v___f_873_, 1, v___y_865_);
lean_closure_set(v___f_873_, 2, v___y_866_);
lean_closure_set(v___f_873_, 3, v___y_867_);
v___x_874_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_860_, v_bi_861_, v_type_862_, v___f_873_, v_kind_864_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
return v___x_874_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_883_, lean_object* v_bi_884_, lean_object* v_type_885_, lean_object* v_k_886_, lean_object* v_kind_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_bi_boxed_896_; uint8_t v_kind_boxed_897_; lean_object* v_res_898_; 
v_bi_boxed_896_ = lean_unbox(v_bi_884_);
v_kind_boxed_897_ = lean_unbox(v_kind_887_);
v_res_898_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_883_, v_bi_boxed_896_, v_type_885_, v_k_886_, v_kind_boxed_897_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(lean_object* v_name_899_, lean_object* v_type_900_, lean_object* v_k_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
uint8_t v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
v___x_910_ = 0;
v___x_911_ = 0;
v___x_912_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_899_, v___x_910_, v_type_900_, v_k_901_, v___x_911_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_913_, lean_object* v_type_914_, lean_object* v_k_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_913_, v_type_914_, v_k_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq(lean_object* v_e_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___y_941_; lean_object* v___x_950_; uint8_t v_transparency_951_; uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_950_ = l_Lean_Meta_Context_config(v_a_935_);
v_transparency_951_ = lean_ctor_get_uint8(v___x_950_, 9);
lean_dec_ref(v___x_950_);
v___x_952_ = 3;
v___x_953_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v_keyedConfig_954_; uint8_t v_trackZetaDelta_955_; lean_object* v_zetaDeltaSet_956_; lean_object* v_lctx_957_; lean_object* v_localInstances_958_; lean_object* v_defEqCtx_x3f_959_; lean_object* v_synthPendingDepth_960_; lean_object* v_customCanUnfoldPredicate_x3f_961_; uint8_t v_univApprox_962_; uint8_t v_inTypeClassResolution_963_; uint8_t v_cacheInferType_964_; lean_object* v___x_965_; 
v_keyedConfig_954_ = lean_ctor_get(v_a_935_, 0);
v_trackZetaDelta_955_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*7);
v_zetaDeltaSet_956_ = lean_ctor_get(v_a_935_, 1);
v_lctx_957_ = lean_ctor_get(v_a_935_, 2);
v_localInstances_958_ = lean_ctor_get(v_a_935_, 3);
v_defEqCtx_x3f_959_ = lean_ctor_get(v_a_935_, 4);
v_synthPendingDepth_960_ = lean_ctor_get(v_a_935_, 5);
v_customCanUnfoldPredicate_x3f_961_ = lean_ctor_get(v_a_935_, 6);
v_univApprox_962_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_963_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*7 + 2);
v_cacheInferType_964_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*7 + 3);
lean_inc_ref(v_e_931_);
v___x_965_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_931_, v_a_936_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
lean_inc_ref(v_keyedConfig_954_);
v___x_967_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_952_, v_keyedConfig_954_);
lean_inc(v_customCanUnfoldPredicate_x3f_961_);
lean_inc(v_synthPendingDepth_960_);
lean_inc(v_defEqCtx_x3f_959_);
lean_inc_ref(v_localInstances_958_);
lean_inc_ref(v_lctx_957_);
lean_inc(v_zetaDeltaSet_956_);
v___x_968_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_zetaDeltaSet_956_);
lean_ctor_set(v___x_968_, 2, v_lctx_957_);
lean_ctor_set(v___x_968_, 3, v_localInstances_958_);
lean_ctor_set(v___x_968_, 4, v_defEqCtx_x3f_959_);
lean_ctor_set(v___x_968_, 5, v_synthPendingDepth_960_);
lean_ctor_set(v___x_968_, 6, v_customCanUnfoldPredicate_x3f_961_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*7, v_trackZetaDelta_955_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*7 + 1, v_univApprox_962_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*7 + 2, v_inTypeClassResolution_963_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*7 + 3, v_cacheInferType_964_);
v___x_969_ = l_Lean_Expr_cleanupAnnotations(v_a_966_);
v___x_970_ = l_Lean_Expr_isApp(v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref(v___x_969_);
lean_dec_ref(v_e_931_);
v___x_971_ = lean_box(0);
v___x_972_ = l_reduceCtorEq___lam__0(v___x_971_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
v___y_941_ = v___x_972_;
goto v___jp_940_;
}
else
{
lean_object* v_arg_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_arg_973_ = lean_ctor_get(v___x_969_, 1);
lean_inc_ref(v_arg_973_);
v___x_974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_969_);
v___x_975_ = l_Lean_Expr_isApp(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_e_931_);
v___x_976_ = lean_box(0);
v___x_977_ = l_reduceCtorEq___lam__0(v___x_976_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
v___y_941_ = v___x_977_;
goto v___jp_940_;
}
else
{
lean_object* v_arg_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_arg_978_ = lean_ctor_get(v___x_974_, 1);
lean_inc_ref(v_arg_978_);
v___x_979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_974_);
v___x_980_ = l_Lean_Expr_isApp(v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v___x_979_);
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_e_931_);
v___x_981_ = lean_box(0);
v___x_982_ = l_reduceCtorEq___lam__0(v___x_981_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
v___y_941_ = v___x_982_;
goto v___jp_940_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_979_);
v___x_984_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_985_ = l_Lean_Expr_isConstOf(v___x_983_, v___x_984_);
lean_dec_ref(v___x_983_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_arg_978_);
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_e_931_);
v___x_986_ = lean_box(0);
v___x_987_ = l_reduceCtorEq___lam__0(v___x_986_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
v___y_941_ = v___x_987_;
goto v___jp_940_;
}
else
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_978_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_973_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_990_) == 0)
{
if (lean_obj_tag(v_a_989_) == 1)
{
lean_object* v_val_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1016_; 
v_val_991_ = lean_ctor_get(v_a_989_, 0);
v_a_992_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 1)
{
lean_object* v_val_996_; lean_object* v_fst_997_; lean_object* v_toConstantVal_998_; lean_object* v_fst_999_; lean_object* v_toConstantVal_1000_; lean_object* v_name_1001_; lean_object* v_name_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; uint8_t v___y_1007_; uint8_t v___x_1014_; 
lean_inc(v_val_991_);
lean_dec_ref_known(v_a_989_, 1);
v_val_996_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v_a_992_, 1);
v_fst_997_ = lean_ctor_get(v_val_991_, 0);
lean_inc(v_fst_997_);
lean_dec(v_val_991_);
v_toConstantVal_998_ = lean_ctor_get(v_fst_997_, 0);
lean_inc_ref(v_toConstantVal_998_);
lean_dec(v_fst_997_);
v_fst_999_ = lean_ctor_get(v_val_996_, 0);
lean_inc(v_fst_999_);
lean_dec(v_val_996_);
v_toConstantVal_1000_ = lean_ctor_get(v_fst_999_, 0);
lean_inc_ref(v_toConstantVal_1000_);
lean_dec(v_fst_999_);
v_name_1001_ = lean_ctor_get(v_toConstantVal_998_, 0);
lean_inc(v_name_1001_);
lean_dec_ref(v_toConstantVal_998_);
v_name_1002_ = lean_ctor_get(v_toConstantVal_1000_, 0);
lean_inc(v_name_1002_);
lean_dec_ref(v_toConstantVal_1000_);
v___x_1003_ = lean_box(v___x_953_);
v___x_1004_ = lean_box(v___x_985_);
v___f_1005_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1005_, 0, v___x_1003_);
lean_closure_set(v___f_1005_, 1, v___x_1004_);
v___x_1014_ = lean_name_eq(v_name_1001_, v_name_1002_);
lean_dec(v_name_1002_);
lean_dec(v_name_1001_);
if (v___x_1014_ == 0)
{
v___y_1007_ = v___x_985_;
goto v___jp_1006_;
}
else
{
v___y_1007_ = v___x_953_;
goto v___jp_1006_;
}
v___jp_1006_:
{
if (v___y_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec_ref(v___f_1005_);
lean_dec_ref_known(v___x_968_, 7);
lean_dec_ref(v_e_931_);
v___x_1008_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1008_);
v___x_1010_ = v___x_994_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_994_);
v___x_1012_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_1013_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1012_, v_e_931_, v___f_1005_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
v___y_941_ = v___x_1013_;
goto v___jp_940_;
}
}
}
else
{
lean_object* v___x_1015_; 
lean_del_object(v___x_994_);
lean_dec_ref(v_e_931_);
v___x_1015_ = l_reduceCtorEq___lam__1(v_a_989_, v_a_992_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
lean_dec(v_a_992_);
lean_dec_ref_known(v_a_989_, 1);
v___y_941_ = v___x_1015_;
goto v___jp_940_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
lean_dec_ref(v_e_931_);
v_a_1017_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_990_, 1);
v___x_1018_ = l_reduceCtorEq___lam__1(v_a_989_, v_a_1017_, v_a_932_, v_a_933_, v_a_934_, v___x_968_, v_a_936_, v_a_937_, v_a_938_);
lean_dec_ref_known(v___x_968_, 7);
lean_dec(v_a_1017_);
lean_dec(v_a_989_);
v___y_941_ = v___x_1018_;
goto v___jp_940_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_989_);
lean_dec_ref_known(v___x_968_, 7);
lean_dec_ref(v_e_931_);
v_a_1019_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_990_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_990_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_arg_973_);
lean_dec_ref_known(v___x_968_, 7);
lean_dec_ref(v_e_931_);
v_a_1027_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_988_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_988_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
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
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_e_931_);
v_a_1035_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_965_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_965_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v___x_1043_; 
lean_inc_ref(v_e_931_);
v___x_1043_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_931_, v_a_936_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_Lean_Expr_cleanupAnnotations(v_a_1044_);
v___x_1046_ = l_Lean_Expr_isApp(v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_e_931_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_reduceCtorEq___lam__0(v___x_1047_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
v___y_941_ = v___x_1048_;
goto v___jp_940_;
}
else
{
lean_object* v_arg_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_arg_1049_ = lean_ctor_get(v___x_1045_, 1);
lean_inc_ref(v_arg_1049_);
v___x_1050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1045_);
v___x_1051_ = l_Lean_Expr_isApp(v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_e_931_);
v___x_1052_ = lean_box(0);
v___x_1053_ = l_reduceCtorEq___lam__0(v___x_1052_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
v___y_941_ = v___x_1053_;
goto v___jp_940_;
}
else
{
lean_object* v_arg_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_arg_1054_ = lean_ctor_get(v___x_1050_, 1);
lean_inc_ref(v_arg_1054_);
v___x_1055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1050_);
v___x_1056_ = l_Lean_Expr_isApp(v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_e_931_);
v___x_1057_ = lean_box(0);
v___x_1058_ = l_reduceCtorEq___lam__0(v___x_1057_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
v___y_941_ = v___x_1058_;
goto v___jp_940_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1055_);
v___x_1060_ = ((lean_object*)(l_reduceCtorEq___closed__1));
v___x_1061_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1060_);
lean_dec_ref(v___x_1059_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_e_931_);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_reduceCtorEq___lam__0(v___x_1062_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
v___y_941_ = v___x_1063_;
goto v___jp_940_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1054_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l_Lean_Meta_constructorApp_x27_x3f(v_arg_1049_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1066_) == 0)
{
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1090_; 
v_val_1067_ = lean_ctor_get(v_a_1065_, 0);
v_a_1068_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1090_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1090_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
if (lean_obj_tag(v_a_1068_) == 1)
{
lean_object* v_val_1072_; lean_object* v_fst_1073_; lean_object* v_toConstantVal_1074_; lean_object* v_fst_1075_; lean_object* v_toConstantVal_1076_; lean_object* v_name_1077_; lean_object* v_name_1078_; uint8_t v___x_1079_; 
lean_inc(v_val_1067_);
lean_dec_ref_known(v_a_1065_, 1);
v_val_1072_ = lean_ctor_get(v_a_1068_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v_a_1068_, 1);
v_fst_1073_ = lean_ctor_get(v_val_1067_, 0);
lean_inc(v_fst_1073_);
lean_dec(v_val_1067_);
v_toConstantVal_1074_ = lean_ctor_get(v_fst_1073_, 0);
lean_inc_ref(v_toConstantVal_1074_);
lean_dec(v_fst_1073_);
v_fst_1075_ = lean_ctor_get(v_val_1072_, 0);
lean_inc(v_fst_1075_);
lean_dec(v_val_1072_);
v_toConstantVal_1076_ = lean_ctor_get(v_fst_1075_, 0);
lean_inc_ref(v_toConstantVal_1076_);
lean_dec(v_fst_1075_);
v_name_1077_ = lean_ctor_get(v_toConstantVal_1074_, 0);
lean_inc(v_name_1077_);
lean_dec_ref(v_toConstantVal_1074_);
v_name_1078_ = lean_ctor_get(v_toConstantVal_1076_, 0);
lean_inc(v_name_1078_);
lean_dec_ref(v_toConstantVal_1076_);
v___x_1079_ = lean_name_eq(v_name_1077_, v_name_1078_);
lean_dec(v_name_1078_);
lean_dec(v_name_1077_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_del_object(v___x_1070_);
v___x_1080_ = lean_box(v___x_1079_);
v___x_1081_ = lean_box(v___x_1061_);
v___f_1082_ = lean_alloc_closure((void*)(l_reduceCtorEq___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1082_, 0, v___x_1080_);
lean_closure_set(v___f_1082_, 1, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_reduceCtorEq___closed__3));
v___x_1084_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_1083_, v_e_931_, v___f_1082_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
v___y_941_ = v___x_1084_;
goto v___jp_940_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec_ref(v_e_931_);
v___x_1085_ = ((lean_object*)(l_reduceIte___closed__0));
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1085_);
v___x_1087_ = v___x_1070_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v___x_1089_; 
lean_del_object(v___x_1070_);
lean_dec_ref(v_e_931_);
v___x_1089_ = l_reduceCtorEq___lam__1(v_a_1065_, v_a_1068_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_1068_);
lean_dec_ref_known(v_a_1065_, 1);
v___y_941_ = v___x_1089_;
goto v___jp_940_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_e_931_);
v_a_1091_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1092_ = l_reduceCtorEq___lam__1(v_a_1065_, v_a_1091_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_1091_);
lean_dec(v_a_1065_);
v___y_941_ = v___x_1092_;
goto v___jp_940_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v_a_1065_);
lean_dec_ref(v_e_931_);
v_a_1093_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1066_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1066_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_e_931_);
v_a_1101_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1064_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1064_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
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
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_e_931_);
v_a_1109_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1043_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1043_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
v___jp_940_:
{
if (lean_obj_tag(v___y_941_) == 0)
{
return v___y_941_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___y_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___y_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___y_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___y_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_reduceCtorEq___boxed(lean_object* v_e_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_reduceCtorEq(v_e_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_1127_, lean_object* v_name_1128_, uint8_t v_bi_1129_, lean_object* v_type_1130_, lean_object* v_k_1131_, uint8_t v_kind_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_1128_, v_bi_1129_, v_type_1130_, v_k_1131_, v_kind_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_name_1143_, lean_object* v_bi_1144_, lean_object* v_type_1145_, lean_object* v_k_1146_, lean_object* v_kind_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_bi_boxed_1156_; uint8_t v_kind_boxed_1157_; lean_object* v_res_1158_; 
v_bi_boxed_1156_ = lean_unbox(v_bi_1144_);
v_kind_boxed_1157_ = lean_unbox(v_kind_1147_);
v_res_1158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_1142_, v_name_1143_, v_bi_boxed_1156_, v_type_1145_, v_k_1146_, v_kind_boxed_1157_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(lean_object* v_00_u03b1_1159_, lean_object* v_name_1160_, lean_object* v_type_1161_, lean_object* v_k_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v_name_1160_, v_type_1161_, v_k_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1171_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23____boxed(lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_();
return v_res_1205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_alloc_closure((void*)(l_reduceCtorEq___boxed), 9, 0);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1210_ = 1;
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1212_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1209_, v___x_1210_, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25____boxed(lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_();
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_23_));
v___x_1217_ = 1;
v___x_1218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_25_);
v___x_1219_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1216_, v___x_1217_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27____boxed(lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3278911854____hygCtx___hyg_27_();
return v_res_1221_;
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
