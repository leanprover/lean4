// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
// Imports: public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt
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
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Char_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Char_reduceUnary___redArg___closed__0 = (const lean_object*)&l_Char_reduceUnary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Char_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Char_reduceBinPred___redArg___closed__0 = (const lean_object*)&l_Char_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Char_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Char_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l_Char_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l_Char_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Char_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l_Char_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Char_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Char_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l_Char_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l_Char_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceBoolPred___redArg___closed__3;
static const lean_string_object l_Char_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Char_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l_Char_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l_Char_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Char_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Char_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Char_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l_Char_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l_Char_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Char_reduceToLower___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Char_reduceToLower___redArg___closed__0 = (const lean_object*)&l_Char_reduceToLower___redArg___closed__0_value;
static const lean_string_object l_Char_reduceToLower___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toLower"};
static const lean_object* l_Char_reduceToLower___redArg___closed__1 = (const lean_object*)&l_Char_reduceToLower___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceToLower___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToLower___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceToLower___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 99, 124, 56, 54, 25, 183, 82)}};
static const lean_object* l_Char_reduceToLower___redArg___closed__2 = (const lean_object*)&l_Char_reduceToLower___redArg___closed__2_value;
static const lean_string_object l_Char_reduceToLower___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Char_reduceToLower___redArg___closed__3 = (const lean_object*)&l_Char_reduceToLower___redArg___closed__3_value;
static const lean_ctor_object l_Char_reduceToLower___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToLower___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__4_value_aux_0),((lean_object*)&l_Char_reduceToLower___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Char_reduceToLower___redArg___closed__4 = (const lean_object*)&l_Char_reduceToLower___redArg___closed__4_value;
static lean_once_cell_t l_Char_reduceToLower___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceToLower___redArg___closed__5;
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceToLower"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(246, 164, 69, 44, 68, 154, 164, 206)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceToUpper___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toUpper"};
static const lean_object* l_Char_reduceToUpper___redArg___closed__0 = (const lean_object*)&l_Char_reduceToUpper___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceToUpper___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToUpper___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceToUpper___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 31, 99, 242, 138, 166, 22, 89)}};
static const lean_object* l_Char_reduceToUpper___redArg___closed__1 = (const lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceToUpper"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(19, 136, 219, 72, 237, 65, 146, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceToNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Char_reduceToNat___redArg___closed__0 = (const lean_object*)&l_Char_reduceToNat___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceToNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceToNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 141, 246, 182, 101, 131, 69)}};
static const lean_object* l_Char_reduceToNat___redArg___closed__1 = (const lean_object*)&l_Char_reduceToNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceToNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(69, 114, 185, 38, 145, 239, 81, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToNat___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsWhitespace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isWhitespace"};
static const lean_object* l_Char_reduceIsWhitespace___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsWhitespace___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 198, 33, 133, 239, 7, 155, 87)}};
static const lean_object* l_Char_reduceIsWhitespace___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "reduceIsWhitespace"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(136, 194, 231, 0, 63, 197, 245, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsUpper___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isUpper"};
static const lean_object* l_Char_reduceIsUpper___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsUpper___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsUpper___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsUpper___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsUpper___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 247, 101, 132, 107, 237, 7, 181)}};
static const lean_object* l_Char_reduceIsUpper___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsUpper"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(48, 97, 102, 45, 130, 126, 188, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsLower___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isLower"};
static const lean_object* l_Char_reduceIsLower___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsLower___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsLower___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsLower___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 68, 161, 26, 43, 169, 19, 246)}};
static const lean_object* l_Char_reduceIsLower___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsLower"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(170, 130, 124, 235, 92, 103, 233, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsAlpha___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isAlpha"};
static const lean_object* l_Char_reduceIsAlpha___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsAlpha___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsAlpha___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 26, 253, 231, 184, 82, 201, 49)}};
static const lean_object* l_Char_reduceIsAlpha___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsAlpha"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(203, 178, 144, 111, 26, 233, 147, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsDigit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isDigit"};
static const lean_object* l_Char_reduceIsDigit___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsDigit___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsDigit___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsDigit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsDigit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 3, 214, 114, 123, 37, 169, 158)}};
static const lean_object* l_Char_reduceIsDigit___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsDigit"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(210, 158, 243, 105, 248, 216, 59, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsAlphaNum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isAlphanum"};
static const lean_object* l_Char_reduceIsAlphaNum___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsAlphaNum___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 189, 120, 149, 13, 219, 127, 87)}};
static const lean_object* l_Char_reduceIsAlphaNum___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceIsAlphaNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(92, 41, 179, 36, 218, 131, 154, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToString"};
static const lean_object* l_Char_reduceToString___redArg___closed__0 = (const lean_object*)&l_Char_reduceToString___redArg___closed__0_value;
static const lean_string_object l_Char_reduceToString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l_Char_reduceToString___redArg___closed__1 = (const lean_object*)&l_Char_reduceToString___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceToString___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToString___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 202, 174, 203, 16, 186, 159, 168)}};
static const lean_ctor_object l_Char_reduceToString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToString___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceToString___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(206, 210, 39, 124, 69, 192, 37, 107)}};
static const lean_object* l_Char_reduceToString___redArg___closed__2 = (const lean_object*)&l_Char_reduceToString___redArg___closed__2_value;
static const lean_string_object l_Char_reduceToString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Char_reduceToString___redArg___closed__3 = (const lean_object*)&l_Char_reduceToString___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceToString"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(78, 126, 108, 201, 251, 160, 71, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToString___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20____boxed(lean_object*);
static const lean_string_object l_Char_reduceVal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Char_reduceVal___redArg___closed__0 = (const lean_object*)&l_Char_reduceVal___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceVal___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceVal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceVal___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceVal___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 121, 142, 57, 80, 29, 36, 131)}};
static const lean_object* l_Char_reduceVal___redArg___closed__1 = (const lean_object*)&l_Char_reduceVal___redArg___closed__1_value;
static const lean_string_object l_Char_reduceVal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Char_reduceVal___redArg___closed__2 = (const lean_object*)&l_Char_reduceVal___redArg___closed__2_value;
static const lean_ctor_object l_Char_reduceVal___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceVal___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Char_reduceVal___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceVal___redArg___closed__3_value_aux_0),((lean_object*)&l_Char_reduceToLower___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Char_reduceVal___redArg___closed__3 = (const lean_object*)&l_Char_reduceVal___redArg___closed__3_value;
static lean_once_cell_t l_Char_reduceVal___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceVal___redArg___closed__4;
static lean_once_cell_t l_Char_reduceVal___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceVal___redArg___closed__5;
static lean_once_cell_t l_Char_reduceVal___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceVal___redArg___closed__6;
static const lean_string_object l_Char_reduceVal___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Char_reduceVal___redArg___closed__7 = (const lean_object*)&l_Char_reduceVal___redArg___closed__7_value;
static const lean_ctor_object l_Char_reduceVal___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceVal___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Char_reduceVal___redArg___closed__8 = (const lean_object*)&l_Char_reduceVal___redArg___closed__8_value;
static lean_once_cell_t l_Char_reduceVal___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceVal___redArg___closed__9;
static const lean_string_object l_Char_reduceVal___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Char_reduceVal___redArg___closed__10 = (const lean_object*)&l_Char_reduceVal___redArg___closed__10_value;
static const lean_ctor_object l_Char_reduceVal___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceVal___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Char_reduceVal___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceVal___redArg___closed__11_value_aux_0),((lean_object*)&l_Char_reduceVal___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l_Char_reduceVal___redArg___closed__11 = (const lean_object*)&l_Char_reduceVal___redArg___closed__11_value;
static lean_once_cell_t l_Char_reduceVal___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceVal___redArg___closed__12;
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceVal"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(221, 110, 235, 101, 86, 206, 196, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 6}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Char_reduceLT___redArg___closed__0 = (const lean_object*)&l_Char_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Char_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Char_reduceLT___redArg___closed__1 = (const lean_object*)&l_Char_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Char_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Char_reduceLT___redArg___closed__2 = (const lean_object*)&l_Char_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(79, 159, 98, 241, 171, 227, 76, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Char_reduceLE___redArg___closed__0 = (const lean_object*)&l_Char_reduceLE___redArg___closed__0_value;
static const lean_string_object l_Char_reduceLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Char_reduceLE___redArg___closed__1 = (const lean_object*)&l_Char_reduceLE___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Char_reduceLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceLE___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceLE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Char_reduceLE___redArg___closed__2 = (const lean_object*)&l_Char_reduceLE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(89, 169, 124, 250, 37, 125, 125, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Char_reduceGT___redArg___closed__0 = (const lean_object*)&l_Char_reduceGT___redArg___closed__0_value;
static const lean_string_object l_Char_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Char_reduceGT___redArg___closed__1 = (const lean_object*)&l_Char_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Char_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Char_reduceGT___redArg___closed__2 = (const lean_object*)&l_Char_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(41, 5, 154, 136, 195, 43, 53, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceGE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Char_reduceGE___redArg___closed__0 = (const lean_object*)&l_Char_reduceGE___redArg___closed__0_value;
static const lean_string_object l_Char_reduceGE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Char_reduceGE___redArg___closed__1 = (const lean_object*)&l_Char_reduceGE___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceGE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceGE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Char_reduceGE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceGE___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceGE___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Char_reduceGE___redArg___closed__2 = (const lean_object*)&l_Char_reduceGE___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(100, 184, 21, 249, 88, 153, 169, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Char_reduceEq___redArg___closed__0 = (const lean_object*)&l_Char_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Char_reduceEq___redArg___closed__1 = (const lean_object*)&l_Char_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(230, 148, 129, 250, 225, 177, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Char_reduceNe___redArg___closed__0 = (const lean_object*)&l_Char_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Char_reduceNe___redArg___closed__1 = (const lean_object*)&l_Char_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(141, 192, 11, 11, 58, 38, 59, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Char_reduceBEq___redArg___closed__0 = (const lean_object*)&l_Char_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_Char_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Char_reduceBEq___redArg___closed__1 = (const lean_object*)&l_Char_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Char_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Char_reduceBEq___redArg___closed__2 = (const lean_object*)&l_Char_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(170, 11, 99, 162, 42, 194, 168, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Char_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Char_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Char_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Char_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(244, 16, 149, 45, 21, 105, 48, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(123, 237, 132, 188, 163, 148, 231, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Char_reduceOfNatAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNatAux"};
static const lean_object* l_Char_reduceOfNatAux___redArg___closed__0 = (const lean_object*)&l_Char_reduceOfNatAux___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceOfNatAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 234, 215, 212, 41, 156, 42, 184)}};
static const lean_object* l_Char_reduceOfNatAux___redArg___closed__1 = (const lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceOfNatAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(181, 57, 32, 171, 55, 79, 143, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Char_reduceDefault___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Char_reduceDefault___redArg___closed__0 = (const lean_object*)&l_Char_reduceDefault___redArg___closed__0_value;
static const lean_string_object l_Char_reduceDefault___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Char_reduceDefault___redArg___closed__1 = (const lean_object*)&l_Char_reduceDefault___redArg___closed__1_value;
static const lean_ctor_object l_Char_reduceDefault___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceDefault___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l_Char_reduceDefault___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceDefault___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_reduceDefault___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l_Char_reduceDefault___redArg___closed__2 = (const lean_object*)&l_Char_reduceDefault___redArg___closed__2_value;
static lean_once_cell_t l_Char_reduceDefault___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceDefault___redArg___closed__3;
static lean_once_cell_t l_Char_reduceDefault___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceDefault___redArg___closed__4;
static lean_once_cell_t l_Char_reduceDefault___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_reduceDefault___redArg___closed__5;
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceDefault"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(24, 117, 54, 198, 106, 75, 186, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceDefault___redArg___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(uint32_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__0 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value;
static const lean_string_object l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "digitChar"};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__1 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value;
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 147, 212, 79, 88, 204, 199, 90)}};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__2 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17;
static lean_once_cell_t l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__3;
static const lean_string_object l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "digitChar_ne"};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__4 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value;
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(77, 94, 54, 151, 131, 127, 181, 182)}};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__5 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value;
static lean_once_cell_t l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__6;
static const lean_string_object l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__7 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value;
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__8 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__8_value;
static lean_once_cell_t l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__9;
static const lean_string_object l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__10 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value;
static const lean_ctor_object l_Char_Nat_reduceDigitCharEq___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__11 = (const lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__11_value;
static lean_once_cell_t l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceDigitCharEq___redArg___closed__12;
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceDigitCharEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 192, 151, 97, 108, 193, 18, 29)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(74, 133, 65, 18, 82, 189, 182, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27____boxed(lean_object*);
static const lean_string_object l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__0 = (const lean_object*)&l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value;
static const lean_ctor_object l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_ctor_object l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 137, 24, 74, 49, 62, 0, 94)}};
static const lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__1 = (const lean_object*)&l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value;
static lean_once_cell_t l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__2;
static lean_once_cell_t l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__3;
static lean_once_cell_t l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__4;
static lean_once_cell_t l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_Nat_reduceEqDigitChar___redArg___closed__5;
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceEqDigitChar"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 192, 151, 97, 108, 193, 18, 29)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(239, 45, 189, 47, 73, 225, 5, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getCharValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Char_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getCharValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Char_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Char_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg(lean_object* v_inst_37_, lean_object* v_declName_38_, lean_object* v_op_39_, lean_object* v_arity_40_, lean_object* v_e_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Lean_Expr_isAppOfArity(v_e_41_, v_declName_38_, v_arity_40_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_op_39_);
lean_dec_ref(v_inst_37_);
v___x_48_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Lean_Expr_appArg_x21(v_e_41_);
v___x_51_ = l_Lean_Meta_getCharValue_x3f(v___x_50_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_74_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_74_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_74_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_74_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
if (lean_obj_tag(v_a_52_) == 1)
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_69_; 
v_val_56_ = lean_ctor_get(v_a_52_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_a_52_);
if (v_isSharedCheck_69_ == 0)
{
v___x_58_ = v_a_52_;
v_isShared_59_ = v_isSharedCheck_69_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_a_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_69_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_toExpr_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v_toExpr_60_ = lean_ctor_get(v_inst_37_, 0);
lean_inc_ref(v_toExpr_60_);
lean_dec_ref(v_inst_37_);
v___x_61_ = lean_apply_1(v_op_39_, v_val_56_);
v___x_62_ = lean_apply_1(v_toExpr_60_, v___x_61_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 0);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_64_ = v___x_58_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_68_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_64_);
v___x_66_ = v___x_54_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_72_; 
lean_dec(v_a_52_);
lean_dec(v_op_39_);
lean_dec_ref(v_inst_37_);
v___x_70_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_70_);
v___x_72_ = v___x_54_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_op_39_);
lean_dec_ref(v_inst_37_);
v_a_75_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_51_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_51_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___redArg___boxed(lean_object* v_inst_83_, lean_object* v_declName_84_, lean_object* v_op_85_, lean_object* v_arity_86_, lean_object* v_e_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Char_reduceUnary___redArg(v_inst_83_, v_declName_84_, v_op_85_, v_arity_86_, v_e_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec_ref(v_e_87_);
lean_dec(v_declName_84_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_declName_96_, lean_object* v_op_97_, lean_object* v_arity_98_, lean_object* v_e_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_Expr_isAppOfArity(v_e_99_, v_declName_96_, v_arity_98_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_op_97_);
lean_dec_ref(v_inst_95_);
v___x_109_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = l_Lean_Expr_appArg_x21(v_e_99_);
v___x_112_ = l_Lean_Meta_getCharValue_x3f(v___x_111_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_135_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_135_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_135_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_135_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
if (lean_obj_tag(v_a_113_) == 1)
{
lean_object* v_val_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_130_; 
v_val_117_ = lean_ctor_get(v_a_113_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_a_113_);
if (v_isSharedCheck_130_ == 0)
{
v___x_119_ = v_a_113_;
v_isShared_120_ = v_isSharedCheck_130_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_val_117_);
lean_dec(v_a_113_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_130_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_toExpr_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v_toExpr_121_ = lean_ctor_get(v_inst_95_, 0);
lean_inc_ref(v_toExpr_121_);
lean_dec_ref(v_inst_95_);
v___x_122_ = lean_apply_1(v_op_97_, v_val_117_);
v___x_123_ = lean_apply_1(v_toExpr_121_, v___x_122_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 0);
lean_ctor_set(v___x_119_, 0, v___x_123_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_125_);
v___x_127_ = v___x_115_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v_a_113_);
lean_dec(v_op_97_);
lean_dec_ref(v_inst_95_);
v___x_131_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_131_);
v___x_133_ = v___x_115_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_op_97_);
lean_dec_ref(v_inst_95_);
v_a_136_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_112_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_112_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceUnary___boxed(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_declName_146_, lean_object* v_op_147_, lean_object* v_arity_148_, lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Char_reduceUnary(v_00_u03b1_144_, v_inst_145_, v_declName_146_, v_op_147_, v_arity_148_, v_e_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_e_149_);
lean_dec(v_declName_146_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg(lean_object* v_declName_161_, lean_object* v_arity_162_, lean_object* v_op_163_, lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Expr_isAppOfArity(v_e_164_, v_declName_161_, v_arity_162_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v___x_171_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = l_Lean_Expr_appFn_x21(v_e_164_);
v___x_174_ = l_Lean_Expr_appArg_x21(v___x_173_);
lean_dec_ref(v___x_173_);
v___x_175_ = l_Lean_Meta_getCharValue_x3f(v___x_174_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_208_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_208_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_208_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_208_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
if (lean_obj_tag(v_a_176_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_del_object(v___x_178_);
v_val_180_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v_a_176_);
v___x_181_ = l_Lean_Expr_appArg_x21(v_e_164_);
v___x_182_ = l_Lean_Meta_getCharValue_x3f(v___x_181_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
if (lean_obj_tag(v_a_183_) == 1)
{
lean_object* v_val_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; 
lean_del_object(v___x_185_);
v_val_187_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v_a_183_);
v___x_188_ = lean_apply_2(v_op_163_, v_val_180_, v_val_187_);
v___x_189_ = lean_unbox(v___x_188_);
v___x_190_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_164_, v___x_189_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec(v_a_183_);
lean_dec(v_val_180_);
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v___x_191_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_191_);
v___x_193_ = v___x_185_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_val_180_);
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v_a_196_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_182_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_182_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_a_176_);
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v___x_204_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_204_);
v___x_206_ = v___x_178_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v_a_209_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_175_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_175_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred___redArg___boxed(lean_object* v_declName_217_, lean_object* v_arity_218_, lean_object* v_op_219_, lean_object* v_e_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Char_reduceBinPred___redArg(v_declName_217_, v_arity_218_, v_op_219_, v_e_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_declName_217_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred(lean_object* v_declName_227_, lean_object* v_arity_228_, lean_object* v_op_229_, lean_object* v_e_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Expr_isAppOfArity(v_e_230_, v_declName_227_, v_arity_228_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v___x_240_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = l_Lean_Expr_appFn_x21(v_e_230_);
v___x_243_ = l_Lean_Expr_appArg_x21(v___x_242_);
lean_dec_ref(v___x_242_);
v___x_244_ = l_Lean_Meta_getCharValue_x3f(v___x_243_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_277_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_277_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_277_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_277_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
if (lean_obj_tag(v_a_245_) == 1)
{
lean_object* v_val_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_del_object(v___x_247_);
v_val_249_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_val_249_);
lean_dec_ref(v_a_245_);
v___x_250_ = l_Lean_Expr_appArg_x21(v_e_230_);
v___x_251_ = l_Lean_Meta_getCharValue_x3f(v___x_250_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_264_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_264_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
if (lean_obj_tag(v_a_252_) == 1)
{
lean_object* v_val_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
lean_del_object(v___x_254_);
v_val_256_ = lean_ctor_get(v_a_252_, 0);
lean_inc(v_val_256_);
lean_dec_ref(v_a_252_);
v___x_257_ = lean_apply_2(v_op_229_, v_val_249_, v_val_256_);
v___x_258_ = lean_unbox(v___x_257_);
v___x_259_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_230_, v___x_258_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_a_252_);
lean_dec(v_val_249_);
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v___x_260_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_260_);
v___x_262_ = v___x_254_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_val_249_);
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v_a_265_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_251_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_251_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_dec(v_a_245_);
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v___x_273_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_273_);
v___x_275_ = v___x_247_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v_a_278_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_244_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_244_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBinPred___boxed(lean_object* v_declName_286_, lean_object* v_arity_287_, lean_object* v_op_288_, lean_object* v_e_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Char_reduceBinPred(v_declName_286_, v_arity_287_, v_op_288_, v_e_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec(v_declName_286_);
return v_res_298_;
}
}
static lean_object* _init_l_Char_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_box(0);
v___x_305_ = ((lean_object*)(l_Char_reduceBoolPred___redArg___closed__2));
v___x_306_ = l_Lean_mkConst(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_Char_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l_Char_reduceBoolPred___redArg___closed__5));
v___x_313_ = l_Lean_mkConst(v___x_312_, v___x_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg(lean_object* v_declName_314_, lean_object* v_arity_315_, lean_object* v_op_316_, lean_object* v_e_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Expr_isAppOfArity(v_e_317_, v_declName_314_, v_arity_315_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v_op_316_);
v___x_324_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_Expr_appFn_x21(v_e_317_);
v___x_327_ = l_Lean_Expr_appArg_x21(v___x_326_);
lean_dec_ref(v___x_326_);
v___x_328_ = l_Lean_Meta_getCharValue_x3f(v___x_327_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_374_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_374_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_374_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_374_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
if (lean_obj_tag(v_a_329_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_369_; 
v_val_333_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_369_ == 0)
{
v___x_335_ = v_a_329_;
v_isShared_336_ = v_isSharedCheck_369_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v_a_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_369_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_Expr_appArg_x21(v_e_317_);
v___x_338_ = l_Lean_Meta_getCharValue_x3f(v___x_337_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_360_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_360_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___y_344_; 
if (lean_obj_tag(v_a_339_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
lean_del_object(v___x_331_);
v_val_351_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_val_351_);
lean_dec_ref(v_a_339_);
v___x_352_ = lean_apply_2(v_op_316_, v_val_333_, v_val_351_);
v___x_353_ = lean_unbox(v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_344_ = v___x_354_;
goto v___jp_343_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_344_ = v___x_355_;
goto v___jp_343_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_op_316_);
v___x_356_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_356_);
v___x_358_ = v___x_331_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
v___jp_343_:
{
lean_object* v___x_346_; 
lean_inc_ref(v___y_344_);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 0);
lean_ctor_set(v___x_335_, 0, v___y_344_);
v___x_346_ = v___x_335_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___y_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_346_);
v___x_348_ = v___x_341_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_del_object(v___x_331_);
lean_dec_ref(v_op_316_);
v_a_361_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_338_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_338_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_372_; 
lean_dec(v_a_329_);
lean_dec_ref(v_op_316_);
v___x_370_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_370_);
v___x_372_ = v___x_331_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_op_316_);
v_a_375_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_328_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_328_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___redArg___boxed(lean_object* v_declName_383_, lean_object* v_arity_384_, lean_object* v_op_385_, lean_object* v_e_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Char_reduceBoolPred___redArg(v_declName_383_, v_arity_384_, v_op_385_, v_e_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec_ref(v_e_386_);
lean_dec(v_declName_383_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred(lean_object* v_declName_393_, lean_object* v_arity_394_, lean_object* v_op_395_, lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = l_Lean_Expr_isAppOfArity(v_e_396_, v_declName_393_, v_arity_394_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v_op_395_);
v___x_406_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = l_Lean_Expr_appFn_x21(v_e_396_);
v___x_409_ = l_Lean_Expr_appArg_x21(v___x_408_);
lean_dec_ref(v___x_408_);
v___x_410_ = l_Lean_Meta_getCharValue_x3f(v___x_409_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_456_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_456_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_456_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_456_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
if (lean_obj_tag(v_a_411_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_451_; 
v_val_415_ = lean_ctor_get(v_a_411_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_451_ == 0)
{
v___x_417_ = v_a_411_;
v_isShared_418_ = v_isSharedCheck_451_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v_a_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_451_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_Lean_Expr_appArg_x21(v_e_396_);
v___x_420_ = l_Lean_Meta_getCharValue_x3f(v___x_419_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
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
lean_object* v___y_426_; 
if (lean_obj_tag(v_a_421_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
lean_del_object(v___x_413_);
v_val_433_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_val_433_);
lean_dec_ref(v_a_421_);
v___x_434_ = lean_apply_2(v_op_395_, v_val_415_, v_val_433_);
v___x_435_ = lean_unbox(v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_426_ = v___x_437_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_del_object(v___x_423_);
lean_dec(v_a_421_);
lean_del_object(v___x_417_);
lean_dec(v_val_415_);
lean_dec_ref(v_op_395_);
v___x_438_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_438_);
v___x_440_ = v___x_413_;
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
v___jp_425_:
{
lean_object* v___x_428_; 
lean_inc_ref(v___y_426_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
lean_ctor_set(v___x_417_, 0, v___y_426_);
v___x_428_ = v___x_417_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___y_426_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_428_);
v___x_430_ = v___x_423_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_del_object(v___x_417_);
lean_dec(v_val_415_);
lean_del_object(v___x_413_);
lean_dec_ref(v_op_395_);
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
}
else
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec(v_a_411_);
lean_dec_ref(v_op_395_);
v___x_452_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_452_);
v___x_454_ = v___x_413_;
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
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_op_395_);
v_a_457_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_410_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_410_);
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
}
}
LEAN_EXPORT lean_object* l_Char_reduceBoolPred___boxed(lean_object* v_declName_465_, lean_object* v_arity_466_, lean_object* v_op_467_, lean_object* v_e_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Char_reduceBoolPred(v_declName_465_, v_arity_466_, v_op_467_, v_e_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_e_468_);
lean_dec(v_declName_465_);
return v_res_477_;
}
}
static lean_object* _init_l_Char_reduceToLower___redArg___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
v___x_488_ = ((lean_object*)(l_Char_reduceToLower___redArg___closed__4));
v___x_489_ = l_Lean_mkConst(v___x_488_, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg(lean_object* v_e_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = ((lean_object*)(l_Char_reduceToLower___redArg___closed__2));
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = l_Lean_Expr_isAppOfArity(v_e_490_, v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_Expr_appArg_x21(v_e_490_);
v___x_502_ = l_Lean_Meta_getCharValue_x3f(v___x_501_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_531_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_531_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_531_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint32_t v___y_508_; 
if (lean_obj_tag(v_a_503_) == 1)
{
lean_object* v_val_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint8_t v___x_520_; 
v_val_517_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_val_517_);
lean_dec_ref(v_a_503_);
v___x_518_ = 65;
v___x_519_ = lean_unbox_uint32(v_val_517_);
v___x_520_ = lean_uint32_dec_le(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
uint32_t v___x_521_; 
v___x_521_ = lean_unbox_uint32(v_val_517_);
lean_dec(v_val_517_);
v___y_508_ = v___x_521_;
goto v___jp_507_;
}
else
{
uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = 90;
v___x_523_ = lean_unbox_uint32(v_val_517_);
v___x_524_ = lean_uint32_dec_le(v___x_523_, v___x_522_);
if (v___x_524_ == 0)
{
uint32_t v___x_525_; 
v___x_525_ = lean_unbox_uint32(v_val_517_);
lean_dec(v_val_517_);
v___y_508_ = v___x_525_;
goto v___jp_507_;
}
else
{
uint32_t v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; 
v___x_526_ = 32;
v___x_527_ = lean_unbox_uint32(v_val_517_);
lean_dec(v_val_517_);
v___x_528_ = lean_uint32_add(v___x_527_, v___x_526_);
v___y_508_ = v___x_528_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
v___x_529_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_509_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_510_ = lean_uint32_to_nat(v___y_508_);
v___x_511_ = l_Lean_mkRawNatLit(v___x_510_);
v___x_512_ = l_Lean_Expr_app___override(v___x_509_, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_513_);
v___x_515_ = v___x_505_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_502_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_502_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Char_reduceToLower___redArg(v_e_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec_ref(v_e_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Char_reduceToLower___redArg(v_e_547_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Char_reduceToLower(v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_e_557_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_));
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_));
v___x_583_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_584_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13____boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_();
return v_res_586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_));
v___x_591_ = 1;
v___x_592_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_);
v___x_593_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_590_, v___x_591_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15____boxed(lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_));
v___x_598_ = 1;
v___x_599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_);
v___x_600_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_597_, v___x_598_, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17____boxed(lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_();
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = ((lean_object*)(l_Char_reduceToUpper___redArg___closed__1));
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = l_Lean_Expr_isAppOfArity(v_e_607_, v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = l_Lean_Expr_appArg_x21(v_e_607_);
v___x_619_ = l_Lean_Meta_getCharValue_x3f(v___x_618_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_648_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_648_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint32_t v___y_625_; 
if (lean_obj_tag(v_a_620_) == 1)
{
lean_object* v_val_634_; uint32_t v___x_635_; uint32_t v___x_636_; uint8_t v___x_637_; 
v_val_634_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_val_634_);
lean_dec_ref(v_a_620_);
v___x_635_ = 97;
v___x_636_ = lean_unbox_uint32(v_val_634_);
v___x_637_ = lean_uint32_dec_le(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
uint32_t v___x_638_; 
v___x_638_ = lean_unbox_uint32(v_val_634_);
lean_dec(v_val_634_);
v___y_625_ = v___x_638_;
goto v___jp_624_;
}
else
{
uint32_t v___x_639_; uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = 122;
v___x_640_ = lean_unbox_uint32(v_val_634_);
v___x_641_ = lean_uint32_dec_le(v___x_640_, v___x_639_);
if (v___x_641_ == 0)
{
uint32_t v___x_642_; 
v___x_642_ = lean_unbox_uint32(v_val_634_);
lean_dec(v_val_634_);
v___y_625_ = v___x_642_;
goto v___jp_624_;
}
else
{
uint32_t v___x_643_; uint32_t v___x_644_; uint32_t v___x_645_; 
v___x_643_ = 4294967264;
v___x_644_ = lean_unbox_uint32(v_val_634_);
lean_dec(v_val_634_);
v___x_645_ = lean_uint32_add(v___x_644_, v___x_643_);
v___y_625_ = v___x_645_;
goto v___jp_624_;
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_del_object(v___x_622_);
lean_dec(v_a_620_);
v___x_646_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_626_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_627_ = lean_uint32_to_nat(v___y_625_);
v___x_628_ = l_Lean_mkRawNatLit(v___x_627_);
v___x_629_ = l_Lean_Expr_app___override(v___x_626_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_630_);
v___x_632_ = v___x_622_;
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
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_649_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_619_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_619_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Char_reduceToUpper___redArg(v_e_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec_ref(v_e_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object* v_e_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Char_reduceToUpper___redArg(v_e_664_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Char_reduceToUpper(v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_e_674_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_));
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_));
v___x_700_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_701_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_698_, v___x_699_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13____boxed(lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_();
return v_res_703_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_));
v___x_708_ = 1;
v___x_709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_);
v___x_710_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_707_, v___x_708_, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15____boxed(lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_();
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_));
v___x_715_ = 1;
v___x_716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_);
v___x_717_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_714_, v___x_715_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17____boxed(lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_();
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = ((lean_object*)(l_Char_reduceToNat___redArg___closed__1));
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = l_Lean_Expr_isAppOfArity(v_e_724_, v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = l_Lean_Expr_appArg_x21(v_e_724_);
v___x_736_ = l_Lean_Meta_getCharValue_x3f(v___x_735_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_759_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_759_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_759_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_759_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
if (lean_obj_tag(v_a_737_) == 1)
{
lean_object* v_val_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_754_; 
v_val_741_ = lean_ctor_get(v_a_737_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_754_ == 0)
{
v___x_743_ = v_a_737_;
v_isShared_744_ = v_isSharedCheck_754_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_val_741_);
lean_dec(v_a_737_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_754_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint32_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = lean_unbox_uint32(v_val_741_);
lean_dec(v_val_741_);
v___x_746_ = lean_uint32_to_nat(v___x_745_);
v___x_747_ = l_Lean_mkNatLit(v___x_746_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 0);
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_749_);
v___x_751_ = v___x_739_;
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
}
else
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v_a_737_);
v___x_755_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_755_);
v___x_757_ = v___x_739_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
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
v_a_760_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_736_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_736_);
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
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object* v_e_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Char_reduceToNat___redArg(v_e_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec_ref(v_e_768_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object* v_e_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Char_reduceToNat___redArg(v_e_775_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object* v_e_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Char_reduceToNat(v_e_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_e_785_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_));
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_));
v___x_811_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_812_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_809_, v___x_810_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13____boxed(lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_();
return v_res_814_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_));
v___x_819_ = 1;
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_);
v___x_821_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_818_, v___x_819_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15____boxed(lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_();
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_));
v___x_826_ = 1;
v___x_827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_);
v___x_828_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_825_, v___x_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17____boxed(lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_();
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object* v_e_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = ((lean_object*)(l_Char_reduceIsWhitespace___redArg___closed__1));
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = l_Lean_Expr_isAppOfArity(v_e_835_, v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = l_Lean_Expr_appArg_x21(v_e_835_);
v___x_847_ = l_Lean_Meta_getCharValue_x3f(v___x_846_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_880_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_880_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_880_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_880_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___y_853_; uint8_t v___y_861_; 
if (lean_obj_tag(v_a_848_) == 1)
{
lean_object* v_val_863_; uint8_t v___y_865_; uint32_t v___x_872_; uint32_t v___x_873_; uint8_t v___x_874_; 
v_val_863_ = lean_ctor_get(v_a_848_, 0);
lean_inc(v_val_863_);
lean_dec_ref(v_a_848_);
v___x_872_ = 32;
v___x_873_ = lean_unbox_uint32(v_val_863_);
v___x_874_ = lean_uint32_dec_eq(v___x_873_, v___x_872_);
if (v___x_874_ == 0)
{
uint32_t v___x_875_; uint32_t v___x_876_; uint8_t v___x_877_; 
v___x_875_ = 9;
v___x_876_ = lean_unbox_uint32(v_val_863_);
v___x_877_ = lean_uint32_dec_eq(v___x_876_, v___x_875_);
v___y_865_ = v___x_877_;
goto v___jp_864_;
}
else
{
v___y_865_ = v___x_874_;
goto v___jp_864_;
}
v___jp_864_:
{
if (v___y_865_ == 0)
{
uint32_t v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = 13;
v___x_867_ = lean_unbox_uint32(v_val_863_);
v___x_868_ = lean_uint32_dec_eq(v___x_867_, v___x_866_);
if (v___x_868_ == 0)
{
uint32_t v___x_869_; uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_869_ = 10;
v___x_870_ = lean_unbox_uint32(v_val_863_);
lean_dec(v_val_863_);
v___x_871_ = lean_uint32_dec_eq(v___x_870_, v___x_869_);
v___y_861_ = v___x_871_;
goto v___jp_860_;
}
else
{
lean_dec(v_val_863_);
v___y_861_ = v___x_868_;
goto v___jp_860_;
}
}
else
{
lean_dec(v_val_863_);
goto v___jp_858_;
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_850_);
lean_dec(v_a_848_);
v___x_878_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_inc_ref(v___y_853_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___y_853_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
v___jp_858_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_853_ = v___x_859_;
goto v___jp_852_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_853_ = v___x_862_;
goto v___jp_852_;
}
else
{
goto v___jp_858_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_847_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_847_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object* v_e_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Char_reduceIsWhitespace___redArg(v_e_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec_ref(v_e_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object* v_e_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Char_reduceIsWhitespace___redArg(v_e_896_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object* v_e_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Char_reduceIsWhitespace(v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_e_906_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_));
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_));
v___x_932_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_933_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_930_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13____boxed(lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_();
return v_res_935_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_));
v___x_940_ = 1;
v___x_941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_);
v___x_942_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_939_, v___x_940_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15____boxed(lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_();
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_));
v___x_947_ = 1;
v___x_948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_);
v___x_949_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_946_, v___x_947_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17____boxed(lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_();
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_962_ = ((lean_object*)(l_Char_reduceIsUpper___redArg___closed__1));
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = l_Lean_Expr_isAppOfArity(v_e_956_, v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l_Lean_Expr_appArg_x21(v_e_956_);
v___x_968_ = l_Lean_Meta_getCharValue_x3f(v___x_967_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_991_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_991_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_991_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_991_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___y_974_; 
if (lean_obj_tag(v_a_969_) == 1)
{
lean_object* v_val_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint8_t v___x_984_; 
v_val_981_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_981_);
lean_dec_ref(v_a_969_);
v___x_982_ = 65;
v___x_983_ = lean_unbox_uint32(v_val_981_);
v___x_984_ = lean_uint32_dec_le(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_dec(v_val_981_);
goto v___jp_979_;
}
else
{
uint32_t v___x_985_; uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_985_ = 90;
v___x_986_ = lean_unbox_uint32(v_val_981_);
lean_dec(v_val_981_);
v___x_987_ = lean_uint32_dec_le(v___x_986_, v___x_985_);
if (v___x_987_ == 0)
{
goto v___jp_979_;
}
else
{
if (v___x_964_ == 0)
{
goto v___jp_979_;
}
else
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_974_ = v___x_988_;
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_del_object(v___x_971_);
lean_dec(v_a_969_);
v___x_989_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_inc_ref(v___y_974_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___y_974_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_975_);
v___x_977_ = v___x_971_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
v___jp_979_:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_974_ = v___x_980_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_968_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_968_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object* v_e_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Char_reduceIsUpper___redArg(v_e_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_e_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Char_reduceIsUpper___redArg(v_e_1007_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object* v_e_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Char_reduceIsUpper(v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_e_1017_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_));
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_));
v___x_1043_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1044_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1041_, v___x_1042_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13____boxed(lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_();
return v_res_1046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_));
v___x_1051_ = 1;
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_);
v___x_1053_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1050_, v___x_1051_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15____boxed(lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_();
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_));
v___x_1058_ = 1;
v___x_1059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_);
v___x_1060_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1057_, v___x_1058_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17____boxed(lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_();
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object* v_e_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = ((lean_object*)(l_Char_reduceIsLower___redArg___closed__1));
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = l_Lean_Expr_isAppOfArity(v_e_1067_, v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_Lean_Expr_appArg_x21(v_e_1067_);
v___x_1079_ = l_Lean_Meta_getCharValue_x3f(v___x_1078_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1103_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___y_1085_; uint8_t v___y_1091_; 
if (lean_obj_tag(v_a_1080_) == 1)
{
lean_object* v_val_1094_; uint32_t v___x_1095_; uint32_t v___x_1096_; uint8_t v___x_1097_; 
v_val_1094_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v_a_1080_);
v___x_1095_ = 97;
v___x_1096_ = lean_unbox_uint32(v_val_1094_);
v___x_1097_ = lean_uint32_dec_le(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec(v_val_1094_);
v___y_1091_ = v___x_1097_;
goto v___jp_1090_;
}
else
{
uint32_t v___x_1098_; uint32_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = 122;
v___x_1099_ = lean_unbox_uint32(v_val_1094_);
lean_dec(v_val_1094_);
v___x_1100_ = lean_uint32_dec_le(v___x_1099_, v___x_1098_);
v___y_1091_ = v___x_1100_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_del_object(v___x_1082_);
lean_dec(v_a_1080_);
v___x_1101_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_inc_ref(v___y_1085_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___y_1085_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
v___jp_1090_:
{
if (v___y_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_1085_ = v___x_1092_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_1085_ = v___x_1093_;
goto v___jp_1084_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1079_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1079_);
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
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Char_reduceIsLower___redArg(v_e_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_e_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object* v_e_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Char_reduceIsLower___redArg(v_e_1119_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object* v_e_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Char_reduceIsLower(v_e_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_e_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_));
v___x_1154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_));
v___x_1155_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1156_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1153_, v___x_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13____boxed(lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_();
return v_res_1158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_));
v___x_1163_ = 1;
v___x_1164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_);
v___x_1165_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1162_, v___x_1163_, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15____boxed(lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_();
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_));
v___x_1170_ = 1;
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_);
v___x_1172_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1169_, v___x_1170_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17____boxed(lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_();
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object* v_e_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = ((lean_object*)(l_Char_reduceIsAlpha___redArg___closed__1));
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = l_Lean_Expr_isAppOfArity(v_e_1179_, v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = l_Lean_Expr_appArg_x21(v_e_1179_);
v___x_1191_ = l_Lean_Meta_getCharValue_x3f(v___x_1190_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1222_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___y_1197_; uint8_t v___y_1203_; 
if (lean_obj_tag(v_a_1192_) == 1)
{
lean_object* v_val_1206_; uint32_t v___x_1214_; uint32_t v___x_1215_; uint8_t v___x_1216_; 
v_val_1206_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v_a_1192_);
v___x_1214_ = 65;
v___x_1215_ = lean_unbox_uint32(v_val_1206_);
v___x_1216_ = lean_uint32_dec_le(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
goto v___jp_1207_;
}
else
{
uint32_t v___x_1217_; uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = 90;
v___x_1218_ = lean_unbox_uint32(v_val_1206_);
v___x_1219_ = lean_uint32_dec_le(v___x_1218_, v___x_1217_);
if (v___x_1219_ == 0)
{
goto v___jp_1207_;
}
else
{
lean_dec(v_val_1206_);
v___y_1203_ = v___x_1187_;
goto v___jp_1202_;
}
}
v___jp_1207_:
{
uint32_t v___x_1208_; uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = 97;
v___x_1209_ = lean_unbox_uint32(v_val_1206_);
v___x_1210_ = lean_uint32_dec_le(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec(v_val_1206_);
v___y_1203_ = v___x_1210_;
goto v___jp_1202_;
}
else
{
uint32_t v___x_1211_; uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1211_ = 122;
v___x_1212_ = lean_unbox_uint32(v_val_1206_);
lean_dec(v_val_1206_);
v___x_1213_ = lean_uint32_dec_le(v___x_1212_, v___x_1211_);
v___y_1203_ = v___x_1213_;
goto v___jp_1202_;
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
v___x_1220_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_inc_ref(v___y_1197_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___y_1197_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
v___jp_1202_:
{
if (v___y_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_1197_ = v___x_1204_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_1197_ = v___x_1205_;
goto v___jp_1196_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1191_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1191_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object* v_e_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Char_reduceIsAlpha___redArg(v_e_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_e_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Char_reduceIsAlpha___redArg(v_e_1238_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object* v_e_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Char_reduceIsAlpha(v_e_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_e_1248_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_));
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_));
v___x_1274_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1275_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1272_, v___x_1273_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13____boxed(lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_();
return v_res_1277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_));
v___x_1282_ = 1;
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_);
v___x_1284_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15____boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_));
v___x_1289_ = 1;
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_);
v___x_1291_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17____boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_();
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = ((lean_object*)(l_Char_reduceIsDigit___redArg___closed__1));
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = l_Lean_Expr_isAppOfArity(v_e_1298_, v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = l_Lean_Expr_appArg_x21(v_e_1298_);
v___x_1310_ = l_Lean_Meta_getCharValue_x3f(v___x_1309_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1334_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1334_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1334_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___y_1316_; uint8_t v___y_1322_; 
if (lean_obj_tag(v_a_1311_) == 1)
{
lean_object* v_val_1325_; uint32_t v___x_1326_; uint32_t v___x_1327_; uint8_t v___x_1328_; 
v_val_1325_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_val_1325_);
lean_dec_ref(v_a_1311_);
v___x_1326_ = 48;
v___x_1327_ = lean_unbox_uint32(v_val_1325_);
v___x_1328_ = lean_uint32_dec_le(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec(v_val_1325_);
v___y_1322_ = v___x_1328_;
goto v___jp_1321_;
}
else
{
uint32_t v___x_1329_; uint32_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = 57;
v___x_1330_ = lean_unbox_uint32(v_val_1325_);
lean_dec(v_val_1325_);
v___x_1331_ = lean_uint32_dec_le(v___x_1330_, v___x_1329_);
v___y_1322_ = v___x_1331_;
goto v___jp_1321_;
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_del_object(v___x_1313_);
lean_dec(v_a_1311_);
v___x_1332_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
v___jp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc_ref(v___y_1316_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1316_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1317_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
v___jp_1321_:
{
if (v___y_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_1316_ = v___x_1323_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_1316_ = v___x_1324_;
goto v___jp_1315_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1310_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1310_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Char_reduceIsDigit___redArg(v_e_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec_ref(v_e_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object* v_e_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Char_reduceIsDigit___redArg(v_e_1350_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object* v_e_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Char_reduceIsDigit(v_e_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_e_1360_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_));
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_));
v___x_1386_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1387_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1384_, v___x_1385_, v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13____boxed(lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_();
return v_res_1389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_));
v___x_1394_ = 1;
v___x_1395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_);
v___x_1396_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1393_, v___x_1394_, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15____boxed(lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_();
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_));
v___x_1401_ = 1;
v___x_1402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_);
v___x_1403_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1400_, v___x_1401_, v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17____boxed(lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_();
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object* v_e_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = ((lean_object*)(l_Char_reduceIsAlphaNum___redArg___closed__1));
v___x_1417_ = lean_unsigned_to_nat(1u);
v___x_1418_ = l_Lean_Expr_isAppOfArity(v_e_1410_, v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = l_Lean_Expr_appArg_x21(v_e_1410_);
v___x_1422_ = l_Lean_Meta_getCharValue_x3f(v___x_1421_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1462_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1462_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1462_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___y_1428_; uint8_t v___y_1436_; 
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1438_; uint8_t v___y_1440_; uint32_t v___x_1454_; uint32_t v___x_1455_; uint8_t v___x_1456_; 
v_val_1438_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_val_1438_);
lean_dec_ref(v_a_1423_);
v___x_1454_ = 65;
v___x_1455_ = lean_unbox_uint32(v_val_1438_);
v___x_1456_ = lean_uint32_dec_le(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
goto v___jp_1447_;
}
else
{
uint32_t v___x_1457_; uint32_t v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = 90;
v___x_1458_ = lean_unbox_uint32(v_val_1438_);
v___x_1459_ = lean_uint32_dec_le(v___x_1458_, v___x_1457_);
if (v___x_1459_ == 0)
{
goto v___jp_1447_;
}
else
{
lean_dec(v_val_1438_);
v___y_1436_ = v___x_1418_;
goto v___jp_1435_;
}
}
v___jp_1439_:
{
if (v___y_1440_ == 0)
{
uint32_t v___x_1441_; uint32_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = 48;
v___x_1442_ = lean_unbox_uint32(v_val_1438_);
v___x_1443_ = lean_uint32_dec_le(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_dec(v_val_1438_);
v___y_1436_ = v___x_1443_;
goto v___jp_1435_;
}
else
{
uint32_t v___x_1444_; uint32_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = 57;
v___x_1445_ = lean_unbox_uint32(v_val_1438_);
lean_dec(v_val_1438_);
v___x_1446_ = lean_uint32_dec_le(v___x_1445_, v___x_1444_);
v___y_1436_ = v___x_1446_;
goto v___jp_1435_;
}
}
else
{
lean_dec(v_val_1438_);
goto v___jp_1433_;
}
}
v___jp_1447_:
{
uint32_t v___x_1448_; uint32_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = 97;
v___x_1449_ = lean_unbox_uint32(v_val_1438_);
v___x_1450_ = lean_uint32_dec_le(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
v___y_1440_ = v___x_1450_;
goto v___jp_1439_;
}
else
{
uint32_t v___x_1451_; uint32_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1451_ = 122;
v___x_1452_ = lean_unbox_uint32(v_val_1438_);
v___x_1453_ = lean_uint32_dec_le(v___x_1452_, v___x_1451_);
v___y_1440_ = v___x_1453_;
goto v___jp_1439_;
}
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_del_object(v___x_1425_);
lean_dec(v_a_1423_);
v___x_1460_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc_ref(v___y_1428_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___y_1428_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1429_);
v___x_1431_ = v___x_1425_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
v___jp_1433_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_1428_ = v___x_1434_;
goto v___jp_1427_;
}
v___jp_1435_:
{
if (v___y_1436_ == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_1428_ = v___x_1437_;
goto v___jp_1427_;
}
else
{
goto v___jp_1433_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1463_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1422_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1422_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object* v_e_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Char_reduceIsAlphaNum___redArg(v_e_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_e_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Char_reduceIsAlphaNum___redArg(v_e_1478_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Char_reduceIsAlphaNum(v_e_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_e_1488_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_));
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_));
v___x_1514_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1515_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1512_, v___x_1513_, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13____boxed(lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_();
return v_res_1517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_));
v___x_1522_ = 1;
v___x_1523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_);
v___x_1524_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1521_, v___x_1522_, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15____boxed(lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_();
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_));
v___x_1529_ = 1;
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_);
v___x_1531_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1528_, v___x_1529_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17____boxed(lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_();
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg(lean_object* v_e_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__2));
v___x_1547_ = lean_unsigned_to_nat(3u);
v___x_1548_ = l_Lean_Expr_isAppOfArity(v_e_1540_, v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Lean_Expr_appArg_x21(v_e_1540_);
v___x_1552_ = l_Lean_Meta_getCharValue_x3f(v___x_1551_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1576_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1576_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1576_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1571_; 
v_val_1557_ = lean_ctor_get(v_a_1553_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1559_ = v_a_1553_;
v_isShared_1560_ = v_isSharedCheck_1571_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v_a_1553_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1571_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; uint32_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1561_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__3));
v___x_1562_ = lean_unbox_uint32(v_val_1557_);
lean_dec(v_val_1557_);
v___x_1563_ = lean_string_push(v___x_1561_, v___x_1562_);
v___x_1564_ = l_Lean_mkStrLit(v___x_1563_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1564_);
v___x_1566_ = v___x_1559_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1566_);
v___x_1568_ = v___x_1555_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
lean_dec(v_a_1553_);
v___x_1572_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1572_);
v___x_1574_ = v___x_1555_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1552_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1552_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Char_reduceToString___redArg(v_e_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec_ref(v_e_1585_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString(lean_object* v_e_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Char_reduceToString___redArg(v_e_1592_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object* v_e_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Char_reduceToString(v_e_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_e_1602_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_));
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_));
v___x_1636_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1637_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1634_, v___x_1635_, v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16____boxed(lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_();
return v_res_1639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_));
v___x_1644_ = 1;
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_);
v___x_1646_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1643_, v___x_1644_, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18____boxed(lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_();
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_));
v___x_1651_ = 1;
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_);
v___x_1653_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1650_, v___x_1651_, v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20____boxed(lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_();
return v_res_1655_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__4(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = l_Lean_Level_ofNat(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__5(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__4, &l_Char_reduceVal___redArg___closed__4_once, _init_l_Char_reduceVal___redArg___closed__4);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__6(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__5, &l_Char_reduceVal___redArg___closed__5_once, _init_l_Char_reduceVal___redArg___closed__5);
v___x_1670_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__3));
v___x_1671_ = l_Lean_Expr_const___override(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__9(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__8));
v___x_1677_ = l_Lean_mkConst(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__12(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__11));
v___x_1684_ = l_Lean_Expr_const___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg(lean_object* v_e_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1685_, v_a_1687_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1744_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1744_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1744_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = l_Lean_Expr_cleanupAnnotations(v_a_1692_);
v___x_1702_ = l_Lean_Expr_isApp(v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec_ref(v___x_1701_);
goto v___jp_1696_;
}
else
{
lean_object* v_arg_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_arg_1703_ = lean_ctor_get(v___x_1701_, 1);
lean_inc_ref(v_arg_1703_);
v___x_1704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1701_);
v___x_1705_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__1));
v___x_1706_ = l_Lean_Expr_isConstOf(v___x_1704_, v___x_1705_);
lean_dec_ref(v___x_1704_);
if (v___x_1706_ == 0)
{
lean_dec_ref(v_arg_1703_);
goto v___jp_1696_;
}
else
{
lean_object* v___x_1707_; 
lean_del_object(v___x_1694_);
v___x_1707_ = l_Lean_Meta_getCharValue_x3f(v_arg_1703_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1735_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1735_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1735_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
if (lean_obj_tag(v_a_1708_) == 1)
{
lean_object* v_val_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1730_; 
v_val_1712_ = lean_ctor_get(v_a_1708_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_a_1708_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1714_ = v_a_1708_;
v_isShared_1715_ = v_isSharedCheck_1730_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_val_1712_);
lean_dec(v_a_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1730_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint32_t v___x_1716_; lean_object* v___x_1717_; lean_object* v_r_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1716_ = lean_unbox_uint32(v_val_1712_);
lean_dec(v_val_1712_);
v___x_1717_ = lean_uint32_to_nat(v___x_1716_);
v_r_1718_ = l_Lean_mkRawNatLit(v___x_1717_);
v___x_1719_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__6, &l_Char_reduceVal___redArg___closed__6_once, _init_l_Char_reduceVal___redArg___closed__6);
v___x_1720_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__9, &l_Char_reduceVal___redArg___closed__9_once, _init_l_Char_reduceVal___redArg___closed__9);
v___x_1721_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__12, &l_Char_reduceVal___redArg___closed__12_once, _init_l_Char_reduceVal___redArg___closed__12);
lean_inc_ref(v_r_1718_);
v___x_1722_ = l_Lean_Expr_app___override(v___x_1721_, v_r_1718_);
v___x_1723_ = l_Lean_mkApp3(v___x_1719_, v___x_1720_, v_r_1718_, v___x_1722_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1723_);
v___x_1725_ = v___x_1714_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1725_);
v___x_1727_ = v___x_1710_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v_a_1708_);
v___x_1731_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1731_);
v___x_1733_ = v___x_1710_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1707_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1707_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1697_);
v___x_1699_ = v___x_1694_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1691_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1691_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object* v_e_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Char_reduceVal___redArg(v_e_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal(lean_object* v_e_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Char_reduceVal___redArg(v_e_1760_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object* v_e_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Char_reduceVal(v_e_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_));
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_));
v___x_1796_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1797_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1794_, v___x_1795_, v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13____boxed(lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_();
return v_res_1799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_));
v___x_1804_ = 1;
v___x_1805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_);
v___x_1806_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1803_, v___x_1804_, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15____boxed(lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_();
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_));
v___x_1811_ = 1;
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_);
v___x_1813_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1810_, v___x_1811_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17____boxed(lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_();
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg(lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = ((lean_object*)(l_Char_reduceLT___redArg___closed__2));
v___x_1828_ = lean_unsigned_to_nat(4u);
v___x_1829_ = l_Lean_Expr_isAppOfArity(v_e_1821_, v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_e_1821_);
v___x_1830_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = l_Lean_Expr_appFn_x21(v_e_1821_);
v___x_1833_ = l_Lean_Expr_appArg_x21(v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = l_Lean_Meta_getCharValue_x3f(v___x_1833_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1868_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1868_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1868_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
if (lean_obj_tag(v_a_1835_) == 1)
{
lean_object* v_val_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1837_);
v_val_1839_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_val_1839_);
lean_dec_ref(v_a_1835_);
v___x_1840_ = l_Lean_Expr_appArg_x21(v_e_1821_);
v___x_1841_ = l_Lean_Meta_getCharValue_x3f(v___x_1840_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1855_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
if (lean_obj_tag(v_a_1842_) == 1)
{
lean_object* v_val_1846_; uint32_t v___x_1847_; uint32_t v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1844_);
v_val_1846_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_val_1846_);
lean_dec_ref(v_a_1842_);
v___x_1847_ = lean_unbox_uint32(v_val_1839_);
lean_dec(v_val_1839_);
v___x_1848_ = lean_unbox_uint32(v_val_1846_);
lean_dec(v_val_1846_);
v___x_1849_ = lean_uint32_dec_lt(v___x_1847_, v___x_1848_);
v___x_1850_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1821_, v___x_1849_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_a_1842_);
lean_dec(v_val_1839_);
lean_dec_ref(v_e_1821_);
v___x_1851_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1851_);
v___x_1853_ = v___x_1844_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_val_1839_);
lean_dec_ref(v_e_1821_);
v_a_1856_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1841_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1841_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_a_1835_);
lean_dec_ref(v_e_1821_);
v___x_1864_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1864_);
v___x_1866_ = v___x_1837_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_e_1821_);
v_a_1869_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1834_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1834_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg___boxed(lean_object* v_e_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Char_reduceLT___redArg(v_e_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT(lean_object* v_e_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Char_reduceLT___redArg(v_e_1884_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object* v_e_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Char_reduceLT(v_e_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_));
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_));
v___x_1924_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1925_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1922_, v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20____boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_();
return v_res_1927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_));
v___x_1932_ = 1;
v___x_1933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_);
v___x_1934_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1931_, v___x_1932_, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22____boxed(lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_();
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_));
v___x_1939_ = 1;
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_);
v___x_1941_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1938_, v___x_1939_, v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24____boxed(lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_();
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg(lean_object* v_e_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = ((lean_object*)(l_Char_reduceLE___redArg___closed__2));
v___x_1956_ = lean_unsigned_to_nat(4u);
v___x_1957_ = l_Lean_Expr_isAppOfArity(v_e_1949_, v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_e_1949_);
v___x_1958_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = l_Lean_Expr_appFn_x21(v_e_1949_);
v___x_1961_ = l_Lean_Expr_appArg_x21(v___x_1960_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = l_Lean_Meta_getCharValue_x3f(v___x_1961_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1996_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1996_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1996_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
if (lean_obj_tag(v_a_1963_) == 1)
{
lean_object* v_val_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1965_);
v_val_1967_ = lean_ctor_get(v_a_1963_, 0);
lean_inc(v_val_1967_);
lean_dec_ref(v_a_1963_);
v___x_1968_ = l_Lean_Expr_appArg_x21(v_e_1949_);
v___x_1969_ = l_Lean_Meta_getCharValue_x3f(v___x_1968_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_object* v_val_1974_; uint32_t v___x_1975_; uint32_t v___x_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; 
lean_del_object(v___x_1972_);
v_val_1974_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_1974_);
lean_dec_ref(v_a_1970_);
v___x_1975_ = lean_unbox_uint32(v_val_1967_);
lean_dec(v_val_1967_);
v___x_1976_ = lean_unbox_uint32(v_val_1974_);
lean_dec(v_val_1974_);
v___x_1977_ = lean_uint32_dec_le(v___x_1975_, v___x_1976_);
v___x_1978_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1949_, v___x_1977_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
lean_dec(v_a_1970_);
lean_dec(v_val_1967_);
lean_dec_ref(v_e_1949_);
v___x_1979_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1979_);
v___x_1981_ = v___x_1972_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_val_1967_);
lean_dec_ref(v_e_1949_);
v_a_1984_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1969_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1969_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
lean_dec(v_a_1963_);
lean_dec_ref(v_e_1949_);
v___x_1992_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1992_);
v___x_1994_ = v___x_1965_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_e_1949_);
v_a_1997_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1962_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1962_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg___boxed(lean_object* v_e_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Char_reduceLE___redArg(v_e_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE(lean_object* v_e_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Char_reduceLE___redArg(v_e_2012_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object* v_e_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Char_reduceLE(v_e_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_));
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_));
v___x_2052_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2053_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2050_, v___x_2051_, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20____boxed(lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_();
return v_res_2055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_));
v___x_2060_ = 1;
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_);
v___x_2062_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2059_, v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22____boxed(lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_();
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_));
v___x_2067_ = 1;
v___x_2068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_);
v___x_2069_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2066_, v___x_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24____boxed(lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_();
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg(lean_object* v_e_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = ((lean_object*)(l_Char_reduceGT___redArg___closed__2));
v___x_2084_ = lean_unsigned_to_nat(4u);
v___x_2085_ = l_Lean_Expr_isAppOfArity(v_e_2077_, v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v_e_2077_);
v___x_2086_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = l_Lean_Expr_appFn_x21(v_e_2077_);
v___x_2089_ = l_Lean_Expr_appArg_x21(v___x_2088_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l_Lean_Meta_getCharValue_x3f(v___x_2089_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2124_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2124_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2124_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
if (lean_obj_tag(v_a_2091_) == 1)
{
lean_object* v_val_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_del_object(v___x_2093_);
v_val_2095_ = lean_ctor_get(v_a_2091_, 0);
lean_inc(v_val_2095_);
lean_dec_ref(v_a_2091_);
v___x_2096_ = l_Lean_Expr_appArg_x21(v_e_2077_);
v___x_2097_ = l_Lean_Meta_getCharValue_x3f(v___x_2096_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2111_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
if (lean_obj_tag(v_a_2098_) == 1)
{
lean_object* v_val_2102_; uint32_t v___x_2103_; uint32_t v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; 
lean_del_object(v___x_2100_);
v_val_2102_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_val_2102_);
lean_dec_ref(v_a_2098_);
v___x_2103_ = lean_unbox_uint32(v_val_2102_);
lean_dec(v_val_2102_);
v___x_2104_ = lean_unbox_uint32(v_val_2095_);
lean_dec(v_val_2095_);
v___x_2105_ = lean_uint32_dec_lt(v___x_2103_, v___x_2104_);
v___x_2106_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2077_, v___x_2105_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_a_2098_);
lean_dec(v_val_2095_);
lean_dec_ref(v_e_2077_);
v___x_2107_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2107_);
v___x_2109_ = v___x_2100_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_val_2095_);
lean_dec_ref(v_e_2077_);
v_a_2112_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2097_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2097_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v_a_2091_);
lean_dec_ref(v_e_2077_);
v___x_2120_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2120_);
v___x_2122_ = v___x_2093_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_e_2077_);
v_a_2125_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2090_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2090_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg___boxed(lean_object* v_e_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Char_reduceGT___redArg(v_e_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT(lean_object* v_e_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Char_reduceGT___redArg(v_e_2140_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object* v_e_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Char_reduceGT(v_e_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_));
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_));
v___x_2167_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2168_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2165_, v___x_2166_, v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20____boxed(lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_();
return v_res_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_));
v___x_2175_ = 1;
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_);
v___x_2177_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2174_, v___x_2175_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22____boxed(lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_();
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_));
v___x_2182_ = 1;
v___x_2183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_);
v___x_2184_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2181_, v___x_2182_, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24____boxed(lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_();
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg(lean_object* v_e_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = ((lean_object*)(l_Char_reduceGE___redArg___closed__2));
v___x_2199_ = lean_unsigned_to_nat(4u);
v___x_2200_ = l_Lean_Expr_isAppOfArity(v_e_2192_, v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_e_2192_);
v___x_2201_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = l_Lean_Expr_appFn_x21(v_e_2192_);
v___x_2204_ = l_Lean_Expr_appArg_x21(v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_Meta_getCharValue_x3f(v___x_2204_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2239_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2239_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2239_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
if (lean_obj_tag(v_a_2206_) == 1)
{
lean_object* v_val_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_del_object(v___x_2208_);
v_val_2210_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_val_2210_);
lean_dec_ref(v_a_2206_);
v___x_2211_ = l_Lean_Expr_appArg_x21(v_e_2192_);
v___x_2212_ = l_Lean_Meta_getCharValue_x3f(v___x_2211_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2226_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2226_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2226_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
if (lean_obj_tag(v_a_2213_) == 1)
{
lean_object* v_val_2217_; uint32_t v___x_2218_; uint32_t v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
lean_del_object(v___x_2215_);
v_val_2217_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_val_2217_);
lean_dec_ref(v_a_2213_);
v___x_2218_ = lean_unbox_uint32(v_val_2217_);
lean_dec(v_val_2217_);
v___x_2219_ = lean_unbox_uint32(v_val_2210_);
lean_dec(v_val_2210_);
v___x_2220_ = lean_uint32_dec_le(v___x_2218_, v___x_2219_);
v___x_2221_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2192_, v___x_2220_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec(v_a_2213_);
lean_dec(v_val_2210_);
lean_dec_ref(v_e_2192_);
v___x_2222_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2222_);
v___x_2224_ = v___x_2215_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_val_2210_);
lean_dec_ref(v_e_2192_);
v_a_2227_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2212_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2212_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec(v_a_2206_);
lean_dec_ref(v_e_2192_);
v___x_2235_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2235_);
v___x_2237_ = v___x_2208_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec_ref(v_e_2192_);
v_a_2240_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2205_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2205_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg___boxed(lean_object* v_e_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Char_reduceGE___redArg(v_e_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE(lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Char_reduceGE___redArg(v_e_2255_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object* v_e_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Char_reduceGE(v_e_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_));
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_));
v___x_2282_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2283_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2280_, v___x_2281_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20____boxed(lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_();
return v_res_2285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_));
v___x_2290_ = 1;
v___x_2291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_);
v___x_2292_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2289_, v___x_2290_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22____boxed(lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_();
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_));
v___x_2297_ = 1;
v___x_2298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_);
v___x_2299_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2296_, v___x_2297_, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24____boxed(lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_();
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_2312_ = lean_unsigned_to_nat(3u);
v___x_2313_ = l_Lean_Expr_isAppOfArity(v_e_2305_, v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v_e_2305_);
v___x_2314_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = l_Lean_Expr_appFn_x21(v_e_2305_);
v___x_2317_ = l_Lean_Expr_appArg_x21(v___x_2316_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = l_Lean_Meta_getCharValue_x3f(v___x_2317_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2352_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2352_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2352_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
if (lean_obj_tag(v_a_2319_) == 1)
{
lean_object* v_val_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2321_);
v_val_2323_ = lean_ctor_get(v_a_2319_, 0);
lean_inc(v_val_2323_);
lean_dec_ref(v_a_2319_);
v___x_2324_ = l_Lean_Expr_appArg_x21(v_e_2305_);
v___x_2325_ = l_Lean_Meta_getCharValue_x3f(v___x_2324_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2339_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2339_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2339_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
if (lean_obj_tag(v_a_2326_) == 1)
{
lean_object* v_val_2330_; uint32_t v___x_2331_; uint32_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
lean_del_object(v___x_2328_);
v_val_2330_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_val_2330_);
lean_dec_ref(v_a_2326_);
v___x_2331_ = lean_unbox_uint32(v_val_2323_);
lean_dec(v_val_2323_);
v___x_2332_ = lean_unbox_uint32(v_val_2330_);
lean_dec(v_val_2330_);
v___x_2333_ = lean_uint32_dec_eq(v___x_2331_, v___x_2332_);
v___x_2334_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2305_, v___x_2333_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec(v_a_2326_);
lean_dec(v_val_2323_);
lean_dec_ref(v_e_2305_);
v___x_2335_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2335_);
v___x_2337_ = v___x_2328_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_val_2323_);
lean_dec_ref(v_e_2305_);
v_a_2340_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2325_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2325_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v_a_2319_);
lean_dec_ref(v_e_2305_);
v___x_2348_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2348_);
v___x_2350_ = v___x_2321_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_e_2305_);
v_a_2353_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2318_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2318_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg___boxed(lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Char_reduceEq___redArg(v_e_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object* v_e_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Char_reduceEq___redArg(v_e_2368_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object* v_e_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Char_reduceEq(v_e_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_));
v___x_2406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_));
v___x_2407_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2408_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2405_, v___x_2406_, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20____boxed(lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_();
return v_res_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_));
v___x_2415_ = 1;
v___x_2416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_);
v___x_2417_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2414_, v___x_2415_, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22____boxed(lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_();
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_));
v___x_2422_ = 1;
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_);
v___x_2424_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2421_, v___x_2422_, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24____boxed(lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_();
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object* v_e_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2436_ = ((lean_object*)(l_Char_reduceNe___redArg___closed__1));
v___x_2437_ = lean_unsigned_to_nat(3u);
v___x_2438_ = l_Lean_Expr_isAppOfArity(v_e_2430_, v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_e_2430_);
v___x_2439_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = l_Lean_Expr_appFn_x21(v_e_2430_);
v___x_2442_ = l_Lean_Expr_appArg_x21(v___x_2441_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = l_Lean_Meta_getCharValue_x3f(v___x_2442_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2479_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2479_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2479_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
if (lean_obj_tag(v_a_2444_) == 1)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_del_object(v___x_2446_);
v_val_2448_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_val_2448_);
lean_dec_ref(v_a_2444_);
v___x_2449_ = l_Lean_Expr_appArg_x21(v_e_2430_);
v___x_2450_ = l_Lean_Meta_getCharValue_x3f(v___x_2449_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2466_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2466_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2466_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
if (lean_obj_tag(v_a_2451_) == 1)
{
lean_object* v_val_2455_; uint32_t v___x_2456_; uint32_t v___x_2457_; uint8_t v___x_2458_; 
lean_del_object(v___x_2453_);
v_val_2455_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_val_2455_);
lean_dec_ref(v_a_2451_);
v___x_2456_ = lean_unbox_uint32(v_val_2448_);
lean_dec(v_val_2448_);
v___x_2457_ = lean_unbox_uint32(v_val_2455_);
lean_dec(v_val_2455_);
v___x_2458_ = lean_uint32_dec_eq(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2430_, v___x_2438_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2459_;
}
else
{
uint8_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = 0;
v___x_2461_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2430_, v___x_2460_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2461_;
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec(v_a_2451_);
lean_dec(v_val_2448_);
lean_dec_ref(v_e_2430_);
v___x_2462_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2462_);
v___x_2464_ = v___x_2453_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_val_2448_);
lean_dec_ref(v_e_2430_);
v_a_2467_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2450_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2450_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_dec(v_a_2444_);
lean_dec_ref(v_e_2430_);
v___x_2475_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2475_);
v___x_2477_ = v___x_2446_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v_e_2430_);
v_a_2480_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2443_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2443_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg___boxed(lean_object* v_e_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Char_reduceNe___redArg(v_e_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object* v_e_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Char_reduceNe___redArg(v_e_2495_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object* v_e_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Char_reduceNe(v_e_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_));
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_));
v___x_2539_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2540_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2537_, v___x_2538_, v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20____boxed(lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_();
return v_res_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_));
v___x_2547_ = 1;
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_);
v___x_2549_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2546_, v___x_2547_, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22____boxed(lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_();
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_));
v___x_2554_ = 1;
v___x_2555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_);
v___x_2556_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2553_, v___x_2554_, v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24____boxed(lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_();
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg(lean_object* v_e_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = ((lean_object*)(l_Char_reduceBEq___redArg___closed__2));
v___x_2571_ = lean_unsigned_to_nat(4u);
v___x_2572_ = l_Lean_Expr_isAppOfArity(v_e_2564_, v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = l_Lean_Expr_appFn_x21(v_e_2564_);
v___x_2576_ = l_Lean_Expr_appArg_x21(v___x_2575_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = l_Lean_Meta_getCharValue_x3f(v___x_2576_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2624_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2624_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2624_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
if (lean_obj_tag(v_a_2578_) == 1)
{
lean_object* v_val_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2619_; 
v_val_2582_ = lean_ctor_get(v_a_2578_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2584_ = v_a_2578_;
v_isShared_2585_ = v_isSharedCheck_2619_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_val_2582_);
lean_dec(v_a_2578_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2619_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Lean_Expr_appArg_x21(v_e_2564_);
v___x_2587_ = l_Lean_Meta_getCharValue_x3f(v___x_2586_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2610_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2610_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2610_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___y_2593_; 
if (lean_obj_tag(v_a_2588_) == 1)
{
lean_object* v_val_2600_; uint32_t v___x_2601_; uint32_t v___x_2602_; uint8_t v___x_2603_; 
lean_del_object(v___x_2580_);
v_val_2600_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v_a_2588_);
v___x_2601_ = lean_unbox_uint32(v_val_2582_);
lean_dec(v_val_2582_);
v___x_2602_ = lean_unbox_uint32(v_val_2600_);
lean_dec(v_val_2600_);
v___x_2603_ = lean_uint32_dec_eq(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_2593_ = v___x_2604_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_2593_ = v___x_2605_;
goto v___jp_2592_;
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_del_object(v___x_2584_);
lean_dec(v_val_2582_);
v___x_2606_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2606_);
v___x_2608_ = v___x_2580_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
v___jp_2592_:
{
lean_object* v___x_2595_; 
lean_inc_ref(v___y_2593_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
lean_ctor_set(v___x_2584_, 0, v___y_2593_);
v___x_2595_ = v___x_2584_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___y_2593_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2595_);
v___x_2597_ = v___x_2590_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2584_);
lean_dec(v_val_2582_);
lean_del_object(v___x_2580_);
v_a_2611_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2587_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2587_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec(v_a_2578_);
v___x_2620_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2620_);
v___x_2622_ = v___x_2580_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2577_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2577_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object* v_e_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Char_reduceBEq___redArg(v_e_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec_ref(v_e_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq(lean_object* v_e_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Char_reduceBEq___redArg(v_e_2640_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object* v_e_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Char_reduceBEq(v_e_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_e_2650_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_));
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_));
v___x_2680_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2681_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2678_, v___x_2679_, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20____boxed(lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_();
return v_res_2683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_));
v___x_2688_ = 1;
v___x_2689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_);
v___x_2690_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2687_, v___x_2688_, v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22____boxed(lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_();
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_));
v___x_2695_ = 1;
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_);
v___x_2697_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2694_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24____boxed(lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_();
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object* v_e_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = ((lean_object*)(l_Char_reduceBNe___redArg___closed__1));
v___x_2710_ = lean_unsigned_to_nat(4u);
v___x_2711_ = l_Lean_Expr_isAppOfArity(v_e_2703_, v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
return v___x_2713_;
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = l_Lean_Expr_appFn_x21(v_e_2703_);
v___x_2715_ = l_Lean_Expr_appArg_x21(v___x_2714_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = l_Lean_Meta_getCharValue_x3f(v___x_2715_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2764_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2764_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2764_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
if (lean_obj_tag(v_a_2717_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2759_; 
v_val_2721_ = lean_ctor_get(v_a_2717_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_a_2717_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2723_ = v_a_2717_;
v_isShared_2724_ = v_isSharedCheck_2759_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v_a_2717_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2759_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = l_Lean_Expr_appArg_x21(v_e_2703_);
v___x_2726_ = l_Lean_Meta_getCharValue_x3f(v___x_2725_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2750_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2750_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2750_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___y_2732_; 
if (lean_obj_tag(v_a_2727_) == 1)
{
lean_object* v_val_2741_; uint32_t v___x_2742_; uint32_t v___x_2743_; uint8_t v___x_2744_; 
lean_del_object(v___x_2719_);
v_val_2741_ = lean_ctor_get(v_a_2727_, 0);
lean_inc(v_val_2741_);
lean_dec_ref(v_a_2727_);
v___x_2742_ = lean_unbox_uint32(v_val_2721_);
lean_dec(v_val_2721_);
v___x_2743_ = lean_unbox_uint32(v_val_2741_);
lean_dec(v_val_2741_);
v___x_2744_ = lean_uint32_dec_eq(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
if (v___x_2711_ == 0)
{
goto v___jp_2739_;
}
else
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__6, &l_Char_reduceBoolPred___redArg___closed__6_once, _init_l_Char_reduceBoolPred___redArg___closed__6);
v___y_2732_ = v___x_2745_;
goto v___jp_2731_;
}
}
else
{
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_del_object(v___x_2729_);
lean_dec(v_a_2727_);
lean_del_object(v___x_2723_);
lean_dec(v_val_2721_);
v___x_2746_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2746_);
v___x_2748_ = v___x_2719_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
v___jp_2731_:
{
lean_object* v___x_2734_; 
lean_inc_ref(v___y_2732_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 0);
lean_ctor_set(v___x_2723_, 0, v___y_2732_);
v___x_2734_ = v___x_2723_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___y_2732_);
v___x_2734_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2734_);
v___x_2736_ = v___x_2729_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
v___jp_2739_:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_obj_once(&l_Char_reduceBoolPred___redArg___closed__3, &l_Char_reduceBoolPred___redArg___closed__3_once, _init_l_Char_reduceBoolPred___redArg___closed__3);
v___y_2732_ = v___x_2740_;
goto v___jp_2731_;
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_del_object(v___x_2723_);
lean_dec(v_val_2721_);
lean_del_object(v___x_2719_);
v_a_2751_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2726_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2726_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
lean_dec(v_a_2717_);
v___x_2760_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2760_);
v___x_2762_ = v___x_2719_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2716_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2716_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object* v_e_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Char_reduceBNe___redArg(v_e_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_e_2773_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object* v_e_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Char_reduceBNe___redArg(v_e_2780_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object* v_e_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Char_reduceBNe(v_e_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_e_2790_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_));
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_));
v___x_2820_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2821_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2818_, v___x_2819_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20____boxed(lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_();
return v_res_2823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_));
v___x_2828_ = 1;
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_);
v___x_2830_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2827_, v___x_2828_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22____boxed(lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_();
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_));
v___x_2835_ = 1;
v___x_2836_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_);
v___x_2837_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2834_, v___x_2835_, v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24____boxed(lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_();
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object* v_e_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
lean_inc_ref(v_e_2840_);
v___x_2846_ = l_Lean_Meta_getCharValue_x3f(v_e_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2866_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2866_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2866_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
if (lean_obj_tag(v_a_2847_) == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_dec_ref(v_e_2840_);
v___x_2851_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2864_; 
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v_a_2847_, 0);
lean_dec(v_unused_2865_);
v___x_2856_ = v_a_2847_;
v_isShared_2857_ = v_isSharedCheck_2864_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v_a_2847_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2864_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 0);
lean_ctor_set(v___x_2856_, 0, v_e_2840_);
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_e_2840_);
v___x_2859_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2859_);
v___x_2861_ = v___x_2849_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec_ref(v_e_2840_);
v_a_2867_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2846_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2846_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object* v_e_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Char_isValue___redArg(v_e_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue(lean_object* v_e_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Char_isValue___redArg(v_e_2882_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object* v_e_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Char_isValue(v_e_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_));
v___x_2917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_));
v___x_2918_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_2919_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2916_, v___x_2917_, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13____boxed(lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_();
return v_res_2921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_));
v___x_2926_ = 0;
v___x_2927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_);
v___x_2928_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2925_, v___x_2926_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15____boxed(lean_object* v_a_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_();
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_));
v___x_2933_ = 0;
v___x_2934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_);
v___x_2935_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2932_, v___x_2933_, v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17____boxed(lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_();
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2942_, v_a_2944_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3000_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_3000_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3000_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = l_Lean_Expr_cleanupAnnotations(v_a_2949_);
v___x_2959_ = l_Lean_Expr_isApp(v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec_ref(v___x_2958_);
goto v___jp_2953_;
}
else
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2958_);
v___x_2961_ = l_Lean_Expr_isApp(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec_ref(v___x_2960_);
goto v___jp_2953_;
}
else
{
lean_object* v_arg_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_arg_2962_ = lean_ctor_get(v___x_2960_, 1);
lean_inc_ref(v_arg_2962_);
v___x_2963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2960_);
v___x_2964_ = ((lean_object*)(l_Char_reduceOfNatAux___redArg___closed__1));
v___x_2965_ = l_Lean_Expr_isConstOf(v___x_2963_, v___x_2964_);
lean_dec_ref(v___x_2963_);
if (v___x_2965_ == 0)
{
lean_dec_ref(v_arg_2962_);
goto v___jp_2953_;
}
else
{
lean_object* v___x_2966_; 
lean_del_object(v___x_2951_);
v___x_2966_ = l_Lean_Meta_getNatValue_x3f(v_arg_2962_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec_ref(v_arg_2962_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2991_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2991_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2991_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
if (lean_obj_tag(v_a_2967_) == 1)
{
lean_object* v_val_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2986_; 
v_val_2971_ = lean_ctor_get(v_a_2967_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2973_ = v_a_2967_;
v_isShared_2974_ = v_isSharedCheck_2986_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_val_2971_);
lean_dec(v_a_2967_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2986_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
uint32_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2975_ = l_Char_ofNat(v_val_2971_);
lean_dec(v_val_2971_);
v___x_2976_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_2977_ = lean_uint32_to_nat(v___x_2975_);
v___x_2978_ = l_Lean_mkRawNatLit(v___x_2977_);
v___x_2979_ = l_Lean_Expr_app___override(v___x_2976_, v___x_2978_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2979_);
v___x_2981_ = v___x_2973_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2981_);
v___x_2983_ = v___x_2969_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec(v_a_2967_);
v___x_2987_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2987_);
v___x_2989_ = v___x_2969_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
v_a_2992_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2966_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2966_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2954_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2954_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_a_3001_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2948_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2948_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object* v_e_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Char_reduceOfNatAux___redArg(v_e_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Char_reduceOfNatAux___redArg(v_e_3016_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Char_reduceOfNatAux(v_e_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_));
v___x_3052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_));
v___x_3053_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3054_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3051_, v___x_3052_, v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14____boxed(lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_();
return v_res_3056_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_));
v___x_3061_ = 1;
v___x_3062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_);
v___x_3063_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3060_, v___x_3061_, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16____boxed(lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_();
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_));
v___x_3068_ = 1;
v___x_3069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_);
v___x_3070_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3067_, v___x_3068_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18____boxed(lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_();
return v_res_3072_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__3(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_unsigned_to_nat(65u);
v___x_3079_ = l_Lean_mkRawNatLit(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__4(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__3, &l_Char_reduceDefault___redArg___closed__3_once, _init_l_Char_reduceDefault___redArg___closed__3);
v___x_3081_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_3082_ = l_Lean_Expr_app___override(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__5(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__4, &l_Char_reduceDefault___redArg___closed__4_once, _init_l_Char_reduceDefault___redArg___closed__4);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg(lean_object* v_e_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3107_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3107_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3107_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = l_Lean_Expr_cleanupAnnotations(v_a_3089_);
v___x_3099_ = l_Lean_Expr_isApp(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v___x_3098_);
goto v___jp_3093_;
}
else
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3098_);
v___x_3101_ = l_Lean_Expr_isApp(v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec_ref(v___x_3100_);
goto v___jp_3093_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3100_);
v___x_3103_ = ((lean_object*)(l_Char_reduceDefault___redArg___closed__2));
v___x_3104_ = l_Lean_Expr_isConstOf(v___x_3102_, v___x_3103_);
lean_dec_ref(v___x_3102_);
if (v___x_3104_ == 0)
{
goto v___jp_3093_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_del_object(v___x_3091_);
v___x_3105_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__5, &l_Char_reduceDefault___redArg___closed__5_once, _init_l_Char_reduceDefault___redArg___closed__5);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
}
v___jp_3093_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = ((lean_object*)(l_Char_reduceUnary___redArg___closed__0));
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3094_);
v___x_3096_ = v___x_3091_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
v_a_3108_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3088_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3088_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Char_reduceDefault___redArg(v_e_3116_, v_a_3117_);
lean_dec(v_a_3117_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault(lean_object* v_e_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Char_reduceDefault___redArg(v_e_3120_, v_a_3125_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object* v_e_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Char_reduceDefault(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_));
v___x_3157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_));
v___x_3158_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3159_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3156_, v___x_3157_, v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15____boxed(lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_();
return v_res_3161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_));
v___x_3166_ = 1;
v___x_3167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_);
v___x_3168_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3165_, v___x_3166_, v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17____boxed(lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_();
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_));
v___x_3173_ = 1;
v___x_3174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_);
v___x_3175_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3172_, v___x_3173_, v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19____boxed(lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_();
return v_res_3177_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(uint32_t v_a_3178_, lean_object* v_as_3179_, size_t v_i_3180_, size_t v_stop_3181_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; uint32_t v___x_3184_; uint8_t v___x_3185_; 
v___x_3183_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
v___x_3184_ = lean_unbox_uint32(v___x_3183_);
v___x_3185_ = lean_uint32_dec_eq(v_a_3178_, v___x_3184_);
if (v___x_3185_ == 0)
{
size_t v___x_3186_; size_t v___x_3187_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3180_, v___x_3186_);
v_i_3180_ = v___x_3187_;
goto _start;
}
else
{
return v___x_3185_;
}
}
else
{
uint8_t v___x_3189_; 
v___x_3189_ = 0;
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0___boxed(lean_object* v_a_3190_, lean_object* v_as_3191_, lean_object* v_i_3192_, lean_object* v_stop_3193_){
_start:
{
uint32_t v_a_boxed_3194_; size_t v_i_boxed_3195_; size_t v_stop_boxed_3196_; uint8_t v_res_3197_; lean_object* v_r_3198_; 
v_a_boxed_3194_ = lean_unbox_uint32(v_a_3190_);
lean_dec(v_a_3190_);
v_i_boxed_3195_ = lean_unbox_usize(v_i_3192_);
lean_dec(v_i_3192_);
v_stop_boxed_3196_ = lean_unbox_usize(v_stop_3193_);
lean_dec(v_stop_3193_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_boxed_3194_, v_as_3191_, v_i_boxed_3195_, v_stop_boxed_3196_);
lean_dec_ref(v_as_3191_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(lean_object* v_as_3199_, uint32_t v_a_3200_){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_array_get_size(v_as_3199_);
v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
if (v___x_3203_ == 0)
{
return v___x_3203_;
}
else
{
if (v___x_3203_ == 0)
{
return v___x_3203_;
}
else
{
size_t v___x_3204_; size_t v___x_3205_; uint8_t v___x_3206_; 
v___x_3204_ = ((size_t)0ULL);
v___x_3205_ = lean_usize_of_nat(v___x_3202_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_3200_, v_as_3199_, v___x_3204_, v___x_3205_);
return v___x_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0___boxed(lean_object* v_as_3207_, lean_object* v_a_3208_){
_start:
{
uint32_t v_a_boxed_3209_; uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_a_boxed_3209_ = lean_unbox_uint32(v_a_3208_);
lean_dec(v_a_3208_);
v_res_3210_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v_as_3207_, v_a_boxed_3209_);
lean_dec_ref(v_as_3207_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = 42;
v___x_3218_ = lean_box_uint32(v___x_3217_);
return v___x_3218_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2(void){
_start:
{
uint32_t v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = 102;
v___x_3220_ = lean_box_uint32(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3(void){
_start:
{
uint32_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = 101;
v___x_3222_ = lean_box_uint32(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4(void){
_start:
{
uint32_t v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = 100;
v___x_3224_ = lean_box_uint32(v___x_3223_);
return v___x_3224_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5(void){
_start:
{
uint32_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = 99;
v___x_3226_ = lean_box_uint32(v___x_3225_);
return v___x_3226_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6(void){
_start:
{
uint32_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = 98;
v___x_3228_ = lean_box_uint32(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7(void){
_start:
{
uint32_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = 97;
v___x_3230_ = lean_box_uint32(v___x_3229_);
return v___x_3230_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8(void){
_start:
{
uint32_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = 57;
v___x_3232_ = lean_box_uint32(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9(void){
_start:
{
uint32_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = 56;
v___x_3234_ = lean_box_uint32(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10(void){
_start:
{
uint32_t v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = 55;
v___x_3236_ = lean_box_uint32(v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11(void){
_start:
{
uint32_t v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = 54;
v___x_3238_ = lean_box_uint32(v___x_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12(void){
_start:
{
uint32_t v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = 53;
v___x_3240_ = lean_box_uint32(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13(void){
_start:
{
uint32_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = 52;
v___x_3242_ = lean_box_uint32(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14(void){
_start:
{
uint32_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = 51;
v___x_3244_ = lean_box_uint32(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15(void){
_start:
{
uint32_t v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = 50;
v___x_3246_ = lean_box_uint32(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16(void){
_start:
{
uint32_t v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = 49;
v___x_3248_ = lean_box_uint32(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17(void){
_start:
{
uint32_t v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = 48;
v___x_3250_ = lean_box_uint32(v___x_3249_);
return v___x_3250_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3251_ = lean_unsigned_to_nat(17u);
v___x_3252_ = lean_mk_empty_array_with_capacity(v___x_3251_);
v___x_3253_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17;
v___x_3254_ = lean_array_push(v___x_3252_, v___x_3253_);
v___x_3255_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16;
v___x_3256_ = lean_array_push(v___x_3254_, v___x_3255_);
v___x_3257_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15;
v___x_3258_ = lean_array_push(v___x_3256_, v___x_3257_);
v___x_3259_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14;
v___x_3260_ = lean_array_push(v___x_3258_, v___x_3259_);
v___x_3261_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13;
v___x_3262_ = lean_array_push(v___x_3260_, v___x_3261_);
v___x_3263_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12;
v___x_3264_ = lean_array_push(v___x_3262_, v___x_3263_);
v___x_3265_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11;
v___x_3266_ = lean_array_push(v___x_3264_, v___x_3265_);
v___x_3267_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10;
v___x_3268_ = lean_array_push(v___x_3266_, v___x_3267_);
v___x_3269_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9;
v___x_3270_ = lean_array_push(v___x_3268_, v___x_3269_);
v___x_3271_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8;
v___x_3272_ = lean_array_push(v___x_3270_, v___x_3271_);
v___x_3273_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7;
v___x_3274_ = lean_array_push(v___x_3272_, v___x_3273_);
v___x_3275_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6;
v___x_3276_ = lean_array_push(v___x_3274_, v___x_3275_);
v___x_3277_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5;
v___x_3278_ = lean_array_push(v___x_3276_, v___x_3277_);
v___x_3279_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4;
v___x_3280_ = lean_array_push(v___x_3278_, v___x_3279_);
v___x_3281_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3;
v___x_3282_ = lean_array_push(v___x_3280_, v___x_3281_);
v___x_3283_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2;
v___x_3284_ = lean_array_push(v___x_3282_, v___x_3283_);
v___x_3285_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1;
v___x_3286_ = lean_array_push(v___x_3284_, v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_box(0);
v___x_3292_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__5));
v___x_3293_ = l_Lean_mkConst(v___x_3292_, v___x_3291_);
return v___x_3293_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
v___x_3298_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__8));
v___x_3299_ = l_Lean_mkConst(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_box(0);
v___x_3304_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__11));
v___x_3305_ = l_Lean_mkConst(v___x_3304_, v___x_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg(lean_object* v_e_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3312_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3313_ = lean_unsigned_to_nat(3u);
v___x_3314_ = l_Lean_Expr_isAppOfArity(v_e_3306_, v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v_e_3306_);
v___x_3315_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v_lhs_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3317_ = l_Lean_Expr_appFn_x21(v_e_3306_);
v_lhs_3318_ = l_Lean_Expr_appArg_x21(v___x_3317_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = l_Lean_Expr_isAppOfArity(v_lhs_3318_, v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec_ref(v_lhs_3318_);
lean_dec_ref(v_e_3306_);
v___x_3322_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v_rhs_3324_; lean_object* v___x_3325_; 
v_rhs_3324_ = l_Lean_Expr_appArg_x21(v_e_3306_);
lean_inc_ref(v_rhs_3324_);
v___x_3325_ = l_Lean_Meta_getCharValue_x3f(v_rhs_3324_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3361_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3361_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3361_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
if (lean_obj_tag(v_a_3326_) == 1)
{
lean_object* v_val_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3356_; 
v_val_3330_ = lean_ctor_get(v_a_3326_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_a_3326_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3332_ = v_a_3326_;
v_isShared_3333_ = v_isSharedCheck_3356_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_val_3330_);
lean_dec(v_a_3326_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3356_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; uint32_t v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3335_ = lean_unbox_uint32(v_val_3330_);
lean_dec(v_val_3330_);
v___x_3336_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3337_ = l_Lean_Expr_appArg_x21(v_lhs_3318_);
lean_dec_ref(v_lhs_3318_);
v___x_3338_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3339_ = l_Lean_eagerReflBoolTrue;
v___x_3340_ = l_Lean_mkApp3(v___x_3338_, v___x_3337_, v_rhs_3324_, v___x_3339_);
v___x_3341_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3342_ = l_Lean_mkAppB(v___x_3341_, v_e_3306_, v___x_3340_);
v___x_3343_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3342_);
v___x_3345_ = v___x_3332_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3342_);
v___x_3345_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3346_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*2, v___x_3321_);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3347_);
v___x_3349_ = v___x_3328_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
lean_del_object(v___x_3332_);
lean_dec_ref(v_rhs_3324_);
lean_dec_ref(v_lhs_3318_);
lean_dec_ref(v_e_3306_);
v___x_3352_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3352_);
v___x_3354_ = v___x_3328_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_dec(v_a_3326_);
lean_dec_ref(v_rhs_3324_);
lean_dec_ref(v_lhs_3318_);
lean_dec_ref(v_e_3306_);
v___x_3357_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3357_);
v___x_3359_ = v___x_3328_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v_rhs_3324_);
lean_dec_ref(v_lhs_3318_);
lean_dec_ref(v_e_3306_);
v_a_3362_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3325_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3325_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___boxed(lean_object* v_e_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq(lean_object* v_e_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3377_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___boxed(lean_object* v_e_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Char_Nat_reduceDigitCharEq(v_e_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_));
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_));
v___x_3419_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3420_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3417_, v___x_3418_, v___x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23____boxed(lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_();
return v_res_3422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_));
v___x_3427_ = 1;
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_);
v___x_3429_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3426_, v___x_3427_, v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25____boxed(lean_object* v_a_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_();
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_));
v___x_3434_ = 1;
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_);
v___x_3436_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3433_, v___x_3434_, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27____boxed(lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_();
return v_res_3438_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_box(0);
v___x_3444_ = l_Lean_Level_succ___override(v___x_3443_);
return v___x_3444_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__2, &l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2);
v___x_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_3445_);
return v___x_3447_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__3, &l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3);
v___x_3449_ = ((lean_object*)(l_Char_Nat_reduceEqDigitChar___redArg___closed__1));
v___x_3450_ = l_Lean_mkConst(v___x_3449_, v___x_3448_);
return v___x_3450_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_));
v___x_3453_ = l_Lean_mkConst(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg(lean_object* v_e_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3460_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3461_ = lean_unsigned_to_nat(3u);
v___x_3462_ = l_Lean_Expr_isAppOfArity(v_e_3454_, v___x_3460_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref(v_e_3454_);
v___x_3463_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
else
{
lean_object* v_digitCharExpr_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_digitCharExpr_3465_ = l_Lean_Expr_appArg_x21(v_e_3454_);
v___x_3466_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3467_ = lean_unsigned_to_nat(1u);
v___x_3468_ = l_Lean_Expr_isAppOfArity(v_digitCharExpr_3465_, v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v_digitCharExpr_3465_);
lean_dec_ref(v_e_3454_);
v___x_3469_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v_charExpr_3472_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_Expr_appFn_x21(v_e_3454_);
v_charExpr_3472_ = l_Lean_Expr_appArg_x21(v___x_3471_);
lean_dec_ref(v___x_3471_);
lean_inc_ref(v_charExpr_3472_);
v___x_3473_ = l_Lean_Meta_getCharValue_x3f(v_charExpr_3472_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3512_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3512_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3512_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3507_; 
v_val_3478_ = lean_ctor_get(v_a_3474_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3480_ = v_a_3474_;
v_isShared_3481_ = v_isSharedCheck_3507_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v_a_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3507_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; uint32_t v___x_3483_; uint8_t v___x_3484_; 
v___x_3482_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3483_ = lean_unbox_uint32(v_val_3478_);
lean_dec(v_val_3478_);
v___x_3484_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3485_ = l_Lean_Expr_appArg_x21(v_digitCharExpr_3465_);
v___x_3486_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3487_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_charExpr_3472_);
v___x_3488_ = l_Lean_mkApp3(v___x_3486_, v___x_3485_, v_charExpr_3472_, v___x_3487_);
v___x_3489_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__4, &l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4);
v___x_3490_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__5, &l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5);
v___x_3491_ = l_Lean_mkApp4(v___x_3489_, v___x_3490_, v_digitCharExpr_3465_, v_charExpr_3472_, v___x_3488_);
v___x_3492_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3493_ = l_Lean_mkAppB(v___x_3492_, v_e_3454_, v___x_3491_);
v___x_3494_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3493_);
v___x_3496_ = v___x_3480_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3493_);
v___x_3496_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3497_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*2, v___x_3468_);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3498_);
v___x_3500_ = v___x_3476_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_del_object(v___x_3480_);
lean_dec_ref(v_charExpr_3472_);
lean_dec_ref(v_digitCharExpr_3465_);
lean_dec_ref(v_e_3454_);
v___x_3503_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3503_);
v___x_3505_ = v___x_3476_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
lean_dec(v_a_3474_);
lean_dec_ref(v_charExpr_3472_);
lean_dec_ref(v_digitCharExpr_3465_);
lean_dec_ref(v_e_3454_);
v___x_3508_ = ((lean_object*)(l_Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3508_);
v___x_3510_ = v___x_3476_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_charExpr_3472_);
lean_dec_ref(v_digitCharExpr_3465_);
lean_dec_ref(v_e_3454_);
v_a_3513_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3473_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3473_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg___boxed(lean_object* v_e_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar(lean_object* v_e_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3528_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___boxed(lean_object* v_e_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Char_Nat_reduceEqDigitChar(v_e_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_));
v___x_3566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_));
v___x_3567_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3568_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3565_, v___x_3566_, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23____boxed(lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_();
return v_res_3570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3574_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_));
v___x_3575_ = 1;
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_);
v___x_3577_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3574_, v___x_3575_, v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25____boxed(lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_();
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_));
v___x_3582_ = 1;
v___x_3583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_);
v___x_3584_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3581_, v___x_3582_, v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27____boxed(lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_();
return v_res_3586_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16);
l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17 = _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17();
lean_mark_persistent(l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
}
#ifdef __cplusplus
}
#endif
