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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
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
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceToLower"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(246, 164, 69, 44, 68, 154, 164, 206)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceToUpper___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toUpper"};
static const lean_object* l_Char_reduceToUpper___redArg___closed__0 = (const lean_object*)&l_Char_reduceToUpper___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceToUpper___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToUpper___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceToUpper___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 31, 99, 242, 138, 166, 22, 89)}};
static const lean_object* l_Char_reduceToUpper___redArg___closed__1 = (const lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceToUpper"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(19, 136, 219, 72, 237, 65, 146, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToUpper___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceToNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Char_reduceToNat___redArg___closed__0 = (const lean_object*)&l_Char_reduceToNat___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceToNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceToNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceToNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceToNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 141, 246, 182, 101, 131, 69)}};
static const lean_object* l_Char_reduceToNat___redArg___closed__1 = (const lean_object*)&l_Char_reduceToNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceToNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(69, 114, 185, 38, 145, 239, 81, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToNat___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsWhitespace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isWhitespace"};
static const lean_object* l_Char_reduceIsWhitespace___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsWhitespace___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 198, 33, 133, 239, 7, 155, 87)}};
static const lean_object* l_Char_reduceIsWhitespace___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "reduceIsWhitespace"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(136, 194, 231, 0, 63, 197, 245, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsWhitespace___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsUpper___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isUpper"};
static const lean_object* l_Char_reduceIsUpper___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsUpper___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsUpper___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsUpper___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsUpper___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 247, 101, 132, 107, 237, 7, 181)}};
static const lean_object* l_Char_reduceIsUpper___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsUpper"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(48, 97, 102, 45, 130, 126, 188, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsUpper___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsLower___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isLower"};
static const lean_object* l_Char_reduceIsLower___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsLower___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsLower___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsLower___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 68, 161, 26, 43, 169, 19, 246)}};
static const lean_object* l_Char_reduceIsLower___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsLower"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(170, 130, 124, 235, 92, 103, 233, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsLower___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsAlpha___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isAlpha"};
static const lean_object* l_Char_reduceIsAlpha___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsAlpha___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsAlpha___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 26, 253, 231, 184, 82, 201, 49)}};
static const lean_object* l_Char_reduceIsAlpha___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsAlpha"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(203, 178, 144, 111, 26, 233, 147, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsAlpha___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsDigit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isDigit"};
static const lean_object* l_Char_reduceIsDigit___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsDigit___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsDigit___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsDigit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsDigit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 3, 214, 114, 123, 37, 169, 158)}};
static const lean_object* l_Char_reduceIsDigit___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceIsDigit"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(210, 158, 243, 105, 248, 216, 59, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsDigit___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceIsAlphaNum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isAlphanum"};
static const lean_object* l_Char_reduceIsAlphaNum___redArg___closed__0 = (const lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceIsAlphaNum___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 189, 120, 149, 13, 219, 127, 87)}};
static const lean_object* l_Char_reduceIsAlphaNum___redArg___closed__1 = (const lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceIsAlphaNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(92, 41, 179, 36, 218, 131, 154, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceIsAlphaNum___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceToString"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(78, 126, 108, 201, 251, 160, 71, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToString___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceVal"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(221, 110, 235, 101, 86, 206, 196, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 6}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(79, 159, 98, 241, 171, 227, 76, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(89, 169, 124, 250, 37, 125, 125, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceLE___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(41, 5, 154, 136, 195, 43, 53, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(100, 184, 21, 249, 88, 153, 169, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Char_reduceEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Char_reduceEq___redArg___closed__0 = (const lean_object*)&l_Char_reduceEq___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Char_reduceEq___redArg___closed__1 = (const lean_object*)&l_Char_reduceEq___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(230, 148, 129, 250, 225, 177, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceEq___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Char_reduceNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Char_reduceNe___redArg___closed__0 = (const lean_object*)&l_Char_reduceNe___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Char_reduceNe___redArg___closed__1 = (const lean_object*)&l_Char_reduceNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(141, 192, 11, 11, 58, 38, 59, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(170, 11, 99, 162, 42, 194, 168, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31____boxed(lean_object*);
static const lean_string_object l_Char_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Char_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Char_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Char_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Char_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value),LEAN_SCALAR_PTR_LITERAL(244, 16, 149, 45, 21, 105, 48, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(123, 237, 132, 188, 163, 148, 231, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceToLower___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Char_reduceOfNatAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNatAux"};
static const lean_object* l_Char_reduceOfNatAux___redArg___closed__0 = (const lean_object*)&l_Char_reduceOfNatAux___redArg___closed__0_value;
static const lean_ctor_object l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Char_reduceOfNatAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0),((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 234, 215, 212, 41, 156, 42, 184)}};
static const lean_object* l_Char_reduceOfNatAux___redArg___closed__1 = (const lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reduceOfNatAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value),LEAN_SCALAR_PTR_LITERAL(181, 57, 32, 171, 55, 79, 143, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceOfNatAux___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceDefault"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value),LEAN_SCALAR_PTR_LITERAL(24, 117, 54, 198, 106, 75, 186, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_reduceDefault___redArg___closed__2_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceDigitCharEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 192, 151, 97, 108, 193, 18, 29)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value),LEAN_SCALAR_PTR_LITERAL(74, 133, 65, 18, 82, 189, 182, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceEqDigitChar"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Char_reduceToLower___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value_aux_0),((lean_object*)&l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 192, 151, 97, 108, 193, 18, 29)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value),LEAN_SCALAR_PTR_LITERAL(239, 45, 189, 47, 73, 225, 5, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35____boxed(lean_object*);
lean_object* l_Lean_Char_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getCharValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lean_Char_fromExpr_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_Char_fromExpr_x3f___redArg(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___redArg___boxed(lean_object* v_e_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Char_fromExpr_x3f___redArg(v_e_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec_ref(v_a_12_);
lean_dec(v_a_11_);
lean_dec_ref(v_a_10_);
return v_res_15_;
}
}
lean_object* l_Lean_Char_fromExpr_x3f(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_getCharValue_x3f(v_e_16_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Char_fromExpr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_16_ = stack[0].m_obj;
lean_object* v_a_17_ = stack[1].m_obj;
lean_object* v_a_18_ = stack[2].m_obj;
lean_object* v_a_19_ = stack[3].m_obj;
lean_object* v_a_20_ = stack[4].m_obj;
lean_object* v_a_21_ = stack[5].m_obj;
lean_object* v_a_22_ = stack[6].m_obj;
lean_object* v_a_23_ = stack[7].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Char_fromExpr_x3f(v_e_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___boxed(lean_object* v_e_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Char_fromExpr_x3f(v_e_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
return v_res_36_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(lean_object* v_inst_39_, lean_object* v_declName_40_, lean_object* v_op_41_, lean_object* v_arity_42_, lean_object* v_e_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = l_Lean_Expr_isAppOfArity(v_e_43_, v_declName_40_, v_arity_42_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_op_41_);
lean_dec_ref(v_inst_39_);
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_Expr_appArg_x21(v_e_43_);
v___x_53_ = l_Lean_Meta_getCharValue_x3f(v___x_52_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_76_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_76_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_76_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_76_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
if (lean_obj_tag(v_a_54_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_71_; 
v_val_58_ = lean_ctor_get(v_a_54_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_54_);
if (v_isSharedCheck_71_ == 0)
{
v___x_60_ = v_a_54_;
v_isShared_61_ = v_isSharedCheck_71_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v_a_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_71_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_toExpr_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v_toExpr_62_ = lean_ctor_get(v_inst_39_, 0);
lean_inc_ref(v_toExpr_62_);
lean_dec_ref(v_inst_39_);
v___x_63_ = lean_apply_1(v_op_41_, v_val_58_);
v___x_64_ = lean_apply_1(v_toExpr_62_, v___x_63_);
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 0);
lean_ctor_set(v___x_60_, 0, v___x_64_);
v___x_66_ = v___x_60_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_70_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_66_);
v___x_68_ = v___x_56_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v_a_54_);
lean_dec(v_op_41_);
lean_dec_ref(v_inst_39_);
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_72_);
v___x_74_ = v___x_56_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_op_41_);
lean_dec_ref(v_inst_39_);
v_a_77_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_53_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_53_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_39_ = stack[0].m_obj;
lean_object* v_declName_40_ = stack[1].m_obj;
lean_object* v_op_41_ = stack[2].m_obj;
lean_object* v_arity_42_ = stack[3].m_obj;
lean_object* v_e_43_ = stack[4].m_obj;
lean_object* v_a_44_ = stack[5].m_obj;
lean_object* v_a_45_ = stack[6].m_obj;
lean_object* v_a_46_ = stack[7].m_obj;
lean_object* v_a_47_ = stack[8].m_obj;
lean_object* v_res_85_;
v_res_85_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(v_inst_39_, v_declName_40_, v_op_41_, v_arity_42_, v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___boxed(lean_object* v_inst_86_, lean_object* v_declName_87_, lean_object* v_op_88_, lean_object* v_arity_89_, lean_object* v_e_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(v_inst_86_, v_declName_87_, v_op_88_, v_arity_89_, v_e_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec_ref(v_e_90_);
lean_dec(v_declName_87_);
return v_res_96_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_declName_99_, lean_object* v_op_100_, lean_object* v_arity_101_, lean_object* v_e_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_Expr_isAppOfArity(v_e_102_, v_declName_99_, v_arity_101_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_op_100_);
lean_dec_ref(v_inst_98_);
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_Expr_appArg_x21(v_e_102_);
v___x_115_ = l_Lean_Meta_getCharValue_x3f(v___x_114_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_138_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_138_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_a_116_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_133_; 
v_val_120_ = lean_ctor_get(v_a_116_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_a_116_);
if (v_isSharedCheck_133_ == 0)
{
v___x_122_ = v_a_116_;
v_isShared_123_ = v_isSharedCheck_133_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_dec(v_a_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_133_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_toExpr_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v_toExpr_124_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toExpr_124_);
lean_dec_ref(v_inst_98_);
v___x_125_ = lean_apply_1(v_op_100_, v_val_120_);
v___x_126_ = lean_apply_1(v_toExpr_124_, v___x_125_);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 0);
lean_ctor_set(v___x_122_, 0, v___x_126_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_128_);
v___x_130_ = v___x_118_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_a_116_);
lean_dec(v_op_100_);
lean_dec_ref(v_inst_98_);
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_134_);
v___x_136_ = v___x_118_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_op_100_);
lean_dec_ref(v_inst_98_);
v_a_139_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_115_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_115_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_98_ = stack[1].m_obj;
lean_object* v_declName_99_ = stack[2].m_obj;
lean_object* v_op_100_ = stack[3].m_obj;
lean_object* v_arity_101_ = stack[4].m_obj;
lean_object* v_e_102_ = stack[5].m_obj;
lean_object* v_a_103_ = stack[6].m_obj;
lean_object* v_a_104_ = stack[7].m_obj;
lean_object* v_a_105_ = stack[8].m_obj;
lean_object* v_a_106_ = stack[9].m_obj;
lean_object* v_a_107_ = stack[10].m_obj;
lean_object* v_a_108_ = stack[11].m_obj;
lean_object* v_a_109_ = stack[12].m_obj;
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(lean_box(0), v_inst_98_, v_declName_99_, v_op_100_, v_arity_101_, v_e_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___boxed(lean_object* v_00_u03b1_148_, lean_object* v_inst_149_, lean_object* v_declName_150_, lean_object* v_op_151_, lean_object* v_arity_152_, lean_object* v_e_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(v_00_u03b1_148_, v_inst_149_, v_declName_150_, v_op_151_, v_arity_152_, v_e_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_e_153_);
lean_dec(v_declName_150_);
return v_res_162_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(lean_object* v_declName_165_, lean_object* v_arity_166_, lean_object* v_op_167_, lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Expr_isAppOfArity(v_e_168_, v_declName_165_, v_arity_166_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_e_168_);
lean_dec_ref(v_op_167_);
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = l_Lean_Expr_appFn_x21(v_e_168_);
v___x_178_ = l_Lean_Expr_appArg_x21(v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = l_Lean_Meta_getCharValue_x3f(v___x_178_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_212_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_212_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_212_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_212_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
if (lean_obj_tag(v_a_180_) == 1)
{
lean_object* v_val_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_del_object(v___x_182_);
v_val_184_ = lean_ctor_get(v_a_180_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v_a_180_, 1);
v___x_185_ = l_Lean_Expr_appArg_x21(v_e_168_);
v___x_186_ = l_Lean_Meta_getCharValue_x3f(v___x_185_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_199_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_199_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_199_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_199_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
if (lean_obj_tag(v_a_187_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
lean_del_object(v___x_189_);
v_val_191_ = lean_ctor_get(v_a_187_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v_a_187_, 1);
v___x_192_ = lean_apply_2(v_op_167_, v_val_184_, v_val_191_);
v___x_193_ = lean_unbox(v___x_192_);
v___x_194_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_168_, v___x_193_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_dec(v_a_187_);
lean_dec(v_val_184_);
lean_dec_ref(v_e_168_);
lean_dec_ref(v_op_167_);
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_195_);
v___x_197_ = v___x_189_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_val_184_);
lean_dec_ref(v_e_168_);
lean_dec_ref(v_op_167_);
v_a_200_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_186_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_186_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_a_180_);
lean_dec_ref(v_e_168_);
lean_dec_ref(v_op_167_);
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_208_);
v___x_210_ = v___x_182_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_e_168_);
lean_dec_ref(v_op_167_);
v_a_213_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_179_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_179_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_165_ = stack[0].m_obj;
lean_object* v_arity_166_ = stack[1].m_obj;
lean_object* v_op_167_ = stack[2].m_obj;
lean_object* v_e_168_ = stack[3].m_obj;
lean_object* v_a_169_ = stack[4].m_obj;
lean_object* v_a_170_ = stack[5].m_obj;
lean_object* v_a_171_ = stack[6].m_obj;
lean_object* v_a_172_ = stack[7].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(v_declName_165_, v_arity_166_, v_op_167_, v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___boxed(lean_object* v_declName_222_, lean_object* v_arity_223_, lean_object* v_op_224_, lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(v_declName_222_, v_arity_223_, v_op_224_, v_e_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_declName_222_);
return v_res_231_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(lean_object* v_declName_232_, lean_object* v_arity_233_, lean_object* v_op_234_, lean_object* v_e_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = l_Lean_Expr_isAppOfArity(v_e_235_, v_declName_232_, v_arity_233_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref(v_e_235_);
lean_dec_ref(v_op_234_);
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = l_Lean_Expr_appFn_x21(v_e_235_);
v___x_248_ = l_Lean_Expr_appArg_x21(v___x_247_);
lean_dec_ref(v___x_247_);
v___x_249_ = l_Lean_Meta_getCharValue_x3f(v___x_248_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_282_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_282_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_282_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_282_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
if (lean_obj_tag(v_a_250_) == 1)
{
lean_object* v_val_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_del_object(v___x_252_);
v_val_254_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_a_250_, 1);
v___x_255_ = l_Lean_Expr_appArg_x21(v_e_235_);
v___x_256_ = l_Lean_Meta_getCharValue_x3f(v___x_255_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_269_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_269_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
lean_del_object(v___x_259_);
v_val_261_ = lean_ctor_get(v_a_257_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_a_257_, 1);
v___x_262_ = lean_apply_2(v_op_234_, v_val_254_, v_val_261_);
v___x_263_ = lean_unbox(v___x_262_);
v___x_264_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_235_, v___x_263_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_267_; 
lean_dec(v_a_257_);
lean_dec(v_val_254_);
lean_dec_ref(v_e_235_);
lean_dec_ref(v_op_234_);
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_265_);
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
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
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_val_254_);
lean_dec_ref(v_e_235_);
lean_dec_ref(v_op_234_);
v_a_270_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_256_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_256_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
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
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v_a_250_);
lean_dec_ref(v_e_235_);
lean_dec_ref(v_op_234_);
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_278_);
v___x_280_ = v___x_252_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v_e_235_);
lean_dec_ref(v_op_234_);
v_a_283_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_249_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_249_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_232_ = stack[0].m_obj;
lean_object* v_arity_233_ = stack[1].m_obj;
lean_object* v_op_234_ = stack[2].m_obj;
lean_object* v_e_235_ = stack[3].m_obj;
lean_object* v_a_236_ = stack[4].m_obj;
lean_object* v_a_237_ = stack[5].m_obj;
lean_object* v_a_238_ = stack[6].m_obj;
lean_object* v_a_239_ = stack[7].m_obj;
lean_object* v_a_240_ = stack[8].m_obj;
lean_object* v_a_241_ = stack[9].m_obj;
lean_object* v_a_242_ = stack[10].m_obj;
lean_object* v_res_291_;
v_res_291_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(v_declName_232_, v_arity_233_, v_op_234_, v_e_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___boxed(lean_object* v_declName_292_, lean_object* v_arity_293_, lean_object* v_op_294_, lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(v_declName_292_, v_arity_293_, v_op_294_, v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec(v_declName_292_);
return v_res_304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_box(0);
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2));
v___x_312_ = l_Lean_mkConst(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5));
v___x_319_ = l_Lean_mkConst(v___x_318_, v___x_317_);
return v___x_319_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(lean_object* v_declName_320_, lean_object* v_arity_321_, lean_object* v_op_322_, lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_Expr_isAppOfArity(v_e_323_, v_declName_320_, v_arity_321_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_op_322_);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lean_Expr_appFn_x21(v_e_323_);
v___x_333_ = l_Lean_Expr_appArg_x21(v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = l_Lean_Meta_getCharValue_x3f(v___x_333_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_380_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_380_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_380_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_380_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
if (lean_obj_tag(v_a_335_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_375_; 
v_val_339_ = lean_ctor_get(v_a_335_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_335_);
if (v_isSharedCheck_375_ == 0)
{
v___x_341_ = v_a_335_;
v_isShared_342_ = v_isSharedCheck_375_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v_a_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_375_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = l_Lean_Expr_appArg_x21(v_e_323_);
v___x_344_ = l_Lean_Meta_getCharValue_x3f(v___x_343_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_366_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_366_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___y_350_; 
if (lean_obj_tag(v_a_345_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_del_object(v___x_337_);
v_val_357_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v_a_345_, 1);
v___x_358_ = lean_apply_2(v_op_322_, v_val_339_, v_val_357_);
v___x_359_ = lean_unbox(v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_350_ = v___x_360_;
goto v___jp_349_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_350_ = v___x_361_;
goto v___jp_349_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_del_object(v___x_347_);
lean_dec(v_a_345_);
lean_del_object(v___x_341_);
lean_dec(v_val_339_);
lean_dec_ref(v_op_322_);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_362_);
v___x_364_ = v___x_337_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
v___jp_349_:
{
lean_object* v___x_352_; 
lean_inc_ref(v___y_350_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 0);
lean_ctor_set(v___x_341_, 0, v___y_350_);
v___x_352_ = v___x_341_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___y_350_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_352_);
v___x_354_ = v___x_347_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_del_object(v___x_341_);
lean_dec(v_val_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v_op_322_);
v_a_367_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_344_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_344_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
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
}
else
{
lean_object* v___x_376_; lean_object* v___x_378_; 
lean_dec(v_a_335_);
lean_dec_ref(v_op_322_);
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_376_);
v___x_378_ = v___x_337_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_op_322_);
v_a_381_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_334_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_334_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_320_ = stack[0].m_obj;
lean_object* v_arity_321_ = stack[1].m_obj;
lean_object* v_op_322_ = stack[2].m_obj;
lean_object* v_e_323_ = stack[3].m_obj;
lean_object* v_a_324_ = stack[4].m_obj;
lean_object* v_a_325_ = stack[5].m_obj;
lean_object* v_a_326_ = stack[6].m_obj;
lean_object* v_a_327_ = stack[7].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(v_declName_320_, v_arity_321_, v_op_322_, v_e_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___boxed(lean_object* v_declName_390_, lean_object* v_arity_391_, lean_object* v_op_392_, lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(v_declName_390_, v_arity_391_, v_op_392_, v_e_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec_ref(v_e_393_);
lean_dec(v_declName_390_);
return v_res_399_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(lean_object* v_declName_400_, lean_object* v_arity_401_, lean_object* v_op_402_, lean_object* v_e_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_Lean_Expr_isAppOfArity(v_e_403_, v_declName_400_, v_arity_401_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v_op_402_);
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_Expr_appFn_x21(v_e_403_);
v___x_416_ = l_Lean_Expr_appArg_x21(v___x_415_);
lean_dec_ref(v___x_415_);
v___x_417_ = l_Lean_Meta_getCharValue_x3f(v___x_416_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_463_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_463_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_463_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_463_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_458_; 
v_val_422_ = lean_ctor_get(v_a_418_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_458_ == 0)
{
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_458_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_458_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_Expr_appArg_x21(v_e_403_);
v___x_427_ = l_Lean_Meta_getCharValue_x3f(v___x_426_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_449_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_449_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_449_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_449_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___y_433_; 
if (lean_obj_tag(v_a_428_) == 1)
{
lean_object* v_val_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
lean_del_object(v___x_420_);
v_val_440_ = lean_ctor_get(v_a_428_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_428_, 1);
v___x_441_ = lean_apply_2(v_op_402_, v_val_422_, v_val_440_);
v___x_442_ = lean_unbox(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_433_ = v___x_443_;
goto v___jp_432_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_del_object(v___x_430_);
lean_dec(v_a_428_);
lean_del_object(v___x_424_);
lean_dec(v_val_422_);
lean_dec_ref(v_op_402_);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_445_);
v___x_447_ = v___x_420_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
v___jp_432_:
{
lean_object* v___x_435_; 
lean_inc_ref(v___y_433_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v___y_433_);
v___x_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___y_433_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_435_);
v___x_437_ = v___x_430_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_del_object(v___x_424_);
lean_dec(v_val_422_);
lean_del_object(v___x_420_);
lean_dec_ref(v_op_402_);
v_a_450_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_427_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_427_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_a_418_);
lean_dec_ref(v_op_402_);
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_459_);
v___x_461_ = v___x_420_;
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
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_op_402_);
v_a_464_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_417_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_417_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_400_ = stack[0].m_obj;
lean_object* v_arity_401_ = stack[1].m_obj;
lean_object* v_op_402_ = stack[2].m_obj;
lean_object* v_e_403_ = stack[3].m_obj;
lean_object* v_a_404_ = stack[4].m_obj;
lean_object* v_a_405_ = stack[5].m_obj;
lean_object* v_a_406_ = stack[6].m_obj;
lean_object* v_a_407_ = stack[7].m_obj;
lean_object* v_a_408_ = stack[8].m_obj;
lean_object* v_a_409_ = stack[9].m_obj;
lean_object* v_a_410_ = stack[10].m_obj;
lean_object* v_res_472_;
v_res_472_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(v_declName_400_, v_arity_401_, v_op_402_, v_e_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___boxed(lean_object* v_declName_473_, lean_object* v_arity_474_, lean_object* v_op_475_, lean_object* v_e_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(v_declName_473_, v_arity_474_, v_op_475_, v_e_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_e_476_);
lean_dec(v_declName_473_);
return v_res_485_;
}
}
static lean_object* _init_l_Char_reduceToLower___redArg___closed__5(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l_Char_reduceToLower___redArg___closed__4));
v___x_497_ = l_Lean_mkConst(v___x_496_, v___x_495_);
return v___x_497_;
}
}
lean_object* l_Char_reduceToLower___redArg(lean_object* v_e_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_504_ = ((lean_object*)(l_Char_reduceToLower___redArg___closed__2));
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = l_Lean_Expr_isAppOfArity(v_e_498_, v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_Lean_Expr_appArg_x21(v_e_498_);
v___x_510_ = l_Lean_Meta_getCharValue_x3f(v___x_509_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_539_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_539_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_539_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_539_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint32_t v___y_516_; 
if (lean_obj_tag(v_a_511_) == 1)
{
lean_object* v_val_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint8_t v___x_528_; 
v_val_525_ = lean_ctor_get(v_a_511_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_a_511_, 1);
v___x_526_ = 65;
v___x_527_ = lean_unbox_uint32(v_val_525_);
v___x_528_ = lean_uint32_dec_le(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
uint32_t v___x_529_; 
v___x_529_ = lean_unbox_uint32(v_val_525_);
lean_dec(v_val_525_);
v___y_516_ = v___x_529_;
goto v___jp_515_;
}
else
{
uint32_t v___x_530_; uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = 90;
v___x_531_ = lean_unbox_uint32(v_val_525_);
v___x_532_ = lean_uint32_dec_le(v___x_531_, v___x_530_);
if (v___x_532_ == 0)
{
uint32_t v___x_533_; 
v___x_533_ = lean_unbox_uint32(v_val_525_);
lean_dec(v_val_525_);
v___y_516_ = v___x_533_;
goto v___jp_515_;
}
else
{
uint32_t v___x_534_; uint32_t v___x_535_; uint32_t v___x_536_; 
v___x_534_ = 32;
v___x_535_ = lean_unbox_uint32(v_val_525_);
lean_dec(v_val_525_);
v___x_536_ = lean_uint32_add(v___x_535_, v___x_534_);
v___y_516_ = v___x_536_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_513_);
lean_dec(v_a_511_);
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_517_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_518_ = lean_uint32_to_nat(v___y_516_);
v___x_519_ = l_Lean_mkRawNatLit(v___x_518_);
v___x_520_ = l_Lean_Expr_app___override(v___x_517_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_521_);
v___x_523_ = v___x_513_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_510_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_510_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceToLower___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_498_ = stack[0].m_obj;
lean_object* v_a_499_ = stack[1].m_obj;
lean_object* v_a_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Char_reduceToLower___redArg(v_e_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Char_reduceToLower___redArg(v_e_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_e_549_);
return v_res_555_;
}
}
lean_object* l_Char_reduceToLower(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Char_reduceToLower___redArg(v_e_556_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Char_reduceToLower_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_556_ = stack[0].m_obj;
lean_object* v_a_557_ = stack[1].m_obj;
lean_object* v_a_558_ = stack[2].m_obj;
lean_object* v_a_559_ = stack[3].m_obj;
lean_object* v_a_560_ = stack[4].m_obj;
lean_object* v_a_561_ = stack[5].m_obj;
lean_object* v_a_562_ = stack[6].m_obj;
lean_object* v_a_563_ = stack[7].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Char_reduceToLower(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Char_reduceToLower(v_e_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_e_567_);
return v_res_576_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_593_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_594_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_595_;
v_res_595_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_();
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20____boxed(lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_();
return v_res_597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_602_ = 1;
v___x_603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_);
v___x_604_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_601_, v___x_602_, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_605_;
v_res_605_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_();
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22____boxed(lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_();
return v_res_607_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_610_ = 1;
v___x_611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_);
v___x_612_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_609_, v___x_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_613_;
v_res_613_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_();
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24____boxed(lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_();
return v_res_615_;
}
}
lean_object* l_Char_reduceToUpper___redArg(lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = ((lean_object*)(l_Char_reduceToUpper___redArg___closed__1));
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = l_Lean_Expr_isAppOfArity(v_e_620_, v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = l_Lean_Expr_appArg_x21(v_e_620_);
v___x_632_ = l_Lean_Meta_getCharValue_x3f(v___x_631_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_661_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_661_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint32_t v___y_638_; 
if (lean_obj_tag(v_a_633_) == 1)
{
lean_object* v_val_647_; uint32_t v___x_648_; uint32_t v___x_649_; uint8_t v___x_650_; 
v_val_647_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_a_633_, 1);
v___x_648_ = 97;
v___x_649_ = lean_unbox_uint32(v_val_647_);
v___x_650_ = lean_uint32_dec_le(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
uint32_t v___x_651_; 
v___x_651_ = lean_unbox_uint32(v_val_647_);
lean_dec(v_val_647_);
v___y_638_ = v___x_651_;
goto v___jp_637_;
}
else
{
uint32_t v___x_652_; uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = 122;
v___x_653_ = lean_unbox_uint32(v_val_647_);
v___x_654_ = lean_uint32_dec_le(v___x_653_, v___x_652_);
if (v___x_654_ == 0)
{
uint32_t v___x_655_; 
v___x_655_ = lean_unbox_uint32(v_val_647_);
lean_dec(v_val_647_);
v___y_638_ = v___x_655_;
goto v___jp_637_;
}
else
{
uint32_t v___x_656_; uint32_t v___x_657_; uint32_t v___x_658_; 
v___x_656_ = 4294967264;
v___x_657_ = lean_unbox_uint32(v_val_647_);
lean_dec(v_val_647_);
v___x_658_ = lean_uint32_add(v___x_657_, v___x_656_);
v___y_638_ = v___x_658_;
goto v___jp_637_;
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
lean_del_object(v___x_635_);
lean_dec(v_a_633_);
v___x_659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_639_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_640_ = lean_uint32_to_nat(v___y_638_);
v___x_641_ = l_Lean_mkRawNatLit(v___x_640_);
v___x_642_ = l_Lean_Expr_app___override(v___x_639_, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_643_);
v___x_645_ = v___x_635_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_632_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_632_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceToUpper___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_620_ = stack[0].m_obj;
lean_object* v_a_621_ = stack[1].m_obj;
lean_object* v_a_622_ = stack[2].m_obj;
lean_object* v_a_623_ = stack[3].m_obj;
lean_object* v_a_624_ = stack[4].m_obj;
lean_object* v_res_670_;
v_res_670_ = l_Char_reduceToUpper___redArg(v_e_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object* v_e_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Char_reduceToUpper___redArg(v_e_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec_ref(v_e_671_);
return v_res_677_;
}
}
lean_object* l_Char_reduceToUpper(lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Char_reduceToUpper___redArg(v_e_678_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v___x_687_;
}
}
LEAN_EXPORT void l_Char_reduceToUpper_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_678_ = stack[0].m_obj;
lean_object* v_a_679_ = stack[1].m_obj;
lean_object* v_a_680_ = stack[2].m_obj;
lean_object* v_a_681_ = stack[3].m_obj;
lean_object* v_a_682_ = stack[4].m_obj;
lean_object* v_a_683_ = stack[5].m_obj;
lean_object* v_a_684_ = stack[6].m_obj;
lean_object* v_a_685_ = stack[7].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Char_reduceToUpper(v_e_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object* v_e_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Char_reduceToUpper(v_e_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_e_689_);
return v_res_698_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_715_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_716_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_713_, v___x_714_, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_717_;
v_res_717_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_();
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20____boxed(lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_();
return v_res_719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_724_ = 1;
v___x_725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_);
v___x_726_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_727_;
v_res_727_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_();
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22____boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_();
return v_res_729_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_732_ = 1;
v___x_733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_);
v___x_734_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_731_, v___x_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_735_;
v_res_735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_();
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24____boxed(lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_();
return v_res_737_;
}
}
lean_object* l_Char_reduceToNat___redArg(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = ((lean_object*)(l_Char_reduceToNat___redArg___closed__1));
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = l_Lean_Expr_isAppOfArity(v_e_742_, v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l_Lean_Expr_appArg_x21(v_e_742_);
v___x_754_ = l_Lean_Meta_getCharValue_x3f(v___x_753_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_777_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_777_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_777_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_777_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
if (lean_obj_tag(v_a_755_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_772_; 
v_val_759_ = lean_ctor_get(v_a_755_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_772_ == 0)
{
v___x_761_ = v_a_755_;
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_val_759_);
lean_dec(v_a_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint32_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = lean_unbox_uint32(v_val_759_);
lean_dec(v_val_759_);
v___x_764_ = lean_uint32_to_nat(v___x_763_);
v___x_765_ = l_Lean_mkNatLit(v___x_764_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
lean_ctor_set(v___x_761_, 0, v___x_765_);
v___x_767_ = v___x_761_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_767_);
v___x_769_ = v___x_757_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_a_755_);
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_773_);
v___x_775_ = v___x_757_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
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
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_754_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_754_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceToNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_742_ = stack[0].m_obj;
lean_object* v_a_743_ = stack[1].m_obj;
lean_object* v_a_744_ = stack[2].m_obj;
lean_object* v_a_745_ = stack[3].m_obj;
lean_object* v_a_746_ = stack[4].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Char_reduceToNat___redArg(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object* v_e_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Char_reduceToNat___redArg(v_e_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec_ref(v_e_787_);
return v_res_793_;
}
}
lean_object* l_Char_reduceToNat(lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Char_reduceToNat___redArg(v_e_794_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
return v___x_803_;
}
}
LEAN_EXPORT void l_Char_reduceToNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_794_ = stack[0].m_obj;
lean_object* v_a_795_ = stack[1].m_obj;
lean_object* v_a_796_ = stack[2].m_obj;
lean_object* v_a_797_ = stack[3].m_obj;
lean_object* v_a_798_ = stack[4].m_obj;
lean_object* v_a_799_ = stack[5].m_obj;
lean_object* v_a_800_ = stack[6].m_obj;
lean_object* v_a_801_ = stack[7].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Char_reduceToNat(v_e_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Char_reduceToNat(v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_e_805_);
return v_res_814_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_831_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_832_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_829_, v___x_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_833_;
v_res_833_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_();
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20____boxed(lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_();
return v_res_835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_840_ = 1;
v___x_841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_);
v___x_842_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_839_, v___x_840_, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_843_;
v_res_843_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_();
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22____boxed(lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_();
return v_res_845_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_848_ = 1;
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_);
v___x_850_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_847_, v___x_848_, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_851_;
v_res_851_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_();
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24____boxed(lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_();
return v_res_853_;
}
}
lean_object* l_Char_reduceIsWhitespace___redArg(lean_object* v_e_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = ((lean_object*)(l_Char_reduceIsWhitespace___redArg___closed__1));
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = l_Lean_Expr_isAppOfArity(v_e_858_, v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = l_Lean_Expr_appArg_x21(v_e_858_);
v___x_870_ = l_Lean_Meta_getCharValue_x3f(v___x_869_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_899_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_899_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_899_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_899_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___y_876_; 
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_883_; uint32_t v___x_884_; uint32_t v___x_885_; uint8_t v___x_886_; 
v_val_883_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v_a_871_, 1);
v___x_884_ = 32;
v___x_885_ = lean_unbox_uint32(v_val_883_);
v___x_886_ = lean_uint32_dec_eq(v___x_885_, v___x_884_);
if (v___x_886_ == 0)
{
uint32_t v___x_887_; uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_887_ = 9;
v___x_888_ = lean_unbox_uint32(v_val_883_);
v___x_889_ = lean_uint32_dec_eq(v___x_888_, v___x_887_);
if (v___x_889_ == 0)
{
uint32_t v___x_890_; uint32_t v___x_891_; uint8_t v___x_892_; 
v___x_890_ = 13;
v___x_891_ = lean_unbox_uint32(v_val_883_);
v___x_892_ = lean_uint32_dec_eq(v___x_891_, v___x_890_);
if (v___x_892_ == 0)
{
uint32_t v___x_893_; uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_893_ = 10;
v___x_894_ = lean_unbox_uint32(v_val_883_);
lean_dec(v_val_883_);
v___x_895_ = lean_uint32_dec_eq(v___x_894_, v___x_893_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_876_ = v___x_896_;
goto v___jp_875_;
}
else
{
goto v___jp_881_;
}
}
else
{
lean_dec(v_val_883_);
goto v___jp_881_;
}
}
else
{
lean_dec(v_val_883_);
goto v___jp_881_;
}
}
else
{
lean_dec(v_val_883_);
goto v___jp_881_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_873_);
lean_dec(v_a_871_);
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
v___jp_875_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc_ref(v___y_876_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___y_876_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
v___jp_881_:
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_876_ = v___x_882_;
goto v___jp_875_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_900_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_870_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_870_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceIsWhitespace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_858_ = stack[0].m_obj;
lean_object* v_a_859_ = stack[1].m_obj;
lean_object* v_a_860_ = stack[2].m_obj;
lean_object* v_a_861_ = stack[3].m_obj;
lean_object* v_a_862_ = stack[4].m_obj;
lean_object* v_res_908_;
v_res_908_ = l_Char_reduceIsWhitespace___redArg(v_e_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object* v_e_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Char_reduceIsWhitespace___redArg(v_e_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec_ref(v_e_909_);
return v_res_915_;
}
}
lean_object* l_Char_reduceIsWhitespace(lean_object* v_e_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Char_reduceIsWhitespace___redArg(v_e_916_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_925_;
}
}
LEAN_EXPORT void l_Char_reduceIsWhitespace_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_916_ = stack[0].m_obj;
lean_object* v_a_917_ = stack[1].m_obj;
lean_object* v_a_918_ = stack[2].m_obj;
lean_object* v_a_919_ = stack[3].m_obj;
lean_object* v_a_920_ = stack[4].m_obj;
lean_object* v_a_921_ = stack[5].m_obj;
lean_object* v_a_922_ = stack[6].m_obj;
lean_object* v_a_923_ = stack[7].m_obj;
lean_object* v_res_926_;
v_res_926_ = l_Char_reduceIsWhitespace(v_e_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object* v_e_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Char_reduceIsWhitespace(v_e_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_e_927_);
return v_res_936_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_953_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_954_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_951_, v___x_952_, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_955_;
v_res_955_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_();
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20____boxed(lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_();
return v_res_957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_962_ = 1;
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_);
v___x_964_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_961_, v___x_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_965_;
v_res_965_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_();
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22____boxed(lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_();
return v_res_967_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_970_ = 1;
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_);
v___x_972_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_969_, v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_973_;
v_res_973_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_();
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24____boxed(lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_();
return v_res_975_;
}
}
lean_object* l_Char_reduceIsUpper___redArg(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = ((lean_object*)(l_Char_reduceIsUpper___redArg___closed__1));
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = l_Lean_Expr_isAppOfArity(v_e_980_, v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Lean_Expr_appArg_x21(v_e_980_);
v___x_992_ = l_Lean_Meta_getCharValue_x3f(v___x_991_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1015_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1015_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1015_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___y_998_; 
if (lean_obj_tag(v_a_993_) == 1)
{
lean_object* v_val_1005_; uint32_t v___x_1006_; uint32_t v___x_1007_; uint8_t v___x_1008_; 
v_val_1005_ = lean_ctor_get(v_a_993_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_a_993_, 1);
v___x_1006_ = 65;
v___x_1007_ = lean_unbox_uint32(v_val_1005_);
v___x_1008_ = lean_uint32_dec_le(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec(v_val_1005_);
goto v___jp_1003_;
}
else
{
uint32_t v___x_1009_; uint32_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = 90;
v___x_1010_ = lean_unbox_uint32(v_val_1005_);
lean_dec(v_val_1005_);
v___x_1011_ = lean_uint32_dec_le(v___x_1010_, v___x_1009_);
if (v___x_1011_ == 0)
{
goto v___jp_1003_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_998_ = v___x_1012_;
goto v___jp_997_;
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_del_object(v___x_995_);
lean_dec(v_a_993_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_inc_ref(v___y_998_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___y_998_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
v___jp_1003_:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_998_ = v___x_1004_;
goto v___jp_997_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_992_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_992_);
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
}
}
LEAN_EXPORT void l_Char_reduceIsUpper___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_980_ = stack[0].m_obj;
lean_object* v_a_981_ = stack[1].m_obj;
lean_object* v_a_982_ = stack[2].m_obj;
lean_object* v_a_983_ = stack[3].m_obj;
lean_object* v_a_984_ = stack[4].m_obj;
lean_object* v_res_1024_;
v_res_1024_ = l_Char_reduceIsUpper___redArg(v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
stack->m_obj
 = v_res_1024_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Char_reduceIsUpper___redArg(v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec_ref(v_e_1025_);
return v_res_1031_;
}
}
lean_object* l_Char_reduceIsUpper(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Char_reduceIsUpper___redArg(v_e_1032_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT void l_Char_reduceIsUpper_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1032_ = stack[0].m_obj;
lean_object* v_a_1033_ = stack[1].m_obj;
lean_object* v_a_1034_ = stack[2].m_obj;
lean_object* v_a_1035_ = stack[3].m_obj;
lean_object* v_a_1036_ = stack[4].m_obj;
lean_object* v_a_1037_ = stack[5].m_obj;
lean_object* v_a_1038_ = stack[6].m_obj;
lean_object* v_a_1039_ = stack[7].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l_Char_reduceIsUpper(v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object* v_e_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Char_reduceIsUpper(v_e_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_e_1043_);
return v_res_1052_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1069_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1070_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1067_, v___x_1068_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1071_;
v_res_1071_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1071_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20____boxed(lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_();
return v_res_1073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1078_ = 1;
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_);
v___x_1080_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1077_, v___x_1078_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1081_;
v_res_1081_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22____boxed(lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_();
return v_res_1083_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1086_ = 1;
v___x_1087_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_);
v___x_1088_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1085_, v___x_1086_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1089_;
v_res_1089_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1089_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24____boxed(lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_();
return v_res_1091_;
}
}
lean_object* l_Char_reduceIsLower___redArg(lean_object* v_e_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = ((lean_object*)(l_Char_reduceIsLower___redArg___closed__1));
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = l_Lean_Expr_isAppOfArity(v_e_1096_, v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_Expr_appArg_x21(v_e_1096_);
v___x_1108_ = l_Lean_Meta_getCharValue_x3f(v___x_1107_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1131_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1131_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1131_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___y_1114_; 
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_val_1121_; uint32_t v___x_1122_; uint32_t v___x_1123_; uint8_t v___x_1124_; 
v_val_1121_ = lean_ctor_get(v_a_1109_, 0);
lean_inc(v_val_1121_);
lean_dec_ref_known(v_a_1109_, 1);
v___x_1122_ = 97;
v___x_1123_ = lean_unbox_uint32(v_val_1121_);
v___x_1124_ = lean_uint32_dec_le(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec(v_val_1121_);
goto v___jp_1119_;
}
else
{
uint32_t v___x_1125_; uint32_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = 122;
v___x_1126_ = lean_unbox_uint32(v_val_1121_);
lean_dec(v_val_1121_);
v___x_1127_ = lean_uint32_dec_le(v___x_1126_, v___x_1125_);
if (v___x_1127_ == 0)
{
goto v___jp_1119_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1114_ = v___x_1128_;
goto v___jp_1113_;
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1111_);
lean_dec(v_a_1109_);
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_inc_ref(v___y_1114_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___y_1114_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1115_);
v___x_1117_ = v___x_1111_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
v___jp_1119_:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1114_ = v___x_1120_;
goto v___jp_1113_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1108_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1108_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceIsLower___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1096_ = stack[0].m_obj;
lean_object* v_a_1097_ = stack[1].m_obj;
lean_object* v_a_1098_ = stack[2].m_obj;
lean_object* v_a_1099_ = stack[3].m_obj;
lean_object* v_a_1100_ = stack[4].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l_Char_reduceIsLower___redArg(v_e_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object* v_e_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Char_reduceIsLower___redArg(v_e_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_e_1141_);
return v_res_1147_;
}
}
lean_object* l_Char_reduceIsLower(lean_object* v_e_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Char_reduceIsLower___redArg(v_e_1148_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT void l_Char_reduceIsLower_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1148_ = stack[0].m_obj;
lean_object* v_a_1149_ = stack[1].m_obj;
lean_object* v_a_1150_ = stack[2].m_obj;
lean_object* v_a_1151_ = stack[3].m_obj;
lean_object* v_a_1152_ = stack[4].m_obj;
lean_object* v_a_1153_ = stack[5].m_obj;
lean_object* v_a_1154_ = stack[6].m_obj;
lean_object* v_a_1155_ = stack[7].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l_Char_reduceIsLower(v_e_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object* v_e_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Char_reduceIsLower(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_e_1159_);
return v_res_1168_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1185_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1186_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1183_, v___x_1184_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1187_;
v_res_1187_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20____boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_();
return v_res_1189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1194_ = 1;
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_);
v___x_1196_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1193_, v___x_1194_, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1197_;
v_res_1197_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22____boxed(lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_();
return v_res_1199_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1202_ = 1;
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_);
v___x_1204_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1201_, v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1205_;
v_res_1205_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24____boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_();
return v_res_1207_;
}
}
lean_object* l_Char_reduceIsAlpha___redArg(lean_object* v_e_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = ((lean_object*)(l_Char_reduceIsAlpha___redArg___closed__1));
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = l_Lean_Expr_isAppOfArity(v_e_1212_, v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = l_Lean_Expr_appArg_x21(v_e_1212_);
v___x_1224_ = l_Lean_Meta_getCharValue_x3f(v___x_1223_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1255_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___y_1230_; 
if (lean_obj_tag(v_a_1225_) == 1)
{
lean_object* v_val_1239_; uint32_t v___x_1247_; uint32_t v___x_1248_; uint8_t v___x_1249_; 
v_val_1239_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_a_1225_, 1);
v___x_1247_ = 65;
v___x_1248_ = lean_unbox_uint32(v_val_1239_);
v___x_1249_ = lean_uint32_dec_le(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
goto v___jp_1240_;
}
else
{
uint32_t v___x_1250_; uint32_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = 90;
v___x_1251_ = lean_unbox_uint32(v_val_1239_);
v___x_1252_ = lean_uint32_dec_le(v___x_1251_, v___x_1250_);
if (v___x_1252_ == 0)
{
goto v___jp_1240_;
}
else
{
lean_dec(v_val_1239_);
goto v___jp_1237_;
}
}
v___jp_1240_:
{
uint32_t v___x_1241_; uint32_t v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = 97;
v___x_1242_ = lean_unbox_uint32(v_val_1239_);
v___x_1243_ = lean_uint32_dec_le(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v_val_1239_);
goto v___jp_1235_;
}
else
{
uint32_t v___x_1244_; uint32_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = 122;
v___x_1245_ = lean_unbox_uint32(v_val_1239_);
lean_dec(v_val_1239_);
v___x_1246_ = lean_uint32_dec_le(v___x_1245_, v___x_1244_);
if (v___x_1246_ == 0)
{
goto v___jp_1235_;
}
else
{
goto v___jp_1237_;
}
}
}
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_del_object(v___x_1227_);
lean_dec(v_a_1225_);
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
v___jp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_inc_ref(v___y_1230_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___y_1230_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1231_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
v___jp_1235_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1230_ = v___x_1236_;
goto v___jp_1229_;
}
v___jp_1237_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1230_ = v___x_1238_;
goto v___jp_1229_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1224_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1224_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceIsAlpha___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1212_ = stack[0].m_obj;
lean_object* v_a_1213_ = stack[1].m_obj;
lean_object* v_a_1214_ = stack[2].m_obj;
lean_object* v_a_1215_ = stack[3].m_obj;
lean_object* v_a_1216_ = stack[4].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l_Char_reduceIsAlpha___redArg(v_e_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Char_reduceIsAlpha___redArg(v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_e_1265_);
return v_res_1271_;
}
}
lean_object* l_Char_reduceIsAlpha(lean_object* v_e_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Char_reduceIsAlpha___redArg(v_e_1272_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT void l_Char_reduceIsAlpha_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1272_ = stack[0].m_obj;
lean_object* v_a_1273_ = stack[1].m_obj;
lean_object* v_a_1274_ = stack[2].m_obj;
lean_object* v_a_1275_ = stack[3].m_obj;
lean_object* v_a_1276_ = stack[4].m_obj;
lean_object* v_a_1277_ = stack[5].m_obj;
lean_object* v_a_1278_ = stack[6].m_obj;
lean_object* v_a_1279_ = stack[7].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l_Char_reduceIsAlpha(v_e_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object* v_e_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Char_reduceIsAlpha(v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_e_1283_);
return v_res_1292_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1309_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1310_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1307_, v___x_1308_, v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1311_;
v_res_1311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1311_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20____boxed(lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_();
return v_res_1313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1318_ = 1;
v___x_1319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_);
v___x_1320_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1317_, v___x_1318_, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1321_;
v_res_1321_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22____boxed(lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_();
return v_res_1323_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1326_ = 1;
v___x_1327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_);
v___x_1328_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1325_, v___x_1326_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1329_;
v_res_1329_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24____boxed(lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_();
return v_res_1331_;
}
}
lean_object* l_Char_reduceIsDigit___redArg(lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = ((lean_object*)(l_Char_reduceIsDigit___redArg___closed__1));
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = l_Lean_Expr_isAppOfArity(v_e_1336_, v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = l_Lean_Expr_appArg_x21(v_e_1336_);
v___x_1348_ = l_Lean_Meta_getCharValue_x3f(v___x_1347_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1371_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1371_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1371_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___y_1354_; 
if (lean_obj_tag(v_a_1349_) == 1)
{
lean_object* v_val_1361_; uint32_t v___x_1362_; uint32_t v___x_1363_; uint8_t v___x_1364_; 
v_val_1361_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v_a_1349_, 1);
v___x_1362_ = 48;
v___x_1363_ = lean_unbox_uint32(v_val_1361_);
v___x_1364_ = lean_uint32_dec_le(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec(v_val_1361_);
goto v___jp_1359_;
}
else
{
uint32_t v___x_1365_; uint32_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = 57;
v___x_1366_ = lean_unbox_uint32(v_val_1361_);
lean_dec(v_val_1361_);
v___x_1367_ = lean_uint32_dec_le(v___x_1366_, v___x_1365_);
if (v___x_1367_ == 0)
{
goto v___jp_1359_;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1354_ = v___x_1368_;
goto v___jp_1353_;
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_del_object(v___x_1351_);
lean_dec(v_a_1349_);
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
v___jp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_inc_ref(v___y_1354_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1354_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1355_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
v___jp_1359_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1354_ = v___x_1360_;
goto v___jp_1353_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1348_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1348_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceIsDigit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1336_ = stack[0].m_obj;
lean_object* v_a_1337_ = stack[1].m_obj;
lean_object* v_a_1338_ = stack[2].m_obj;
lean_object* v_a_1339_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[4].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l_Char_reduceIsDigit___redArg(v_e_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Char_reduceIsDigit___redArg(v_e_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec_ref(v_e_1381_);
return v_res_1387_;
}
}
lean_object* l_Char_reduceIsDigit(lean_object* v_e_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Char_reduceIsDigit___redArg(v_e_1388_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT void l_Char_reduceIsDigit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1388_ = stack[0].m_obj;
lean_object* v_a_1389_ = stack[1].m_obj;
lean_object* v_a_1390_ = stack[2].m_obj;
lean_object* v_a_1391_ = stack[3].m_obj;
lean_object* v_a_1392_ = stack[4].m_obj;
lean_object* v_a_1393_ = stack[5].m_obj;
lean_object* v_a_1394_ = stack[6].m_obj;
lean_object* v_a_1395_ = stack[7].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l_Char_reduceIsDigit(v_e_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Char_reduceIsDigit(v_e_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_e_1399_);
return v_res_1408_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1425_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1426_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1423_, v___x_1424_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1427_;
v_res_1427_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20____boxed(lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_();
return v_res_1429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1434_ = 1;
v___x_1435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_);
v___x_1436_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1433_, v___x_1434_, v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1437_;
v_res_1437_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22____boxed(lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_();
return v_res_1439_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1442_ = 1;
v___x_1443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_);
v___x_1444_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1441_, v___x_1442_, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1445_;
v_res_1445_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24____boxed(lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_();
return v_res_1447_;
}
}
lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object* v_e_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = ((lean_object*)(l_Char_reduceIsAlphaNum___redArg___closed__1));
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = l_Lean_Expr_isAppOfArity(v_e_1452_, v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = l_Lean_Expr_appArg_x21(v_e_1452_);
v___x_1464_ = l_Lean_Meta_getCharValue_x3f(v___x_1463_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1502_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1502_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1502_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___y_1470_; 
if (lean_obj_tag(v_a_1465_) == 1)
{
lean_object* v_val_1479_; uint32_t v___x_1494_; uint32_t v___x_1495_; uint8_t v___x_1496_; 
v_val_1479_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v_a_1465_, 1);
v___x_1494_ = 65;
v___x_1495_ = lean_unbox_uint32(v_val_1479_);
v___x_1496_ = lean_uint32_dec_le(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
goto v___jp_1487_;
}
else
{
uint32_t v___x_1497_; uint32_t v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = 90;
v___x_1498_ = lean_unbox_uint32(v_val_1479_);
v___x_1499_ = lean_uint32_dec_le(v___x_1498_, v___x_1497_);
if (v___x_1499_ == 0)
{
goto v___jp_1487_;
}
else
{
lean_dec(v_val_1479_);
goto v___jp_1477_;
}
}
v___jp_1480_:
{
uint32_t v___x_1481_; uint32_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = 48;
v___x_1482_ = lean_unbox_uint32(v_val_1479_);
v___x_1483_ = lean_uint32_dec_le(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_dec(v_val_1479_);
goto v___jp_1475_;
}
else
{
uint32_t v___x_1484_; uint32_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = 57;
v___x_1485_ = lean_unbox_uint32(v_val_1479_);
lean_dec(v_val_1479_);
v___x_1486_ = lean_uint32_dec_le(v___x_1485_, v___x_1484_);
if (v___x_1486_ == 0)
{
goto v___jp_1475_;
}
else
{
goto v___jp_1477_;
}
}
}
v___jp_1487_:
{
uint32_t v___x_1488_; uint32_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = 97;
v___x_1489_ = lean_unbox_uint32(v_val_1479_);
v___x_1490_ = lean_uint32_dec_le(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
goto v___jp_1480_;
}
else
{
uint32_t v___x_1491_; uint32_t v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = 122;
v___x_1492_ = lean_unbox_uint32(v_val_1479_);
v___x_1493_ = lean_uint32_dec_le(v___x_1492_, v___x_1491_);
if (v___x_1493_ == 0)
{
goto v___jp_1480_;
}
else
{
lean_dec(v_val_1479_);
goto v___jp_1477_;
}
}
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_del_object(v___x_1467_);
lean_dec(v_a_1465_);
v___x_1500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
v___jp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1470_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1470_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1471_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
v___jp_1475_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1470_ = v___x_1476_;
goto v___jp_1469_;
}
v___jp_1477_:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1470_ = v___x_1478_;
goto v___jp_1469_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1464_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1464_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceIsAlphaNum___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1452_ = stack[0].m_obj;
lean_object* v_a_1453_ = stack[1].m_obj;
lean_object* v_a_1454_ = stack[2].m_obj;
lean_object* v_a_1455_ = stack[3].m_obj;
lean_object* v_a_1456_ = stack[4].m_obj;
lean_object* v_res_1511_;
v_res_1511_ = l_Char_reduceIsAlphaNum___redArg(v_e_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
stack->m_obj
 = v_res_1511_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object* v_e_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Char_reduceIsAlphaNum___redArg(v_e_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec_ref(v_e_1512_);
return v_res_1518_;
}
}
lean_object* l_Char_reduceIsAlphaNum(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Char_reduceIsAlphaNum___redArg(v_e_1519_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT void l_Char_reduceIsAlphaNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1519_ = stack[0].m_obj;
lean_object* v_a_1520_ = stack[1].m_obj;
lean_object* v_a_1521_ = stack[2].m_obj;
lean_object* v_a_1522_ = stack[3].m_obj;
lean_object* v_a_1523_ = stack[4].m_obj;
lean_object* v_a_1524_ = stack[5].m_obj;
lean_object* v_a_1525_ = stack[6].m_obj;
lean_object* v_a_1526_ = stack[7].m_obj;
lean_object* v_res_1529_;
v_res_1529_ = l_Char_reduceIsAlphaNum(v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
stack->m_obj
 = v_res_1529_;
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object* v_e_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Char_reduceIsAlphaNum(v_e_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_e_1530_);
return v_res_1539_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1556_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1557_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1554_, v___x_1555_, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1558_;
v_res_1558_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20____boxed(lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_();
return v_res_1560_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1565_ = 1;
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_);
v___x_1567_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1564_, v___x_1565_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1568_;
v_res_1568_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1568_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22____boxed(lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_();
return v_res_1570_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1573_ = 1;
v___x_1574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_);
v___x_1575_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1572_, v___x_1573_, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1576_;
v_res_1576_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1576_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24____boxed(lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_();
return v_res_1578_;
}
}
lean_object* l_Char_reduceToString___redArg(lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__2));
v___x_1592_ = lean_unsigned_to_nat(3u);
v___x_1593_ = l_Lean_Expr_isAppOfArity(v_e_1585_, v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Lean_Expr_appArg_x21(v_e_1585_);
v___x_1597_ = l_Lean_Meta_getCharValue_x3f(v___x_1596_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1621_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1621_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1621_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
if (lean_obj_tag(v_a_1598_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1616_; 
v_val_1602_ = lean_ctor_get(v_a_1598_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_a_1598_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1604_ = v_a_1598_;
v_isShared_1605_ = v_isSharedCheck_1616_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_val_1602_);
lean_dec(v_a_1598_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1616_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; uint32_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1606_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__3));
v___x_1607_ = lean_unbox_uint32(v_val_1602_);
lean_dec(v_val_1602_);
v___x_1608_ = lean_string_push(v___x_1606_, v___x_1607_);
v___x_1609_ = l_Lean_mkStrLit(v___x_1608_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1609_);
v___x_1611_ = v___x_1604_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1611_);
v___x_1613_ = v___x_1600_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v_a_1598_);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1617_);
v___x_1619_ = v___x_1600_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1597_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1597_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceToString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1585_ = stack[0].m_obj;
lean_object* v_a_1586_ = stack[1].m_obj;
lean_object* v_a_1587_ = stack[2].m_obj;
lean_object* v_a_1588_ = stack[3].m_obj;
lean_object* v_a_1589_ = stack[4].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Char_reduceToString___redArg(v_e_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object* v_e_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Char_reduceToString___redArg(v_e_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_e_1631_);
return v_res_1637_;
}
}
lean_object* l_Char_reduceToString(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Char_reduceToString___redArg(v_e_1638_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT void l_Char_reduceToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1638_ = stack[0].m_obj;
lean_object* v_a_1639_ = stack[1].m_obj;
lean_object* v_a_1640_ = stack[2].m_obj;
lean_object* v_a_1641_ = stack[3].m_obj;
lean_object* v_a_1642_ = stack[4].m_obj;
lean_object* v_a_1643_ = stack[5].m_obj;
lean_object* v_a_1644_ = stack[6].m_obj;
lean_object* v_a_1645_ = stack[7].m_obj;
lean_object* v_res_1648_;
v_res_1648_ = l_Char_reduceToString(v_e_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object* v_e_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Char_reduceToString(v_e_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_e_1649_);
return v_res_1658_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1683_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1684_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1681_, v___x_1682_, v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1685_;
v_res_1685_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_();
stack->m_obj
 = v_res_1685_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23____boxed(lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_();
return v_res_1687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1692_ = 1;
v___x_1693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_);
v___x_1694_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1691_, v___x_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1695_;
v_res_1695_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_();
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25____boxed(lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_();
return v_res_1697_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1700_ = 1;
v___x_1701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_);
v___x_1702_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1699_, v___x_1700_, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1703_;
v_res_1703_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_();
stack->m_obj
 = v_res_1703_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27____boxed(lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_();
return v_res_1705_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__4(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = l_Lean_Level_ofNat(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__5(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__4, &l_Char_reduceVal___redArg___closed__4_once, _init_l_Char_reduceVal___redArg___closed__4);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___x_1716_);
return v___x_1718_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__6(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__5, &l_Char_reduceVal___redArg___closed__5_once, _init_l_Char_reduceVal___redArg___closed__5);
v___x_1720_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__3));
v___x_1721_ = l_Lean_Expr_const___override(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__9(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__8));
v___x_1727_ = l_Lean_mkConst(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__12(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__11));
v___x_1734_ = l_Lean_Expr_const___override(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
lean_object* l_Char_reduceVal___redArg(lean_object* v_e_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1735_, v_a_1737_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = l_Lean_Expr_cleanupAnnotations(v_a_1745_);
v___x_1747_ = l_Lean_Expr_isApp(v___x_1746_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v___x_1746_);
goto v___jp_1741_;
}
else
{
lean_object* v_arg_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_arg_1748_ = lean_ctor_get(v___x_1746_, 1);
lean_inc_ref(v_arg_1748_);
v___x_1749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1746_);
v___x_1750_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__1));
v___x_1751_ = l_Lean_Expr_isConstOf(v___x_1749_, v___x_1750_);
lean_dec_ref(v___x_1749_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v_arg_1748_);
goto v___jp_1741_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Meta_getCharValue_x3f(v_arg_1748_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1780_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1780_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1780_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1775_; 
v_val_1757_ = lean_ctor_get(v_a_1753_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_a_1753_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1759_ = v_a_1753_;
v_isShared_1760_ = v_isSharedCheck_1775_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v_a_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1775_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint32_t v___x_1761_; lean_object* v___x_1762_; lean_object* v_r_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1761_ = lean_unbox_uint32(v_val_1757_);
lean_dec(v_val_1757_);
v___x_1762_ = lean_uint32_to_nat(v___x_1761_);
v_r_1763_ = l_Lean_mkRawNatLit(v___x_1762_);
v___x_1764_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__6, &l_Char_reduceVal___redArg___closed__6_once, _init_l_Char_reduceVal___redArg___closed__6);
v___x_1765_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__9, &l_Char_reduceVal___redArg___closed__9_once, _init_l_Char_reduceVal___redArg___closed__9);
v___x_1766_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__12, &l_Char_reduceVal___redArg___closed__12_once, _init_l_Char_reduceVal___redArg___closed__12);
lean_inc_ref(v_r_1763_);
v___x_1767_ = l_Lean_Expr_app___override(v___x_1766_, v_r_1763_);
v___x_1768_ = l_Lean_mkApp3(v___x_1764_, v___x_1765_, v_r_1763_, v___x_1767_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1768_);
v___x_1770_ = v___x_1759_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1770_);
v___x_1772_ = v___x_1755_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_dec(v_a_1753_);
v___x_1776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1776_);
v___x_1778_ = v___x_1755_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1752_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1752_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1744_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1744_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
v___jp_1741_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
}
LEAN_EXPORT void l_Char_reduceVal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1735_ = stack[0].m_obj;
lean_object* v_a_1736_ = stack[1].m_obj;
lean_object* v_a_1737_ = stack[2].m_obj;
lean_object* v_a_1738_ = stack[3].m_obj;
lean_object* v_a_1739_ = stack[4].m_obj;
lean_object* v_res_1797_;
v_res_1797_ = l_Char_reduceVal___redArg(v_e_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
stack->m_obj
 = v_res_1797_;
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object* v_e_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Char_reduceVal___redArg(v_e_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
return v_res_1804_;
}
}
lean_object* l_Char_reduceVal(lean_object* v_e_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Char_reduceVal___redArg(v_e_1805_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT void l_Char_reduceVal_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1805_ = stack[0].m_obj;
lean_object* v_a_1806_ = stack[1].m_obj;
lean_object* v_a_1807_ = stack[2].m_obj;
lean_object* v_a_1808_ = stack[3].m_obj;
lean_object* v_a_1809_ = stack[4].m_obj;
lean_object* v_a_1810_ = stack[5].m_obj;
lean_object* v_a_1811_ = stack[6].m_obj;
lean_object* v_a_1812_ = stack[7].m_obj;
lean_object* v_res_1815_;
v_res_1815_ = l_Char_reduceVal(v_e_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
stack->m_obj
 = v_res_1815_;
}
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object* v_e_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Char_reduceVal(v_e_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
return v_res_1825_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1842_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1843_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1840_, v___x_1841_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1844_;
v_res_1844_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_();
stack->m_obj
 = v_res_1844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20____boxed(lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_();
return v_res_1846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1851_ = 1;
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_);
v___x_1853_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1850_, v___x_1851_, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1854_;
v_res_1854_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_();
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22____boxed(lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_();
return v_res_1856_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1859_ = 1;
v___x_1860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_);
v___x_1861_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1858_, v___x_1859_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1862_;
v_res_1862_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_();
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24____boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_();
return v_res_1864_;
}
}
lean_object* l_Char_reduceLT___redArg(lean_object* v_e_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1876_ = ((lean_object*)(l_Char_reduceLT___redArg___closed__2));
v___x_1877_ = lean_unsigned_to_nat(4u);
v___x_1878_ = l_Lean_Expr_isAppOfArity(v_e_1870_, v___x_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v_e_1870_);
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_Expr_appFn_x21(v_e_1870_);
v___x_1882_ = l_Lean_Expr_appArg_x21(v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = l_Lean_Meta_getCharValue_x3f(v___x_1882_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1917_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1917_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1917_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_object* v_val_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_del_object(v___x_1886_);
v_val_1888_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v_a_1884_, 1);
v___x_1889_ = l_Lean_Expr_appArg_x21(v_e_1870_);
v___x_1890_ = l_Lean_Meta_getCharValue_x3f(v___x_1889_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1904_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1904_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1904_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
if (lean_obj_tag(v_a_1891_) == 1)
{
lean_object* v_val_1895_; uint32_t v___x_1896_; uint32_t v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; 
lean_del_object(v___x_1893_);
v_val_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v_a_1891_, 1);
v___x_1896_ = lean_unbox_uint32(v_val_1888_);
lean_dec(v_val_1888_);
v___x_1897_ = lean_unbox_uint32(v_val_1895_);
lean_dec(v_val_1895_);
v___x_1898_ = lean_uint32_dec_lt(v___x_1896_, v___x_1897_);
v___x_1899_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1870_, v___x_1898_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
lean_dec(v_a_1891_);
lean_dec(v_val_1888_);
lean_dec_ref(v_e_1870_);
v___x_1900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1900_);
v___x_1902_ = v___x_1893_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_val_1888_);
lean_dec_ref(v_e_1870_);
v_a_1905_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1890_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1890_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_a_1884_);
lean_dec_ref(v_e_1870_);
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1913_);
v___x_1915_ = v___x_1886_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_e_1870_);
v_a_1918_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1883_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1883_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1870_ = stack[0].m_obj;
lean_object* v_a_1871_ = stack[1].m_obj;
lean_object* v_a_1872_ = stack[2].m_obj;
lean_object* v_a_1873_ = stack[3].m_obj;
lean_object* v_a_1874_ = stack[4].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l_Char_reduceLT___redArg(v_e_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg___boxed(lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Char_reduceLT___redArg(v_e_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1933_;
}
}
lean_object* l_Char_reduceLT(lean_object* v_e_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Char_reduceLT___redArg(v_e_1934_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT void l_Char_reduceLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1934_ = stack[0].m_obj;
lean_object* v_a_1935_ = stack[1].m_obj;
lean_object* v_a_1936_ = stack[2].m_obj;
lean_object* v_a_1937_ = stack[3].m_obj;
lean_object* v_a_1938_ = stack[4].m_obj;
lean_object* v_a_1939_ = stack[5].m_obj;
lean_object* v_a_1940_ = stack[6].m_obj;
lean_object* v_a_1941_ = stack[7].m_obj;
lean_object* v_res_1944_;
v_res_1944_ = l_Char_reduceLT(v_e_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
stack->m_obj
 = v_res_1944_;
}
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object* v_e_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Char_reduceLT(v_e_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
return v_res_1954_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1975_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1976_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1973_, v___x_1974_, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1977_;
v_res_1977_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_();
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27____boxed(lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_();
return v_res_1979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1984_ = 1;
v___x_1985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_);
v___x_1986_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1983_, v___x_1984_, v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1987_;
v_res_1987_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_();
stack->m_obj
 = v_res_1987_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29____boxed(lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_();
return v_res_1989_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1992_ = 1;
v___x_1993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_);
v___x_1994_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1991_, v___x_1992_, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1995_;
v_res_1995_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_();
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31____boxed(lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_();
return v_res_1997_;
}
}
lean_object* l_Char_reduceLE___redArg(lean_object* v_e_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = ((lean_object*)(l_Char_reduceLE___redArg___closed__2));
v___x_2010_ = lean_unsigned_to_nat(4u);
v___x_2011_ = l_Lean_Expr_isAppOfArity(v_e_2003_, v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v_e_2003_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = l_Lean_Expr_appFn_x21(v_e_2003_);
v___x_2015_ = l_Lean_Expr_appArg_x21(v___x_2014_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = l_Lean_Meta_getCharValue_x3f(v___x_2015_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2050_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
if (lean_obj_tag(v_a_2017_) == 1)
{
lean_object* v_val_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_del_object(v___x_2019_);
v_val_2021_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v_a_2017_, 1);
v___x_2022_ = l_Lean_Expr_appArg_x21(v_e_2003_);
v___x_2023_ = l_Lean_Meta_getCharValue_x3f(v___x_2022_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2037_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2037_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2037_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
if (lean_obj_tag(v_a_2024_) == 1)
{
lean_object* v_val_2028_; uint32_t v___x_2029_; uint32_t v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; 
lean_del_object(v___x_2026_);
v_val_2028_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_val_2028_);
lean_dec_ref_known(v_a_2024_, 1);
v___x_2029_ = lean_unbox_uint32(v_val_2021_);
lean_dec(v_val_2021_);
v___x_2030_ = lean_unbox_uint32(v_val_2028_);
lean_dec(v_val_2028_);
v___x_2031_ = lean_uint32_dec_le(v___x_2029_, v___x_2030_);
v___x_2032_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2003_, v___x_2031_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec(v_a_2024_);
lean_dec(v_val_2021_);
lean_dec_ref(v_e_2003_);
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2033_);
v___x_2035_ = v___x_2026_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_val_2021_);
lean_dec_ref(v_e_2003_);
v_a_2038_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2023_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2023_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v_a_2017_);
lean_dec_ref(v_e_2003_);
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2046_);
v___x_2048_ = v___x_2019_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_e_2003_);
v_a_2051_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2016_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2016_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2003_ = stack[0].m_obj;
lean_object* v_a_2004_ = stack[1].m_obj;
lean_object* v_a_2005_ = stack[2].m_obj;
lean_object* v_a_2006_ = stack[3].m_obj;
lean_object* v_a_2007_ = stack[4].m_obj;
lean_object* v_res_2059_;
v_res_2059_ = l_Char_reduceLE___redArg(v_e_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg___boxed(lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Char_reduceLE___redArg(v_e_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2066_;
}
}
lean_object* l_Char_reduceLE(lean_object* v_e_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Char_reduceLE___redArg(v_e_2067_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT void l_Char_reduceLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2067_ = stack[0].m_obj;
lean_object* v_a_2068_ = stack[1].m_obj;
lean_object* v_a_2069_ = stack[2].m_obj;
lean_object* v_a_2070_ = stack[3].m_obj;
lean_object* v_a_2071_ = stack[4].m_obj;
lean_object* v_a_2072_ = stack[5].m_obj;
lean_object* v_a_2073_ = stack[6].m_obj;
lean_object* v_a_2074_ = stack[7].m_obj;
lean_object* v_res_2077_;
v_res_2077_ = l_Char_reduceLE(v_e_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
stack->m_obj
 = v_res_2077_;
}
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object* v_e_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Char_reduceLE(v_e_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
return v_res_2087_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2108_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2109_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2106_, v___x_2107_, v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2110_;
v_res_2110_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27____boxed(lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_();
return v_res_2112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2117_ = 1;
v___x_2118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_);
v___x_2119_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2116_, v___x_2117_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2120_;
v_res_2120_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29____boxed(lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_();
return v_res_2122_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2125_ = 1;
v___x_2126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_);
v___x_2127_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2124_, v___x_2125_, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2128_;
v_res_2128_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31____boxed(lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_();
return v_res_2130_;
}
}
lean_object* l_Char_reduceGT___redArg(lean_object* v_e_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = ((lean_object*)(l_Char_reduceGT___redArg___closed__2));
v___x_2143_ = lean_unsigned_to_nat(4u);
v___x_2144_ = l_Lean_Expr_isAppOfArity(v_e_2136_, v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v_e_2136_);
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = l_Lean_Expr_appFn_x21(v_e_2136_);
v___x_2148_ = l_Lean_Expr_appArg_x21(v___x_2147_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = l_Lean_Meta_getCharValue_x3f(v___x_2148_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2183_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2183_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2183_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_val_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_del_object(v___x_2152_);
v_val_2154_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v_a_2150_, 1);
v___x_2155_ = l_Lean_Expr_appArg_x21(v_e_2136_);
v___x_2156_ = l_Lean_Meta_getCharValue_x3f(v___x_2155_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2170_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2170_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
if (lean_obj_tag(v_a_2157_) == 1)
{
lean_object* v_val_2161_; uint32_t v___x_2162_; uint32_t v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
lean_del_object(v___x_2159_);
v_val_2161_ = lean_ctor_get(v_a_2157_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v_a_2157_, 1);
v___x_2162_ = lean_unbox_uint32(v_val_2161_);
lean_dec(v_val_2161_);
v___x_2163_ = lean_unbox_uint32(v_val_2154_);
lean_dec(v_val_2154_);
v___x_2164_ = lean_uint32_dec_lt(v___x_2162_, v___x_2163_);
v___x_2165_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2136_, v___x_2164_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_dec(v_a_2157_);
lean_dec(v_val_2154_);
lean_dec_ref(v_e_2136_);
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2166_);
v___x_2168_ = v___x_2159_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_val_2154_);
lean_dec_ref(v_e_2136_);
v_a_2171_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2156_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2156_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
lean_dec(v_a_2150_);
lean_dec_ref(v_e_2136_);
v___x_2179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2179_);
v___x_2181_ = v___x_2152_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_e_2136_);
v_a_2184_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2149_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2149_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
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
}
}
LEAN_EXPORT void l_Char_reduceGT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2136_ = stack[0].m_obj;
lean_object* v_a_2137_ = stack[1].m_obj;
lean_object* v_a_2138_ = stack[2].m_obj;
lean_object* v_a_2139_ = stack[3].m_obj;
lean_object* v_a_2140_ = stack[4].m_obj;
lean_object* v_res_2192_;
v_res_2192_ = l_Char_reduceGT___redArg(v_e_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
stack->m_obj
 = v_res_2192_;
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg___boxed(lean_object* v_e_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Char_reduceGT___redArg(v_e_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
return v_res_2199_;
}
}
lean_object* l_Char_reduceGT(lean_object* v_e_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Char_reduceGT___redArg(v_e_2200_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT void l_Char_reduceGT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2200_ = stack[0].m_obj;
lean_object* v_a_2201_ = stack[1].m_obj;
lean_object* v_a_2202_ = stack[2].m_obj;
lean_object* v_a_2203_ = stack[3].m_obj;
lean_object* v_a_2204_ = stack[4].m_obj;
lean_object* v_a_2205_ = stack[5].m_obj;
lean_object* v_a_2206_ = stack[6].m_obj;
lean_object* v_a_2207_ = stack[7].m_obj;
lean_object* v_res_2210_;
v_res_2210_ = l_Char_reduceGT(v_e_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
stack->m_obj
 = v_res_2210_;
}
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object* v_e_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Char_reduceGT(v_e_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
return v_res_2220_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_2228_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2229_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2226_, v___x_2227_, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2230_;
v_res_2230_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2230_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27____boxed(lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_();
return v_res_2232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2237_ = 1;
v___x_2238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_);
v___x_2239_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2236_, v___x_2237_, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2240_;
v_res_2240_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29____boxed(lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_();
return v_res_2242_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2245_ = 1;
v___x_2246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_);
v___x_2247_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2244_, v___x_2245_, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2248_;
v_res_2248_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2248_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31____boxed(lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_();
return v_res_2250_;
}
}
lean_object* l_Char_reduceGE___redArg(lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = ((lean_object*)(l_Char_reduceGE___redArg___closed__2));
v___x_2263_ = lean_unsigned_to_nat(4u);
v___x_2264_ = l_Lean_Expr_isAppOfArity(v_e_2256_, v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec_ref(v_e_2256_);
v___x_2265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = l_Lean_Expr_appFn_x21(v_e_2256_);
v___x_2268_ = l_Lean_Expr_appArg_x21(v___x_2267_);
lean_dec_ref(v___x_2267_);
v___x_2269_ = l_Lean_Meta_getCharValue_x3f(v___x_2268_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2303_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2303_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2303_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
if (lean_obj_tag(v_a_2270_) == 1)
{
lean_object* v_val_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_del_object(v___x_2272_);
v_val_2274_ = lean_ctor_get(v_a_2270_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v_a_2270_, 1);
v___x_2275_ = l_Lean_Expr_appArg_x21(v_e_2256_);
v___x_2276_ = l_Lean_Meta_getCharValue_x3f(v___x_2275_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2290_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
if (lean_obj_tag(v_a_2277_) == 1)
{
lean_object* v_val_2281_; uint32_t v___x_2282_; uint32_t v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
lean_del_object(v___x_2279_);
v_val_2281_ = lean_ctor_get(v_a_2277_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v_a_2277_, 1);
v___x_2282_ = lean_unbox_uint32(v_val_2281_);
lean_dec(v_val_2281_);
v___x_2283_ = lean_unbox_uint32(v_val_2274_);
lean_dec(v_val_2274_);
v___x_2284_ = lean_uint32_dec_le(v___x_2282_, v___x_2283_);
v___x_2285_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2256_, v___x_2284_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_dec(v_a_2277_);
lean_dec(v_val_2274_);
lean_dec_ref(v_e_2256_);
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2286_);
v___x_2288_ = v___x_2279_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_val_2274_);
lean_dec_ref(v_e_2256_);
v_a_2291_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2276_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2276_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
lean_dec(v_a_2270_);
lean_dec_ref(v_e_2256_);
v___x_2299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2299_);
v___x_2301_ = v___x_2272_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_e_2256_);
v_a_2304_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2269_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2269_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceGE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2256_ = stack[0].m_obj;
lean_object* v_a_2257_ = stack[1].m_obj;
lean_object* v_a_2258_ = stack[2].m_obj;
lean_object* v_a_2259_ = stack[3].m_obj;
lean_object* v_a_2260_ = stack[4].m_obj;
lean_object* v_res_2312_;
v_res_2312_ = l_Char_reduceGE___redArg(v_e_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
stack->m_obj
 = v_res_2312_;
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg___boxed(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Char_reduceGE___redArg(v_e_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2319_;
}
}
lean_object* l_Char_reduceGE(lean_object* v_e_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Char_reduceGE___redArg(v_e_2320_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT void l_Char_reduceGE_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2320_ = stack[0].m_obj;
lean_object* v_a_2321_ = stack[1].m_obj;
lean_object* v_a_2322_ = stack[2].m_obj;
lean_object* v_a_2323_ = stack[3].m_obj;
lean_object* v_a_2324_ = stack[4].m_obj;
lean_object* v_a_2325_ = stack[5].m_obj;
lean_object* v_a_2326_ = stack[6].m_obj;
lean_object* v_a_2327_ = stack[7].m_obj;
lean_object* v_res_2330_;
v_res_2330_ = l_Char_reduceGE(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
stack->m_obj
 = v_res_2330_;
}
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Char_reduceGE(v_e_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
return v_res_2340_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2348_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2349_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2346_, v___x_2347_, v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2350_;
v_res_2350_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2350_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27____boxed(lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_();
return v_res_2352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2357_ = 1;
v___x_2358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_);
v___x_2359_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2356_, v___x_2357_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2360_;
v_res_2360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29____boxed(lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_();
return v_res_2362_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2365_ = 1;
v___x_2366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_);
v___x_2367_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2364_, v___x_2365_, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2368_;
v_res_2368_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2368_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31____boxed(lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_();
return v_res_2370_;
}
}
lean_object* l_Char_reduceEq___redArg(lean_object* v_e_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2380_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_2381_ = lean_unsigned_to_nat(3u);
v___x_2382_ = l_Lean_Expr_isAppOfArity(v_e_2374_, v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec_ref(v_e_2374_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
return v___x_2384_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = l_Lean_Expr_appFn_x21(v_e_2374_);
v___x_2386_ = l_Lean_Expr_appArg_x21(v___x_2385_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = l_Lean_Meta_getCharValue_x3f(v___x_2386_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2421_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2421_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2421_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
if (lean_obj_tag(v_a_2388_) == 1)
{
lean_object* v_val_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_del_object(v___x_2390_);
v_val_2392_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v_a_2388_, 1);
v___x_2393_ = l_Lean_Expr_appArg_x21(v_e_2374_);
v___x_2394_ = l_Lean_Meta_getCharValue_x3f(v___x_2393_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2408_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2408_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2408_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
if (lean_obj_tag(v_a_2395_) == 1)
{
lean_object* v_val_2399_; uint32_t v___x_2400_; uint32_t v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
lean_del_object(v___x_2397_);
v_val_2399_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_val_2399_);
lean_dec_ref_known(v_a_2395_, 1);
v___x_2400_ = lean_unbox_uint32(v_val_2392_);
lean_dec(v_val_2392_);
v___x_2401_ = lean_unbox_uint32(v_val_2399_);
lean_dec(v_val_2399_);
v___x_2402_ = lean_uint32_dec_eq(v___x_2400_, v___x_2401_);
v___x_2403_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2374_, v___x_2402_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_dec(v_a_2395_);
lean_dec(v_val_2392_);
lean_dec_ref(v_e_2374_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2404_);
v___x_2406_ = v___x_2397_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_val_2392_);
lean_dec_ref(v_e_2374_);
v_a_2409_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2394_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2394_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_dec(v_a_2388_);
lean_dec_ref(v_e_2374_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2417_);
v___x_2419_ = v___x_2390_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v_e_2374_);
v_a_2422_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2387_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2387_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2374_ = stack[0].m_obj;
lean_object* v_a_2375_ = stack[1].m_obj;
lean_object* v_a_2376_ = stack[2].m_obj;
lean_object* v_a_2377_ = stack[3].m_obj;
lean_object* v_a_2378_ = stack[4].m_obj;
lean_object* v_res_2430_;
v_res_2430_ = l_Char_reduceEq___redArg(v_e_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
stack->m_obj
 = v_res_2430_;
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg___boxed(lean_object* v_e_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Char_reduceEq___redArg(v_e_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
lean_object* l_Char_reduceEq(lean_object* v_e_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Char_reduceEq___redArg(v_e_2438_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT void l_Char_reduceEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2438_ = stack[0].m_obj;
lean_object* v_a_2439_ = stack[1].m_obj;
lean_object* v_a_2440_ = stack[2].m_obj;
lean_object* v_a_2441_ = stack[3].m_obj;
lean_object* v_a_2442_ = stack[4].m_obj;
lean_object* v_a_2443_ = stack[5].m_obj;
lean_object* v_a_2444_ = stack[6].m_obj;
lean_object* v_a_2445_ = stack[7].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Char_reduceEq(v_e_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object* v_e_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Char_reduceEq(v_e_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
return v_res_2458_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2478_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2479_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2476_, v___x_2477_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2480_;
v_res_2480_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27____boxed(lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_();
return v_res_2482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2486_; uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2487_ = 1;
v___x_2488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_);
v___x_2489_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2486_, v___x_2487_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2490_;
v_res_2490_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2490_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29____boxed(lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_();
return v_res_2492_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2495_ = 1;
v___x_2496_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_);
v___x_2497_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2494_, v___x_2495_, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2498_;
v_res_2498_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31____boxed(lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_();
return v_res_2500_;
}
}
lean_object* l_Char_reduceNe___redArg(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2510_ = ((lean_object*)(l_Char_reduceNe___redArg___closed__1));
v___x_2511_ = lean_unsigned_to_nat(3u);
v___x_2512_ = l_Lean_Expr_isAppOfArity(v_e_2504_, v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref(v_e_2504_);
v___x_2513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = l_Lean_Expr_appFn_x21(v_e_2504_);
v___x_2516_ = l_Lean_Expr_appArg_x21(v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l_Lean_Meta_getCharValue_x3f(v___x_2516_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2553_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
if (lean_obj_tag(v_a_2518_) == 1)
{
lean_object* v_val_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_del_object(v___x_2520_);
v_val_2522_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v_a_2518_, 1);
v___x_2523_ = l_Lean_Expr_appArg_x21(v_e_2504_);
v___x_2524_ = l_Lean_Meta_getCharValue_x3f(v___x_2523_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2540_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2540_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2540_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
if (lean_obj_tag(v_a_2525_) == 1)
{
lean_object* v_val_2529_; uint32_t v___x_2530_; uint32_t v___x_2531_; uint8_t v___x_2532_; 
lean_del_object(v___x_2527_);
v_val_2529_ = lean_ctor_get(v_a_2525_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v_a_2525_, 1);
v___x_2530_ = lean_unbox_uint32(v_val_2522_);
lean_dec(v_val_2522_);
v___x_2531_ = lean_unbox_uint32(v_val_2529_);
lean_dec(v_val_2529_);
v___x_2532_ = lean_uint32_dec_eq(v___x_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2504_, v___x_2512_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2533_;
}
else
{
uint8_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = 0;
v___x_2535_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2504_, v___x_2534_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_a_2525_);
lean_dec(v_val_2522_);
lean_dec_ref(v_e_2504_);
v___x_2536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2536_);
v___x_2538_ = v___x_2527_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_val_2522_);
lean_dec_ref(v_e_2504_);
v_a_2541_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2524_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2524_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_dec(v_a_2518_);
lean_dec_ref(v_e_2504_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2549_);
v___x_2551_ = v___x_2520_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_e_2504_);
v_a_2554_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2517_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2517_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceNe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2504_ = stack[0].m_obj;
lean_object* v_a_2505_ = stack[1].m_obj;
lean_object* v_a_2506_ = stack[2].m_obj;
lean_object* v_a_2507_ = stack[3].m_obj;
lean_object* v_a_2508_ = stack[4].m_obj;
lean_object* v_res_2562_;
v_res_2562_ = l_Char_reduceNe___redArg(v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg___boxed(lean_object* v_e_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Char_reduceNe___redArg(v_e_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2569_;
}
}
lean_object* l_Char_reduceNe(lean_object* v_e_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Char_reduceNe___redArg(v_e_2570_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT void l_Char_reduceNe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2570_ = stack[0].m_obj;
lean_object* v_a_2571_ = stack[1].m_obj;
lean_object* v_a_2572_ = stack[2].m_obj;
lean_object* v_a_2573_ = stack[3].m_obj;
lean_object* v_a_2574_ = stack[4].m_obj;
lean_object* v_a_2575_ = stack[5].m_obj;
lean_object* v_a_2576_ = stack[6].m_obj;
lean_object* v_a_2577_ = stack[7].m_obj;
lean_object* v_res_2580_;
v_res_2580_ = l_Char_reduceNe(v_e_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
stack->m_obj
 = v_res_2580_;
}
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Char_reduceNe(v_e_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
return v_res_2590_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2615_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2616_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2613_, v___x_2614_, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2617_;
v_res_2617_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27____boxed(lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_();
return v_res_2619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2624_ = 1;
v___x_2625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_);
v___x_2626_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2623_, v___x_2624_, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2627_;
v_res_2627_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29____boxed(lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_();
return v_res_2629_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2632_ = 1;
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_);
v___x_2634_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2631_, v___x_2632_, v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2635_;
v_res_2635_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2635_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31____boxed(lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_();
return v_res_2637_;
}
}
lean_object* l_Char_reduceBEq___redArg(lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Char_reduceBEq___redArg___closed__2));
v___x_2650_ = lean_unsigned_to_nat(4u);
v___x_2651_ = l_Lean_Expr_isAppOfArity(v_e_2643_, v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = l_Lean_Expr_appFn_x21(v_e_2643_);
v___x_2655_ = l_Lean_Expr_appArg_x21(v___x_2654_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = l_Lean_Meta_getCharValue_x3f(v___x_2655_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2703_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2703_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2703_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
if (lean_obj_tag(v_a_2657_) == 1)
{
lean_object* v_val_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2698_; 
v_val_2661_ = lean_ctor_get(v_a_2657_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2663_ = v_a_2657_;
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_val_2661_);
lean_dec(v_a_2657_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = l_Lean_Expr_appArg_x21(v_e_2643_);
v___x_2666_ = l_Lean_Meta_getCharValue_x3f(v___x_2665_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2689_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2689_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2689_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___y_2672_; 
if (lean_obj_tag(v_a_2667_) == 1)
{
lean_object* v_val_2679_; uint32_t v___x_2680_; uint32_t v___x_2681_; uint8_t v___x_2682_; 
lean_del_object(v___x_2659_);
v_val_2679_ = lean_ctor_get(v_a_2667_, 0);
lean_inc(v_val_2679_);
lean_dec_ref_known(v_a_2667_, 1);
v___x_2680_ = lean_unbox_uint32(v_val_2661_);
lean_dec(v_val_2661_);
v___x_2681_ = lean_unbox_uint32(v_val_2679_);
lean_dec(v_val_2679_);
v___x_2682_ = lean_uint32_dec_eq(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_2672_ = v___x_2683_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_2672_ = v___x_2684_;
goto v___jp_2671_;
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_del_object(v___x_2669_);
lean_dec(v_a_2667_);
lean_del_object(v___x_2663_);
lean_dec(v_val_2661_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2685_);
v___x_2687_ = v___x_2659_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
v___jp_2671_:
{
lean_object* v___x_2674_; 
lean_inc_ref(v___y_2672_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2672_);
v___x_2674_ = v___x_2663_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___y_2672_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2674_);
v___x_2676_ = v___x_2669_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2663_);
lean_dec(v_val_2661_);
lean_del_object(v___x_2659_);
v_a_2690_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2666_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2666_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_a_2657_);
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2699_);
v___x_2701_ = v___x_2659_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2656_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2656_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2643_ = stack[0].m_obj;
lean_object* v_a_2644_ = stack[1].m_obj;
lean_object* v_a_2645_ = stack[2].m_obj;
lean_object* v_a_2646_ = stack[3].m_obj;
lean_object* v_a_2647_ = stack[4].m_obj;
lean_object* v_res_2712_;
v_res_2712_ = l_Char_reduceBEq___redArg(v_e_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
stack->m_obj
 = v_res_2712_;
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object* v_e_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Char_reduceBEq___redArg(v_e_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec_ref(v_e_2713_);
return v_res_2719_;
}
}
lean_object* l_Char_reduceBEq(lean_object* v_e_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Char_reduceBEq___redArg(v_e_2720_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT void l_Char_reduceBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2720_ = stack[0].m_obj;
lean_object* v_a_2721_ = stack[1].m_obj;
lean_object* v_a_2722_ = stack[2].m_obj;
lean_object* v_a_2723_ = stack[3].m_obj;
lean_object* v_a_2724_ = stack[4].m_obj;
lean_object* v_a_2725_ = stack[5].m_obj;
lean_object* v_a_2726_ = stack[6].m_obj;
lean_object* v_a_2727_ = stack[7].m_obj;
lean_object* v_res_2730_;
v_res_2730_ = l_Char_reduceBEq(v_e_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
stack->m_obj
 = v_res_2730_;
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object* v_e_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Char_reduceBEq(v_e_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_e_2731_);
return v_res_2740_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2761_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2762_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2759_, v___x_2760_, v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2763_;
v_res_2763_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2763_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27____boxed(lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_();
return v_res_2765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2770_ = 1;
v___x_2771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_);
v___x_2772_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2769_, v___x_2770_, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2773_;
v_res_2773_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2773_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29____boxed(lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_();
return v_res_2775_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2778_ = 1;
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_);
v___x_2780_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2777_, v___x_2778_, v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2781_;
v_res_2781_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31____boxed(lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_();
return v_res_2783_;
}
}
lean_object* l_Char_reduceBNe___redArg(lean_object* v_e_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2793_ = ((lean_object*)(l_Char_reduceBNe___redArg___closed__1));
v___x_2794_ = lean_unsigned_to_nat(4u);
v___x_2795_ = l_Lean_Expr_isAppOfArity(v_e_2787_, v___x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lean_Expr_appFn_x21(v_e_2787_);
v___x_2799_ = l_Lean_Expr_appArg_x21(v___x_2798_);
lean_dec_ref(v___x_2798_);
v___x_2800_ = l_Lean_Meta_getCharValue_x3f(v___x_2799_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2848_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2848_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2848_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_a_2801_) == 1)
{
lean_object* v_val_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2843_; 
v_val_2805_ = lean_ctor_get(v_a_2801_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_a_2801_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2807_ = v_a_2801_;
v_isShared_2808_ = v_isSharedCheck_2843_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_val_2805_);
lean_dec(v_a_2801_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2843_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = l_Lean_Expr_appArg_x21(v_e_2787_);
v___x_2810_ = l_Lean_Meta_getCharValue_x3f(v___x_2809_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2834_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___y_2816_; 
if (lean_obj_tag(v_a_2811_) == 1)
{
lean_object* v_val_2825_; uint32_t v___x_2826_; uint32_t v___x_2827_; uint8_t v___x_2828_; 
lean_del_object(v___x_2803_);
v_val_2825_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_val_2825_);
lean_dec_ref_known(v_a_2811_, 1);
v___x_2826_ = lean_unbox_uint32(v_val_2805_);
lean_dec(v_val_2805_);
v___x_2827_ = lean_unbox_uint32(v_val_2825_);
lean_dec(v_val_2825_);
v___x_2828_ = lean_uint32_dec_eq(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
if (v___x_2795_ == 0)
{
goto v___jp_2823_;
}
else
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_2816_ = v___x_2829_;
goto v___jp_2815_;
}
}
else
{
goto v___jp_2823_;
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_del_object(v___x_2813_);
lean_dec(v_a_2811_);
lean_del_object(v___x_2807_);
lean_dec(v_val_2805_);
v___x_2830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2830_);
v___x_2832_ = v___x_2803_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
v___jp_2815_:
{
lean_object* v___x_2818_; 
lean_inc_ref(v___y_2816_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 0);
lean_ctor_set(v___x_2807_, 0, v___y_2816_);
v___x_2818_ = v___x_2807_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___y_2816_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2818_);
v___x_2820_ = v___x_2813_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
v___jp_2823_:
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_2816_ = v___x_2824_;
goto v___jp_2815_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2807_);
lean_dec(v_val_2805_);
lean_del_object(v___x_2803_);
v_a_2835_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2810_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2810_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
lean_dec(v_a_2801_);
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2844_);
v___x_2846_ = v___x_2803_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_a_2849_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2800_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2800_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
LEAN_EXPORT void l_Char_reduceBNe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2787_ = stack[0].m_obj;
lean_object* v_a_2788_ = stack[1].m_obj;
lean_object* v_a_2789_ = stack[2].m_obj;
lean_object* v_a_2790_ = stack[3].m_obj;
lean_object* v_a_2791_ = stack[4].m_obj;
lean_object* v_res_2857_;
v_res_2857_ = l_Char_reduceBNe___redArg(v_e_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
stack->m_obj
 = v_res_2857_;
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object* v_e_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Char_reduceBNe___redArg(v_e_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec_ref(v_e_2858_);
return v_res_2864_;
}
}
lean_object* l_Char_reduceBNe(lean_object* v_e_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Char_reduceBNe___redArg(v_e_2865_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT void l_Char_reduceBNe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2865_ = stack[0].m_obj;
lean_object* v_a_2866_ = stack[1].m_obj;
lean_object* v_a_2867_ = stack[2].m_obj;
lean_object* v_a_2868_ = stack[3].m_obj;
lean_object* v_a_2869_ = stack[4].m_obj;
lean_object* v_a_2870_ = stack[5].m_obj;
lean_object* v_a_2871_ = stack[6].m_obj;
lean_object* v_a_2872_ = stack[7].m_obj;
lean_object* v_res_2875_;
v_res_2875_ = l_Char_reduceBNe(v_e_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
stack->m_obj
 = v_res_2875_;
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object* v_e_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Char_reduceBNe(v_e_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_e_2876_);
return v_res_2885_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2906_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2907_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2904_, v___x_2905_, v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2908_;
v_res_2908_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_();
stack->m_obj
 = v_res_2908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27____boxed(lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_();
return v_res_2910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2915_ = 1;
v___x_2916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_);
v___x_2917_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2914_, v___x_2915_, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2918_;
v_res_2918_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_();
stack->m_obj
 = v_res_2918_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29____boxed(lean_object* v_a_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_();
return v_res_2920_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2923_ = 1;
v___x_2924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_);
v___x_2925_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2922_, v___x_2923_, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2926_;
v_res_2926_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_();
stack->m_obj
 = v_res_2926_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31____boxed(lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_();
return v_res_2928_;
}
}
lean_object* l_Char_isValue___redArg(lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v___x_2935_; 
lean_inc_ref(v_e_2929_);
v___x_2935_ = l_Lean_Meta_getCharValue_x3f(v_e_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2955_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2955_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2955_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
if (lean_obj_tag(v_a_2936_) == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec_ref(v_e_2929_);
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
else
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2953_; 
v_isSharedCheck_2953_ = !lean_is_exclusive(v_a_2936_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v_a_2936_, 0);
lean_dec(v_unused_2954_);
v___x_2945_ = v_a_2936_;
v_isShared_2946_ = v_isSharedCheck_2953_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v_a_2936_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2953_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 0);
lean_ctor_set(v___x_2945_, 0, v_e_2929_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_e_2929_);
v___x_2948_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2950_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2948_);
v___x_2950_ = v___x_2938_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v_e_2929_);
v_a_2956_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2935_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2935_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT void l_Char_isValue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2929_ = stack[0].m_obj;
lean_object* v_a_2930_ = stack[1].m_obj;
lean_object* v_a_2931_ = stack[2].m_obj;
lean_object* v_a_2932_ = stack[3].m_obj;
lean_object* v_a_2933_ = stack[4].m_obj;
lean_object* v_res_2964_;
v_res_2964_ = l_Char_isValue___redArg(v_e_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
stack->m_obj
 = v_res_2964_;
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object* v_e_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Char_isValue___redArg(v_e_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
return v_res_2971_;
}
}
lean_object* l_Char_isValue(lean_object* v_e_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Char_isValue___redArg(v_e_2972_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT void l_Char_isValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2972_ = stack[0].m_obj;
lean_object* v_a_2973_ = stack[1].m_obj;
lean_object* v_a_2974_ = stack[2].m_obj;
lean_object* v_a_2975_ = stack[3].m_obj;
lean_object* v_a_2976_ = stack[4].m_obj;
lean_object* v_a_2977_ = stack[5].m_obj;
lean_object* v_a_2978_ = stack[6].m_obj;
lean_object* v_a_2979_ = stack[7].m_obj;
lean_object* v_res_2982_;
v_res_2982_ = l_Char_isValue(v_e_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
stack->m_obj
 = v_res_2982_;
}
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object* v_e_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Char_isValue(v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
return v_res_2992_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_3009_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_3010_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3007_, v___x_3008_, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3011_;
v_res_3011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_();
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20____boxed(lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_();
return v_res_3013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_3018_ = 0;
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_);
v___x_3020_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3017_, v___x_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3021_;
v_res_3021_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_();
stack->m_obj
 = v_res_3021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22____boxed(lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_();
return v_res_3023_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_3026_ = 0;
v___x_3027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_);
v___x_3028_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3025_, v___x_3026_, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3029_;
v_res_3029_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_();
stack->m_obj
 = v_res_3029_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24____boxed(lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_();
return v_res_3031_;
}
}
lean_object* l_Char_reduceOfNatAux___redArg(lean_object* v_e_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3036_, v_a_3038_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = l_Lean_Expr_cleanupAnnotations(v_a_3046_);
v___x_3048_ = l_Lean_Expr_isApp(v___x_3047_);
if (v___x_3048_ == 0)
{
lean_dec_ref(v___x_3047_);
goto v___jp_3042_;
}
else
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3047_);
v___x_3050_ = l_Lean_Expr_isApp(v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v___x_3049_);
goto v___jp_3042_;
}
else
{
lean_object* v_arg_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v_arg_3051_ = lean_ctor_get(v___x_3049_, 1);
lean_inc_ref(v_arg_3051_);
v___x_3052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3049_);
v___x_3053_ = ((lean_object*)(l_Char_reduceOfNatAux___redArg___closed__1));
v___x_3054_ = l_Lean_Expr_isConstOf(v___x_3052_, v___x_3053_);
lean_dec_ref(v___x_3052_);
if (v___x_3054_ == 0)
{
lean_dec_ref(v_arg_3051_);
goto v___jp_3042_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Meta_getNatValue_x3f(v_arg_3051_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec_ref(v_arg_3051_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3080_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3080_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3080_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
if (lean_obj_tag(v_a_3056_) == 1)
{
lean_object* v_val_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3075_; 
v_val_3060_ = lean_ctor_get(v_a_3056_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_a_3056_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3062_ = v_a_3056_;
v_isShared_3063_ = v_isSharedCheck_3075_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_val_3060_);
lean_dec(v_a_3056_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3075_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint32_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3064_ = l_Char_ofNat(v_val_3060_);
lean_dec(v_val_3060_);
v___x_3065_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_3066_ = lean_uint32_to_nat(v___x_3064_);
v___x_3067_ = l_Lean_mkRawNatLit(v___x_3066_);
v___x_3068_ = l_Lean_Expr_app___override(v___x_3065_, v___x_3067_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set_tag(v___x_3062_, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3068_);
v___x_3070_ = v___x_3062_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3070_);
v___x_3072_ = v___x_3058_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_a_3056_);
v___x_3076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3076_);
v___x_3078_ = v___x_3058_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3081_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3055_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3055_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
v_a_3089_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3045_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3045_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
v___jp_3042_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
}
LEAN_EXPORT void l_Char_reduceOfNatAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3036_ = stack[0].m_obj;
lean_object* v_a_3037_ = stack[1].m_obj;
lean_object* v_a_3038_ = stack[2].m_obj;
lean_object* v_a_3039_ = stack[3].m_obj;
lean_object* v_a_3040_ = stack[4].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_Char_reduceOfNatAux___redArg(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object* v_e_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Char_reduceOfNatAux___redArg(v_e_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
return v_res_3104_;
}
}
lean_object* l_Char_reduceOfNatAux(lean_object* v_e_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Char_reduceOfNatAux___redArg(v_e_3105_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT void l_Char_reduceOfNatAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3105_ = stack[0].m_obj;
lean_object* v_a_3106_ = stack[1].m_obj;
lean_object* v_a_3107_ = stack[2].m_obj;
lean_object* v_a_3108_ = stack[3].m_obj;
lean_object* v_a_3109_ = stack[4].m_obj;
lean_object* v_a_3110_ = stack[5].m_obj;
lean_object* v_a_3111_ = stack[6].m_obj;
lean_object* v_a_3112_ = stack[7].m_obj;
lean_object* v_res_3115_;
v_res_3115_ = l_Char_reduceOfNatAux(v_e_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
stack->m_obj
 = v_res_3115_;
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Char_reduceOfNatAux(v_e_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_a_3117_);
return v_res_3125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3143_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3144_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3141_, v___x_3142_, v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3145_;
v_res_3145_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_();
stack->m_obj
 = v_res_3145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21____boxed(lean_object* v_a_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_();
return v_res_3147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3152_ = 1;
v___x_3153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_);
v___x_3154_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3151_, v___x_3152_, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3155_;
v_res_3155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_();
stack->m_obj
 = v_res_3155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23____boxed(lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_();
return v_res_3157_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3160_ = 1;
v___x_3161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_);
v___x_3162_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3159_, v___x_3160_, v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3163_;
v_res_3163_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_();
stack->m_obj
 = v_res_3163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25____boxed(lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_();
return v_res_3165_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_unsigned_to_nat(65u);
v___x_3172_ = l_Lean_mkRawNatLit(v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__4(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__3, &l_Char_reduceDefault___redArg___closed__3_once, _init_l_Char_reduceDefault___redArg___closed__3);
v___x_3174_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_3175_ = l_Lean_Expr_app___override(v___x_3174_, v___x_3173_);
return v___x_3175_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__5(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__4, &l_Char_reduceDefault___redArg___closed__4_once, _init_l_Char_reduceDefault___redArg___closed__4);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
lean_object* l_Char_reduceDefault___redArg(lean_object* v_e_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3178_, v_a_3179_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3200_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3200_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3200_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = l_Lean_Expr_cleanupAnnotations(v_a_3185_);
v___x_3190_ = l_Lean_Expr_isApp(v___x_3189_);
if (v___x_3190_ == 0)
{
lean_dec_ref(v___x_3189_);
lean_del_object(v___x_3187_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3189_);
v___x_3192_ = l_Lean_Expr_isApp(v___x_3191_);
if (v___x_3192_ == 0)
{
lean_dec_ref(v___x_3191_);
lean_del_object(v___x_3187_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3191_);
v___x_3194_ = ((lean_object*)(l_Char_reduceDefault___redArg___closed__2));
v___x_3195_ = l_Lean_Expr_isConstOf(v___x_3193_, v___x_3194_);
lean_dec_ref(v___x_3193_);
if (v___x_3195_ == 0)
{
lean_del_object(v___x_3187_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3196_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__5, &l_Char_reduceDefault___redArg___closed__5_once, _init_l_Char_reduceDefault___redArg___closed__5);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3196_);
v___x_3198_ = v___x_3187_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
v_a_3201_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3184_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3184_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
v___jp_3181_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
LEAN_EXPORT void l_Char_reduceDefault___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3178_ = stack[0].m_obj;
lean_object* v_a_3179_ = stack[1].m_obj;
lean_object* v_res_3209_;
v_res_3209_ = l_Char_reduceDefault___redArg(v_e_3178_, v_a_3179_);
stack->m_obj
 = v_res_3209_;
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object* v_e_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Char_reduceDefault___redArg(v_e_3210_, v_a_3211_);
lean_dec(v_a_3211_);
return v_res_3213_;
}
}
lean_object* l_Char_reduceDefault(lean_object* v_e_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Char_reduceDefault___redArg(v_e_3214_, v_a_3219_);
return v___x_3223_;
}
}
LEAN_EXPORT void l_Char_reduceDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3214_ = stack[0].m_obj;
lean_object* v_a_3215_ = stack[1].m_obj;
lean_object* v_a_3216_ = stack[2].m_obj;
lean_object* v_a_3217_ = stack[3].m_obj;
lean_object* v_a_3218_ = stack[4].m_obj;
lean_object* v_a_3219_ = stack[5].m_obj;
lean_object* v_a_3220_ = stack[6].m_obj;
lean_object* v_a_3221_ = stack[7].m_obj;
lean_object* v_res_3224_;
v_res_3224_ = l_Char_reduceDefault(v_e_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
stack->m_obj
 = v_res_3224_;
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object* v_e_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Char_reduceDefault(v_e_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
return v_res_3234_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3253_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3254_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3251_, v___x_3252_, v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3255_;
v_res_3255_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_();
stack->m_obj
 = v_res_3255_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22____boxed(lean_object* v_a_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_();
return v_res_3257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3262_ = 1;
v___x_3263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_);
v___x_3264_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3261_, v___x_3262_, v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3265_;
v_res_3265_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_();
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24____boxed(lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_();
return v_res_3267_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3270_ = 1;
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_);
v___x_3272_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3269_, v___x_3270_, v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3273_;
v_res_3273_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_();
stack->m_obj
 = v_res_3273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26____boxed(lean_object* v_a_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_();
return v_res_3275_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(uint32_t v_a_3276_, lean_object* v_as_3277_, size_t v_i_3278_, size_t v_stop_3279_){
_start:
{
uint8_t v___x_3280_; 
v___x_3280_ = lean_usize_dec_eq(v_i_3278_, v_stop_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; uint32_t v___x_3282_; uint8_t v___x_3283_; 
v___x_3281_ = lean_array_uget_borrowed(v_as_3277_, v_i_3278_);
v___x_3282_ = lean_unbox_uint32(v___x_3281_);
v___x_3283_ = lean_uint32_dec_eq(v_a_3276_, v___x_3282_);
if (v___x_3283_ == 0)
{
size_t v___x_3284_; size_t v___x_3285_; 
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3278_, v___x_3284_);
v_i_3278_ = v___x_3285_;
goto _start;
}
else
{
return v___x_3283_;
}
}
else
{
uint8_t v___x_3287_; 
v___x_3287_ = 0;
return v___x_3287_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_3276_ = stack[0].m_num;
lean_object* v_as_3277_ = stack[1].m_obj;
size_t v_i_3278_ = stack[2].m_num;
size_t v_stop_3279_ = stack[3].m_num;
uint8_t v_res_3288_;
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_3276_, v_as_3277_, v_i_3278_, v_stop_3279_);
stack->m_num = v_res_3288_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0___boxed(lean_object* v_a_3289_, lean_object* v_as_3290_, lean_object* v_i_3291_, lean_object* v_stop_3292_){
_start:
{
uint32_t v_a_boxed_3293_; size_t v_i_boxed_3294_; size_t v_stop_boxed_3295_; uint8_t v_res_3296_; lean_object* v_r_3297_; 
v_a_boxed_3293_ = lean_unbox_uint32(v_a_3289_);
lean_dec(v_a_3289_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3291_);
lean_dec(v_i_3291_);
v_stop_boxed_3295_ = lean_unbox_usize(v_stop_3292_);
lean_dec(v_stop_3292_);
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_boxed_3293_, v_as_3290_, v_i_boxed_3294_, v_stop_boxed_3295_);
lean_dec_ref(v_as_3290_);
v_r_3297_ = lean_box(v_res_3296_);
return v_r_3297_;
}
}
uint8_t l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(lean_object* v_as_3298_, uint32_t v_a_3299_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = lean_array_get_size(v_as_3298_);
v___x_3302_ = lean_nat_dec_lt(v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
return v___x_3302_;
}
else
{
if (v___x_3302_ == 0)
{
return v___x_3302_;
}
else
{
size_t v___x_3303_; size_t v___x_3304_; uint8_t v___x_3305_; 
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = lean_usize_of_nat(v___x_3301_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_3299_, v_as_3298_, v___x_3303_, v___x_3304_);
return v___x_3305_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3298_ = stack[0].m_obj;
uint32_t v_a_3299_ = stack[1].m_num;
uint8_t v_res_3306_;
v_res_3306_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v_as_3298_, v_a_3299_);
stack->m_num = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0___boxed(lean_object* v_as_3307_, lean_object* v_a_3308_){
_start:
{
uint32_t v_a_boxed_3309_; uint8_t v_res_3310_; lean_object* v_r_3311_; 
v_a_boxed_3309_ = lean_unbox_uint32(v_a_3308_);
lean_dec(v_a_3308_);
v_res_3310_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v_as_3307_, v_a_boxed_3309_);
lean_dec_ref(v_as_3307_);
v_r_3311_ = lean_box(v_res_3310_);
return v_r_3311_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = 42;
v___x_3318_ = lean_box_uint32(v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2(void){
_start:
{
uint32_t v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = 102;
v___x_3320_ = lean_box_uint32(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3(void){
_start:
{
uint32_t v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = 101;
v___x_3322_ = lean_box_uint32(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4(void){
_start:
{
uint32_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = 100;
v___x_3324_ = lean_box_uint32(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5(void){
_start:
{
uint32_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = 99;
v___x_3326_ = lean_box_uint32(v___x_3325_);
return v___x_3326_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6(void){
_start:
{
uint32_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = 98;
v___x_3328_ = lean_box_uint32(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7(void){
_start:
{
uint32_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = 97;
v___x_3330_ = lean_box_uint32(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8(void){
_start:
{
uint32_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 57;
v___x_3332_ = lean_box_uint32(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9(void){
_start:
{
uint32_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = 56;
v___x_3334_ = lean_box_uint32(v___x_3333_);
return v___x_3334_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10(void){
_start:
{
uint32_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = 55;
v___x_3336_ = lean_box_uint32(v___x_3335_);
return v___x_3336_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11(void){
_start:
{
uint32_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = 54;
v___x_3338_ = lean_box_uint32(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12(void){
_start:
{
uint32_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = 53;
v___x_3340_ = lean_box_uint32(v___x_3339_);
return v___x_3340_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13(void){
_start:
{
uint32_t v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = 52;
v___x_3342_ = lean_box_uint32(v___x_3341_);
return v___x_3342_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14(void){
_start:
{
uint32_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = 51;
v___x_3344_ = lean_box_uint32(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15(void){
_start:
{
uint32_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = 50;
v___x_3346_ = lean_box_uint32(v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16(void){
_start:
{
uint32_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = 49;
v___x_3348_ = lean_box_uint32(v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17(void){
_start:
{
uint32_t v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = 48;
v___x_3350_ = lean_box_uint32(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3351_ = lean_unsigned_to_nat(17u);
v___x_3352_ = lean_mk_empty_array_with_capacity(v___x_3351_);
v___x_3353_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17;
v___x_3354_ = lean_array_push(v___x_3352_, v___x_3353_);
v___x_3355_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16;
v___x_3356_ = lean_array_push(v___x_3354_, v___x_3355_);
v___x_3357_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15;
v___x_3358_ = lean_array_push(v___x_3356_, v___x_3357_);
v___x_3359_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14;
v___x_3360_ = lean_array_push(v___x_3358_, v___x_3359_);
v___x_3361_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13;
v___x_3362_ = lean_array_push(v___x_3360_, v___x_3361_);
v___x_3363_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12;
v___x_3364_ = lean_array_push(v___x_3362_, v___x_3363_);
v___x_3365_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11;
v___x_3366_ = lean_array_push(v___x_3364_, v___x_3365_);
v___x_3367_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10;
v___x_3368_ = lean_array_push(v___x_3366_, v___x_3367_);
v___x_3369_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9;
v___x_3370_ = lean_array_push(v___x_3368_, v___x_3369_);
v___x_3371_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8;
v___x_3372_ = lean_array_push(v___x_3370_, v___x_3371_);
v___x_3373_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7;
v___x_3374_ = lean_array_push(v___x_3372_, v___x_3373_);
v___x_3375_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6;
v___x_3376_ = lean_array_push(v___x_3374_, v___x_3375_);
v___x_3377_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5;
v___x_3378_ = lean_array_push(v___x_3376_, v___x_3377_);
v___x_3379_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4;
v___x_3380_ = lean_array_push(v___x_3378_, v___x_3379_);
v___x_3381_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3;
v___x_3382_ = lean_array_push(v___x_3380_, v___x_3381_);
v___x_3383_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2;
v___x_3384_ = lean_array_push(v___x_3382_, v___x_3383_);
v___x_3385_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1;
v___x_3386_ = lean_array_push(v___x_3384_, v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_box(0);
v___x_3392_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__5));
v___x_3393_ = l_Lean_mkConst(v___x_3392_, v___x_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = lean_box(0);
v___x_3398_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__8));
v___x_3399_ = l_Lean_mkConst(v___x_3398_, v___x_3397_);
return v___x_3399_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(0);
v___x_3404_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__11));
v___x_3405_ = l_Lean_mkConst(v___x_3404_, v___x_3403_);
return v___x_3405_;
}
}
lean_object* l_Char_Nat_reduceDigitCharEq___redArg(lean_object* v_e_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3413_ = lean_unsigned_to_nat(3u);
v___x_3414_ = l_Lean_Expr_isAppOfArity(v_e_3406_, v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec_ref(v_e_3406_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; lean_object* v_lhs_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3417_ = l_Lean_Expr_appFn_x21(v_e_3406_);
v_lhs_3418_ = l_Lean_Expr_appArg_x21(v___x_3417_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = l_Lean_Expr_isAppOfArity(v_lhs_3418_, v___x_3419_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v_lhs_3418_);
lean_dec_ref(v_e_3406_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
else
{
lean_object* v_rhs_3424_; lean_object* v___x_3425_; 
v_rhs_3424_ = l_Lean_Expr_appArg_x21(v_e_3406_);
lean_inc_ref(v_rhs_3424_);
v___x_3425_ = l_Lean_Meta_getCharValue_x3f(v_rhs_3424_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3461_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3461_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3461_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
if (lean_obj_tag(v_a_3426_) == 1)
{
lean_object* v_val_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3456_; 
v_val_3430_ = lean_ctor_get(v_a_3426_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_a_3426_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3432_ = v_a_3426_;
v_isShared_3433_ = v_isSharedCheck_3456_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_val_3430_);
lean_dec(v_a_3426_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3456_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; uint32_t v___x_3435_; uint8_t v___x_3436_; 
v___x_3434_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3435_ = lean_unbox_uint32(v_val_3430_);
lean_dec(v_val_3430_);
v___x_3436_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3437_ = l_Lean_Expr_appArg_x21(v_lhs_3418_);
lean_dec_ref(v_lhs_3418_);
v___x_3438_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3439_ = l_Lean_eagerReflBoolTrue;
v___x_3440_ = l_Lean_mkApp3(v___x_3438_, v___x_3437_, v_rhs_3424_, v___x_3439_);
v___x_3441_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3442_ = l_Lean_mkAppB(v___x_3441_, v_e_3406_, v___x_3440_);
v___x_3443_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3442_);
v___x_3445_ = v___x_3432_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3442_);
v___x_3445_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3446_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3446_, 0, v___x_3443_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
lean_ctor_set_uint8(v___x_3446_, sizeof(void*)*2, v___x_3421_);
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3447_);
v___x_3449_ = v___x_3428_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
lean_del_object(v___x_3432_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3418_);
lean_dec_ref(v_e_3406_);
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3452_);
v___x_3454_ = v___x_3428_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
lean_dec(v_a_3426_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3418_);
lean_dec_ref(v_e_3406_);
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3457_);
v___x_3459_ = v___x_3428_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3418_);
lean_dec_ref(v_e_3406_);
v_a_3462_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3425_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3425_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Char_Nat_reduceDigitCharEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3406_ = stack[0].m_obj;
lean_object* v_a_3407_ = stack[1].m_obj;
lean_object* v_a_3408_ = stack[2].m_obj;
lean_object* v_a_3409_ = stack[3].m_obj;
lean_object* v_a_3410_ = stack[4].m_obj;
lean_object* v_res_3470_;
v_res_3470_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___boxed(lean_object* v_e_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3477_;
}
}
lean_object* l_Char_Nat_reduceDigitCharEq(lean_object* v_e_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3478_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
return v___x_3487_;
}
}
LEAN_EXPORT void l_Char_Nat_reduceDigitCharEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3478_ = stack[0].m_obj;
lean_object* v_a_3479_ = stack[1].m_obj;
lean_object* v_a_3480_ = stack[2].m_obj;
lean_object* v_a_3481_ = stack[3].m_obj;
lean_object* v_a_3482_ = stack[4].m_obj;
lean_object* v_a_3483_ = stack[5].m_obj;
lean_object* v_a_3484_ = stack[6].m_obj;
lean_object* v_a_3485_ = stack[7].m_obj;
lean_object* v_res_3488_;
v_res_3488_ = l_Char_Nat_reduceDigitCharEq(v_e_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
stack->m_obj
 = v_res_3488_;
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___boxed(lean_object* v_e_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Char_Nat_reduceDigitCharEq(v_e_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
return v_res_3498_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3521_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3522_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3519_, v___x_3520_, v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3523_;
v_res_3523_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31____boxed(lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_();
return v_res_3525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3530_ = 1;
v___x_3531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_);
v___x_3532_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3529_, v___x_3530_, v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3533_;
v_res_3533_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_();
stack->m_obj
 = v_res_3533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33____boxed(lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_();
return v_res_3535_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_(){
_start:
{
lean_object* v___x_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3538_ = 1;
v___x_3539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_);
v___x_3540_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3537_, v___x_3538_, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3541_;
v_res_3541_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_();
stack->m_obj
 = v_res_3541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35____boxed(lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_();
return v_res_3543_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_box(0);
v___x_3549_ = l_Lean_Level_succ___override(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_box(0);
v___x_3551_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__2, &l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2);
v___x_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__3, &l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3);
v___x_3554_ = ((lean_object*)(l_Char_Nat_reduceEqDigitChar___redArg___closed__1));
v___x_3555_ = l_Lean_mkConst(v___x_3554_, v___x_3553_);
return v___x_3555_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_box(0);
v___x_3557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_3558_ = l_Lean_mkConst(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
lean_object* l_Char_Nat_reduceEqDigitChar___redArg(lean_object* v_e_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3565_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3566_ = lean_unsigned_to_nat(3u);
v___x_3567_ = l_Lean_Expr_isAppOfArity(v_e_3559_, v___x_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec_ref(v_e_3559_);
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
else
{
lean_object* v_digitCharExpr_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v_digitCharExpr_3570_ = l_Lean_Expr_appArg_x21(v_e_3559_);
v___x_3571_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = l_Lean_Expr_isAppOfArity(v_digitCharExpr_3570_, v___x_3571_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec_ref(v_digitCharExpr_3570_);
lean_dec_ref(v_e_3559_);
v___x_3574_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
else
{
lean_object* v___x_3576_; lean_object* v_charExpr_3577_; lean_object* v___x_3578_; 
v___x_3576_ = l_Lean_Expr_appFn_x21(v_e_3559_);
v_charExpr_3577_ = l_Lean_Expr_appArg_x21(v___x_3576_);
lean_dec_ref(v___x_3576_);
lean_inc_ref(v_charExpr_3577_);
v___x_3578_ = l_Lean_Meta_getCharValue_x3f(v_charExpr_3577_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3617_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3617_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3617_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
if (lean_obj_tag(v_a_3579_) == 1)
{
lean_object* v_val_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3612_; 
v_val_3583_ = lean_ctor_get(v_a_3579_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3579_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3585_ = v_a_3579_;
v_isShared_3586_ = v_isSharedCheck_3612_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_val_3583_);
lean_dec(v_a_3579_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3612_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; uint32_t v___x_3588_; uint8_t v___x_3589_; 
v___x_3587_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3588_ = lean_unbox_uint32(v_val_3583_);
lean_dec(v_val_3583_);
v___x_3589_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3587_, v___x_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3590_ = l_Lean_Expr_appArg_x21(v_digitCharExpr_3570_);
v___x_3591_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3592_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_charExpr_3577_);
v___x_3593_ = l_Lean_mkApp3(v___x_3591_, v___x_3590_, v_charExpr_3577_, v___x_3592_);
v___x_3594_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__4, &l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4);
v___x_3595_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__5, &l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5);
v___x_3596_ = l_Lean_mkApp4(v___x_3594_, v___x_3595_, v_digitCharExpr_3570_, v_charExpr_3577_, v___x_3593_);
v___x_3597_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3598_ = l_Lean_mkAppB(v___x_3597_, v_e_3559_, v___x_3596_);
v___x_3599_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3598_);
v___x_3601_ = v___x_3585_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3598_);
v___x_3601_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3602_, 0, v___x_3599_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
lean_ctor_set_uint8(v___x_3602_, sizeof(void*)*2, v___x_3573_);
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3603_);
v___x_3605_ = v___x_3581_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
lean_del_object(v___x_3585_);
lean_dec_ref(v_charExpr_3577_);
lean_dec_ref(v_digitCharExpr_3570_);
lean_dec_ref(v_e_3559_);
v___x_3608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3608_);
v___x_3610_ = v___x_3581_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
lean_dec(v_a_3579_);
lean_dec_ref(v_charExpr_3577_);
lean_dec_ref(v_digitCharExpr_3570_);
lean_dec_ref(v_e_3559_);
v___x_3613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3613_);
v___x_3615_ = v___x_3581_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_charExpr_3577_);
lean_dec_ref(v_digitCharExpr_3570_);
lean_dec_ref(v_e_3559_);
v_a_3618_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3578_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3578_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Char_Nat_reduceEqDigitChar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3559_ = stack[0].m_obj;
lean_object* v_a_3560_ = stack[1].m_obj;
lean_object* v_a_3561_ = stack[2].m_obj;
lean_object* v_a_3562_ = stack[3].m_obj;
lean_object* v_a_3563_ = stack[4].m_obj;
lean_object* v_res_3626_;
v_res_3626_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
stack->m_obj
 = v_res_3626_;
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg___boxed(lean_object* v_e_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
return v_res_3633_;
}
}
lean_object* l_Char_Nat_reduceEqDigitChar(lean_object* v_e_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3634_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT void l_Char_Nat_reduceEqDigitChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3634_ = stack[0].m_obj;
lean_object* v_a_3635_ = stack[1].m_obj;
lean_object* v_a_3636_ = stack[2].m_obj;
lean_object* v_a_3637_ = stack[3].m_obj;
lean_object* v_a_3638_ = stack[4].m_obj;
lean_object* v_a_3639_ = stack[5].m_obj;
lean_object* v_a_3640_ = stack[6].m_obj;
lean_object* v_a_3641_ = stack[7].m_obj;
lean_object* v_res_3644_;
v_res_3644_ = l_Char_Nat_reduceEqDigitChar(v_e_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
stack->m_obj
 = v_res_3644_;
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___boxed(lean_object* v_e_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Char_Nat_reduceEqDigitChar(v_e_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
return v_res_3654_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3674_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3675_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3672_, v___x_3673_, v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3676_;
v_res_3676_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_();
stack->m_obj
 = v_res_3676_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31____boxed(lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_();
return v_res_3678_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
return v___x_3680_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3683_ = 1;
v___x_3684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_);
v___x_3685_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3682_, v___x_3683_, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3686_;
v_res_3686_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_();
stack->m_obj
 = v_res_3686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33____boxed(lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_();
return v_res_3688_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_(){
_start:
{
lean_object* v___x_3690_; uint8_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3691_ = 1;
v___x_3692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_);
v___x_3693_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3690_, v___x_3691_, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3694_;
v_res_3694_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_();
stack->m_obj
 = v_res_3694_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35____boxed(lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_();
return v_res_3696_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_();
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
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_();
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
