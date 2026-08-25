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
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getCharValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Char_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getCharValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Char_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Char_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(lean_object* v_inst_37_, lean_object* v_declName_38_, lean_object* v_op_39_, lean_object* v_arity_40_, lean_object* v_e_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Lean_Expr_isAppOfArity(v_e_41_, v_declName_38_, v_arity_40_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_op_39_);
lean_dec_ref(v_inst_37_);
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___boxed(lean_object* v_inst_83_, lean_object* v_declName_84_, lean_object* v_op_85_, lean_object* v_arity_86_, lean_object* v_e_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg(v_inst_83_, v_declName_84_, v_op_85_, v_arity_86_, v_e_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec_ref(v_e_87_);
lean_dec(v_declName_84_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_declName_96_, lean_object* v_op_97_, lean_object* v_arity_98_, lean_object* v_e_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_Expr_isAppOfArity(v_e_99_, v_declName_96_, v_arity_98_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_op_97_);
lean_dec_ref(v_inst_95_);
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
v___x_131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___boxed(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_declName_146_, lean_object* v_op_147_, lean_object* v_arity_148_, lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary(v_00_u03b1_144_, v_inst_145_, v_declName_146_, v_op_147_, v_arity_148_, v_e_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(lean_object* v_declName_161_, lean_object* v_arity_162_, lean_object* v_op_163_, lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Expr_isAppOfArity(v_e_164_, v_declName_161_, v_arity_162_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_e_164_);
lean_dec_ref(v_op_163_);
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_176_, 1);
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
lean_dec_ref_known(v_a_183_, 1);
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
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___boxed(lean_object* v_declName_217_, lean_object* v_arity_218_, lean_object* v_op_219_, lean_object* v_e_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg(v_declName_217_, v_arity_218_, v_op_219_, v_e_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_declName_217_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(lean_object* v_declName_227_, lean_object* v_arity_228_, lean_object* v_op_229_, lean_object* v_e_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Expr_isAppOfArity(v_e_230_, v_declName_227_, v_arity_228_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_e_230_);
lean_dec_ref(v_op_229_);
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
lean_dec_ref_known(v_a_245_, 1);
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
lean_dec_ref_known(v_a_252_, 1);
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
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___boxed(lean_object* v_declName_286_, lean_object* v_arity_287_, lean_object* v_op_288_, lean_object* v_e_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred(v_declName_286_, v_arity_287_, v_op_288_, v_e_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_box(0);
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__2));
v___x_306_ = l_Lean_mkConst(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__5));
v___x_313_ = l_Lean_mkConst(v___x_312_, v___x_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(lean_object* v_declName_314_, lean_object* v_arity_315_, lean_object* v_op_316_, lean_object* v_e_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Expr_isAppOfArity(v_e_317_, v_declName_314_, v_arity_315_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v_op_316_);
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_339_, 1);
v___x_352_ = lean_apply_2(v_op_316_, v_val_333_, v_val_351_);
v___x_353_ = lean_unbox(v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_344_ = v___x_354_;
goto v___jp_343_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
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
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___boxed(lean_object* v_declName_383_, lean_object* v_arity_384_, lean_object* v_op_385_, lean_object* v_e_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg(v_declName_383_, v_arity_384_, v_op_385_, v_e_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec_ref(v_e_386_);
lean_dec(v_declName_383_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(lean_object* v_declName_393_, lean_object* v_arity_394_, lean_object* v_op_395_, lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = l_Lean_Expr_isAppOfArity(v_e_396_, v_declName_393_, v_arity_394_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v_op_395_);
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
lean_dec_ref_known(v_a_421_, 1);
v___x_434_ = lean_apply_2(v_op_395_, v_val_415_, v_val_433_);
v___x_435_ = lean_unbox(v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
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
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___boxed(lean_object* v_declName_465_, lean_object* v_arity_466_, lean_object* v_op_467_, lean_object* v_e_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred(v_declName_465_, v_arity_466_, v_op_467_, v_e_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
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
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
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
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_532_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_532_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_532_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_532_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint32_t v___y_508_; 
if (lean_obj_tag(v_a_503_) == 1)
{
lean_object* v_val_517_; uint8_t v___y_519_; uint32_t v___x_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v_val_517_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_a_503_, 1);
v___x_524_ = 65;
v___x_525_ = lean_unbox_uint32(v_val_517_);
v___x_526_ = lean_uint32_dec_le(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
v___y_519_ = v___x_526_;
goto v___jp_518_;
}
else
{
uint32_t v___x_527_; uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = 90;
v___x_528_ = lean_unbox_uint32(v_val_517_);
v___x_529_ = lean_uint32_dec_le(v___x_528_, v___x_527_);
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
v___jp_518_:
{
if (v___y_519_ == 0)
{
uint32_t v___x_520_; 
v___x_520_ = lean_unbox_uint32(v_val_517_);
lean_dec(v_val_517_);
v___y_508_ = v___x_520_;
goto v___jp_507_;
}
else
{
uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; 
v___x_521_ = 32;
v___x_522_ = lean_unbox_uint32(v_val_517_);
lean_dec(v_val_517_);
v___x_523_ = lean_uint32_add(v___x_522_, v___x_521_);
v___y_508_ = v___x_523_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
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
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_502_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_502_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___redArg___boxed(lean_object* v_e_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Char_reduceToLower___redArg(v_e_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_e_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower(lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Char_reduceToLower___redArg(v_e_548_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToLower___boxed(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Char_reduceToLower(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_e_558_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_584_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_585_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_582_, v___x_583_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20____boxed(lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_();
return v_res_587_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_alloc_closure((void*)(l_Char_reduceToLower___boxed), 9, 0);
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_592_ = 1;
v___x_593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_);
v___x_594_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22____boxed(lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_();
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_20_));
v___x_599_ = 1;
v___x_600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_22_);
v___x_601_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_598_, v___x_599_, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24____boxed(lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1388500878____hygCtx___hyg_24_();
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg(lean_object* v_e_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = ((lean_object*)(l_Char_reduceToUpper___redArg___closed__1));
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = l_Lean_Expr_isAppOfArity(v_e_608_, v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = l_Lean_Expr_appArg_x21(v_e_608_);
v___x_620_ = l_Lean_Meta_getCharValue_x3f(v___x_619_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_650_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_650_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_650_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_650_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint32_t v___y_626_; 
if (lean_obj_tag(v_a_621_) == 1)
{
lean_object* v_val_635_; uint8_t v___y_637_; uint32_t v___x_642_; uint32_t v___x_643_; uint8_t v___x_644_; 
v_val_635_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v_a_621_, 1);
v___x_642_ = 97;
v___x_643_ = lean_unbox_uint32(v_val_635_);
v___x_644_ = lean_uint32_dec_le(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
else
{
uint32_t v___x_645_; uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_645_ = 122;
v___x_646_ = lean_unbox_uint32(v_val_635_);
v___x_647_ = lean_uint32_dec_le(v___x_646_, v___x_645_);
v___y_637_ = v___x_647_;
goto v___jp_636_;
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
uint32_t v___x_638_; 
v___x_638_ = lean_unbox_uint32(v_val_635_);
lean_dec(v_val_635_);
v___y_626_ = v___x_638_;
goto v___jp_625_;
}
else
{
uint32_t v___x_639_; uint32_t v___x_640_; uint32_t v___x_641_; 
v___x_639_ = 4294967264;
v___x_640_ = lean_unbox_uint32(v_val_635_);
lean_dec(v_val_635_);
v___x_641_ = lean_uint32_add(v___x_640_, v___x_639_);
v___y_626_ = v___x_641_;
goto v___jp_625_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_del_object(v___x_623_);
lean_dec(v_a_621_);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_627_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_628_ = lean_uint32_to_nat(v___y_626_);
v___x_629_ = l_Lean_mkRawNatLit(v___x_628_);
v___x_630_ = l_Lean_Expr_app___override(v___x_627_, v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_631_);
v___x_633_ = v___x_623_;
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
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_a_651_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_620_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_620_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___redArg___boxed(lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Char_reduceToUpper___redArg(v_e_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec_ref(v_e_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper(lean_object* v_e_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Char_reduceToUpper___redArg(v_e_666_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToUpper___boxed(lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Char_reduceToUpper(v_e_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_e_676_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_702_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_703_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_700_, v___x_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20____boxed(lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_();
return v_res_705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_alloc_closure((void*)(l_Char_reduceToUpper___boxed), 9, 0);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_710_ = 1;
v___x_711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_);
v___x_712_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_709_, v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22____boxed(lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_();
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_20_));
v___x_717_ = 1;
v___x_718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_22_);
v___x_719_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_716_, v___x_717_, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24____boxed(lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_909336162____hygCtx___hyg_24_();
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg(lean_object* v_e_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = ((lean_object*)(l_Char_reduceToNat___redArg___closed__1));
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = l_Lean_Expr_isAppOfArity(v_e_726_, v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_Expr_appArg_x21(v_e_726_);
v___x_738_ = l_Lean_Meta_getCharValue_x3f(v___x_737_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_761_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_761_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_761_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_761_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
if (lean_obj_tag(v_a_739_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_756_; 
v_val_743_ = lean_ctor_get(v_a_739_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_756_ == 0)
{
v___x_745_ = v_a_739_;
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v_a_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint32_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_747_ = lean_unbox_uint32(v_val_743_);
lean_dec(v_val_743_);
v___x_748_ = lean_uint32_to_nat(v___x_747_);
v___x_749_ = l_Lean_mkNatLit(v___x_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 0);
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_751_);
v___x_753_ = v___x_741_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v_a_739_);
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_757_);
v___x_759_ = v___x_741_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_738_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_738_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___redArg___boxed(lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Char_reduceToNat___redArg(v_e_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_e_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat(lean_object* v_e_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Char_reduceToNat___redArg(v_e_777_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToNat___boxed(lean_object* v_e_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Char_reduceToNat(v_e_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_e_787_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_813_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_814_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_811_, v___x_812_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20____boxed(lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_();
return v_res_816_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_alloc_closure((void*)(l_Char_reduceToNat___boxed), 9, 0);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_821_ = 1;
v___x_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_);
v___x_823_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_820_, v___x_821_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22____boxed(lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_();
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_20_));
v___x_828_ = 1;
v___x_829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_22_);
v___x_830_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_827_, v___x_828_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24____boxed(lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2527246418____hygCtx___hyg_24_();
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg(lean_object* v_e_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = ((lean_object*)(l_Char_reduceIsWhitespace___redArg___closed__1));
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = l_Lean_Expr_isAppOfArity(v_e_837_, v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = l_Lean_Expr_appArg_x21(v_e_837_);
v___x_849_ = l_Lean_Meta_getCharValue_x3f(v___x_848_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_878_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_878_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___y_855_; 
if (lean_obj_tag(v_a_850_) == 1)
{
lean_object* v_val_862_; uint32_t v___x_863_; uint32_t v___x_864_; uint8_t v___x_865_; 
v_val_862_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_a_850_, 1);
v___x_863_ = 32;
v___x_864_ = lean_unbox_uint32(v_val_862_);
v___x_865_ = lean_uint32_dec_eq(v___x_864_, v___x_863_);
if (v___x_865_ == 0)
{
uint32_t v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = 9;
v___x_867_ = lean_unbox_uint32(v_val_862_);
v___x_868_ = lean_uint32_dec_eq(v___x_867_, v___x_866_);
if (v___x_868_ == 0)
{
uint32_t v___x_869_; uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_869_ = 13;
v___x_870_ = lean_unbox_uint32(v_val_862_);
v___x_871_ = lean_uint32_dec_eq(v___x_870_, v___x_869_);
if (v___x_871_ == 0)
{
uint32_t v___x_872_; uint32_t v___x_873_; uint8_t v___x_874_; 
v___x_872_ = 10;
v___x_873_ = lean_unbox_uint32(v_val_862_);
lean_dec(v_val_862_);
v___x_874_ = lean_uint32_dec_eq(v___x_873_, v___x_872_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_855_ = v___x_875_;
goto v___jp_854_;
}
else
{
goto v___jp_860_;
}
}
else
{
lean_dec(v_val_862_);
goto v___jp_860_;
}
}
else
{
lean_dec(v_val_862_);
goto v___jp_860_;
}
}
else
{
lean_dec(v_val_862_);
goto v___jp_860_;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_del_object(v___x_852_);
lean_dec(v_a_850_);
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
v___jp_854_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
lean_inc_ref(v___y_855_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___y_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
v___jp_860_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_855_ = v___x_861_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_849_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_849_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___redArg___boxed(lean_object* v_e_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Char_reduceIsWhitespace___redArg(v_e_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec_ref(v_e_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace(lean_object* v_e_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Char_reduceIsWhitespace___redArg(v_e_894_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsWhitespace___boxed(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Char_reduceIsWhitespace(v_e_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_930_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_931_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_928_, v___x_929_, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20____boxed(lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_();
return v_res_933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_alloc_closure((void*)(l_Char_reduceIsWhitespace___boxed), 9, 0);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_938_ = 1;
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_);
v___x_940_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_937_, v___x_938_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22____boxed(lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_();
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_20_));
v___x_945_ = 1;
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_22_);
v___x_947_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_944_, v___x_945_, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24____boxed(lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_678033891____hygCtx___hyg_24_();
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg(lean_object* v_e_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_960_ = ((lean_object*)(l_Char_reduceIsUpper___redArg___closed__1));
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = l_Lean_Expr_isAppOfArity(v_e_954_, v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = l_Lean_Expr_appArg_x21(v_e_954_);
v___x_966_ = l_Lean_Meta_getCharValue_x3f(v___x_965_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_990_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_990_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___y_972_; uint8_t v___y_978_; 
if (lean_obj_tag(v_a_967_) == 1)
{
lean_object* v_val_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint8_t v___x_984_; 
v_val_981_ = lean_ctor_get(v_a_967_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_a_967_, 1);
v___x_982_ = 65;
v___x_983_ = lean_unbox_uint32(v_val_981_);
v___x_984_ = lean_uint32_dec_le(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_dec(v_val_981_);
v___y_978_ = v___x_984_;
goto v___jp_977_;
}
else
{
uint32_t v___x_985_; uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_985_ = 90;
v___x_986_ = lean_unbox_uint32(v_val_981_);
lean_dec(v_val_981_);
v___x_987_ = lean_uint32_dec_le(v___x_986_, v___x_985_);
v___y_978_ = v___x_987_;
goto v___jp_977_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_del_object(v___x_969_);
lean_dec(v_a_967_);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_inc_ref(v___y_972_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___y_972_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
v___jp_977_:
{
if (v___y_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_972_ = v___x_979_;
goto v___jp_971_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_966_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_966_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___redArg___boxed(lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Char_reduceIsUpper___redArg(v_e_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_e_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper(lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Char_reduceIsUpper___redArg(v_e_1006_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsUpper___boxed(lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Char_reduceIsUpper(v_e_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_e_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1042_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1043_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1040_, v___x_1041_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20____boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_();
return v_res_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_alloc_closure((void*)(l_Char_reduceIsUpper___boxed), 9, 0);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1050_ = 1;
v___x_1051_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_);
v___x_1052_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1049_, v___x_1050_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22____boxed(lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_();
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_20_));
v___x_1057_ = 1;
v___x_1058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_22_);
v___x_1059_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1056_, v___x_1057_, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24____boxed(lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3896334987____hygCtx___hyg_24_();
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Char_reduceIsLower___redArg___closed__1));
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = l_Lean_Expr_isAppOfArity(v_e_1066_, v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = l_Lean_Expr_appArg_x21(v_e_1066_);
v___x_1078_ = l_Lean_Meta_getCharValue_x3f(v___x_1077_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1101_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1101_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1101_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___y_1084_; 
if (lean_obj_tag(v_a_1079_) == 1)
{
lean_object* v_val_1091_; uint32_t v___x_1092_; uint32_t v___x_1093_; uint8_t v___x_1094_; 
v_val_1091_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v_a_1079_, 1);
v___x_1092_ = 97;
v___x_1093_ = lean_unbox_uint32(v_val_1091_);
v___x_1094_ = lean_uint32_dec_le(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_dec(v_val_1091_);
goto v___jp_1089_;
}
else
{
uint32_t v___x_1095_; uint32_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = 122;
v___x_1096_ = lean_unbox_uint32(v_val_1091_);
lean_dec(v_val_1091_);
v___x_1097_ = lean_uint32_dec_le(v___x_1096_, v___x_1095_);
if (v___x_1097_ == 0)
{
goto v___jp_1089_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1084_ = v___x_1098_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_del_object(v___x_1081_);
lean_dec(v_a_1079_);
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_inc_ref(v___y_1084_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1084_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1085_);
v___x_1087_ = v___x_1081_;
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
v___jp_1089_:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1084_ = v___x_1090_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1078_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1078_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___redArg___boxed(lean_object* v_e_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Char_reduceIsLower___redArg(v_e_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec_ref(v_e_1110_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower(lean_object* v_e_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Char_reduceIsLower___redArg(v_e_1117_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsLower___boxed(lean_object* v_e_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Char_reduceIsLower(v_e_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_e_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1153_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1154_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1151_, v___x_1152_, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20____boxed(lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_();
return v_res_1156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_alloc_closure((void*)(l_Char_reduceIsLower___boxed), 9, 0);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1161_ = 1;
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_);
v___x_1163_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1160_, v___x_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22____boxed(lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_();
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_20_));
v___x_1168_ = 1;
v___x_1169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_22_);
v___x_1170_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1167_, v___x_1168_, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24____boxed(lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2052311774____hygCtx___hyg_24_();
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg(lean_object* v_e_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = ((lean_object*)(l_Char_reduceIsAlpha___redArg___closed__1));
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = l_Lean_Expr_isAppOfArity(v_e_1177_, v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = l_Lean_Expr_appArg_x21(v_e_1177_);
v___x_1189_ = l_Lean_Meta_getCharValue_x3f(v___x_1188_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1221_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1221_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1221_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___y_1195_; 
if (lean_obj_tag(v_a_1190_) == 1)
{
lean_object* v_val_1204_; uint8_t v___y_1206_; uint32_t v___x_1213_; uint32_t v___x_1214_; uint8_t v___x_1215_; 
v_val_1204_ = lean_ctor_get(v_a_1190_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_a_1190_, 1);
v___x_1213_ = 65;
v___x_1214_ = lean_unbox_uint32(v_val_1204_);
v___x_1215_ = lean_uint32_dec_le(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
v___y_1206_ = v___x_1215_;
goto v___jp_1205_;
}
else
{
uint32_t v___x_1216_; uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = 90;
v___x_1217_ = lean_unbox_uint32(v_val_1204_);
v___x_1218_ = lean_uint32_dec_le(v___x_1217_, v___x_1216_);
v___y_1206_ = v___x_1218_;
goto v___jp_1205_;
}
v___jp_1205_:
{
if (v___y_1206_ == 0)
{
uint32_t v___x_1207_; uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1207_ = 97;
v___x_1208_ = lean_unbox_uint32(v_val_1204_);
v___x_1209_ = lean_uint32_dec_le(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec(v_val_1204_);
goto v___jp_1200_;
}
else
{
uint32_t v___x_1210_; uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = 122;
v___x_1211_ = lean_unbox_uint32(v_val_1204_);
lean_dec(v_val_1204_);
v___x_1212_ = lean_uint32_dec_le(v___x_1211_, v___x_1210_);
if (v___x_1212_ == 0)
{
goto v___jp_1200_;
}
else
{
goto v___jp_1202_;
}
}
}
else
{
lean_dec(v_val_1204_);
goto v___jp_1202_;
}
}
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1192_);
lean_dec(v_a_1190_);
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc_ref(v___y_1195_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1195_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
v___jp_1200_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1195_ = v___x_1201_;
goto v___jp_1194_;
}
v___jp_1202_:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1195_ = v___x_1203_;
goto v___jp_1194_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1189_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1189_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___redArg___boxed(lean_object* v_e_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Char_reduceIsAlpha___redArg(v_e_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec_ref(v_e_1230_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha(lean_object* v_e_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Char_reduceIsAlpha___redArg(v_e_1237_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlpha___boxed(lean_object* v_e_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Char_reduceIsAlpha(v_e_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_e_1247_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1273_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1274_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1271_, v___x_1272_, v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20____boxed(lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_();
return v_res_1276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_alloc_closure((void*)(l_Char_reduceIsAlpha___boxed), 9, 0);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1281_ = 1;
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_);
v___x_1283_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1280_, v___x_1281_, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22____boxed(lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_();
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_20_));
v___x_1288_ = 1;
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_22_);
v___x_1290_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1287_, v___x_1288_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24____boxed(lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3413861558____hygCtx___hyg_24_();
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg(lean_object* v_e_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = ((lean_object*)(l_Char_reduceIsDigit___redArg___closed__1));
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = l_Lean_Expr_isAppOfArity(v_e_1297_, v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l_Lean_Expr_appArg_x21(v_e_1297_);
v___x_1309_ = l_Lean_Meta_getCharValue_x3f(v___x_1308_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1332_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1332_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1332_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___y_1315_; 
if (lean_obj_tag(v_a_1310_) == 1)
{
lean_object* v_val_1322_; uint32_t v___x_1323_; uint32_t v___x_1324_; uint8_t v___x_1325_; 
v_val_1322_ = lean_ctor_get(v_a_1310_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_a_1310_, 1);
v___x_1323_ = 48;
v___x_1324_ = lean_unbox_uint32(v_val_1322_);
v___x_1325_ = lean_uint32_dec_le(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_val_1322_);
goto v___jp_1320_;
}
else
{
uint32_t v___x_1326_; uint32_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = 57;
v___x_1327_ = lean_unbox_uint32(v_val_1322_);
lean_dec(v_val_1322_);
v___x_1328_ = lean_uint32_dec_le(v___x_1327_, v___x_1326_);
if (v___x_1328_ == 0)
{
goto v___jp_1320_;
}
else
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1315_ = v___x_1329_;
goto v___jp_1314_;
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_del_object(v___x_1312_);
lean_dec(v_a_1310_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
v___jp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_inc_ref(v___y_1315_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1315_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1316_);
v___x_1318_ = v___x_1312_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
v___jp_1320_:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1315_ = v___x_1321_;
goto v___jp_1314_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1309_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1309_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___redArg___boxed(lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Char_reduceIsDigit___redArg(v_e_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec_ref(v_e_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit(lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Char_reduceIsDigit___redArg(v_e_1348_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsDigit___boxed(lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Char_reduceIsDigit(v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_e_1358_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1384_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1385_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1382_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20____boxed(lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_();
return v_res_1387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_closure((void*)(l_Char_reduceIsDigit___boxed), 9, 0);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1392_ = 1;
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_);
v___x_1394_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1391_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22____boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_20_));
v___x_1399_ = 1;
v___x_1400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_22_);
v___x_1401_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1398_, v___x_1399_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24____boxed(lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3934525011____hygCtx___hyg_24_();
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg(lean_object* v_e_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = ((lean_object*)(l_Char_reduceIsAlphaNum___redArg___closed__1));
v___x_1415_ = lean_unsigned_to_nat(1u);
v___x_1416_ = l_Lean_Expr_isAppOfArity(v_e_1408_, v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = l_Lean_Expr_appArg_x21(v_e_1408_);
v___x_1420_ = l_Lean_Meta_getCharValue_x3f(v___x_1419_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1459_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1459_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1459_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___y_1426_; 
if (lean_obj_tag(v_a_1421_) == 1)
{
lean_object* v_val_1435_; uint8_t v___y_1444_; uint32_t v___x_1451_; uint32_t v___x_1452_; uint8_t v___x_1453_; 
v_val_1435_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_a_1421_, 1);
v___x_1451_ = 65;
v___x_1452_ = lean_unbox_uint32(v_val_1435_);
v___x_1453_ = lean_uint32_dec_le(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
v___y_1444_ = v___x_1453_;
goto v___jp_1443_;
}
else
{
uint32_t v___x_1454_; uint32_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1454_ = 90;
v___x_1455_ = lean_unbox_uint32(v_val_1435_);
v___x_1456_ = lean_uint32_dec_le(v___x_1455_, v___x_1454_);
v___y_1444_ = v___x_1456_;
goto v___jp_1443_;
}
v___jp_1436_:
{
uint32_t v___x_1437_; uint32_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = 48;
v___x_1438_ = lean_unbox_uint32(v_val_1435_);
v___x_1439_ = lean_uint32_dec_le(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec(v_val_1435_);
goto v___jp_1431_;
}
else
{
uint32_t v___x_1440_; uint32_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = 57;
v___x_1441_ = lean_unbox_uint32(v_val_1435_);
lean_dec(v_val_1435_);
v___x_1442_ = lean_uint32_dec_le(v___x_1441_, v___x_1440_);
if (v___x_1442_ == 0)
{
goto v___jp_1431_;
}
else
{
goto v___jp_1433_;
}
}
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
uint32_t v___x_1445_; uint32_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = 97;
v___x_1446_ = lean_unbox_uint32(v_val_1435_);
v___x_1447_ = lean_uint32_dec_le(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
goto v___jp_1436_;
}
else
{
uint32_t v___x_1448_; uint32_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = 122;
v___x_1449_ = lean_unbox_uint32(v_val_1435_);
v___x_1450_ = lean_uint32_dec_le(v___x_1449_, v___x_1448_);
if (v___x_1450_ == 0)
{
goto v___jp_1436_;
}
else
{
lean_dec(v_val_1435_);
goto v___jp_1433_;
}
}
}
else
{
lean_dec(v_val_1435_);
goto v___jp_1433_;
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_del_object(v___x_1423_);
lean_dec(v_a_1421_);
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
v___jp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_inc_ref(v___y_1426_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1426_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
v___jp_1431_:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_1426_ = v___x_1432_;
goto v___jp_1425_;
}
v___jp_1433_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_1426_ = v___x_1434_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1420_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1420_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___redArg___boxed(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Char_reduceIsAlphaNum___redArg(v_e_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec_ref(v_e_1468_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Char_reduceIsAlphaNum___redArg(v_e_1475_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceIsAlphaNum___boxed(lean_object* v_e_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Char_reduceIsAlphaNum(v_e_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_e_1485_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1511_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1512_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1509_, v___x_1510_, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20____boxed(lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_();
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_alloc_closure((void*)(l_Char_reduceIsAlphaNum___boxed), 9, 0);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1519_ = 1;
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_);
v___x_1521_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1518_, v___x_1519_, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22____boxed(lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_();
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_20_));
v___x_1526_ = 1;
v___x_1527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_22_);
v___x_1528_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1525_, v___x_1526_, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24____boxed(lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2292854610____hygCtx___hyg_24_();
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg(lean_object* v_e_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__2));
v___x_1544_ = lean_unsigned_to_nat(3u);
v___x_1545_ = l_Lean_Expr_isAppOfArity(v_e_1537_, v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = l_Lean_Expr_appArg_x21(v_e_1537_);
v___x_1549_ = l_Lean_Meta_getCharValue_x3f(v___x_1548_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1573_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1573_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1573_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1568_; 
v_val_1554_ = lean_ctor_get(v_a_1550_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1556_ = v_a_1550_;
v_isShared_1557_ = v_isSharedCheck_1568_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v_a_1550_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1568_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; uint32_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1558_ = ((lean_object*)(l_Char_reduceToString___redArg___closed__3));
v___x_1559_ = lean_unbox_uint32(v_val_1554_);
lean_dec(v_val_1554_);
v___x_1560_ = lean_string_push(v___x_1558_, v___x_1559_);
v___x_1561_ = l_Lean_mkStrLit(v___x_1560_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1561_);
v___x_1563_ = v___x_1556_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1563_);
v___x_1565_ = v___x_1552_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_dec(v_a_1550_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1569_);
v___x_1571_ = v___x_1552_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1549_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1549_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___redArg___boxed(lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Char_reduceToString___redArg(v_e_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec_ref(v_e_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString(lean_object* v_e_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Char_reduceToString___redArg(v_e_1589_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceToString___boxed(lean_object* v_e_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Char_reduceToString(v_e_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_e_1599_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1633_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1634_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1631_, v___x_1632_, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23____boxed(lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_();
return v_res_1636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_alloc_closure((void*)(l_Char_reduceToString___boxed), 9, 0);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1641_ = 1;
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_);
v___x_1643_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1640_, v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25____boxed(lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_();
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_1648_ = 1;
v___x_1649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_25_);
v___x_1650_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1647_, v___x_1648_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27____boxed(lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_27_();
return v_res_1652_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__4(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Lean_Level_ofNat(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__5(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__4, &l_Char_reduceVal___redArg___closed__4_once, _init_l_Char_reduceVal___redArg___closed__4);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__6(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__5, &l_Char_reduceVal___redArg___closed__5_once, _init_l_Char_reduceVal___redArg___closed__5);
v___x_1667_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__3));
v___x_1668_ = l_Lean_Expr_const___override(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__9(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__8));
v___x_1674_ = l_Lean_mkConst(v___x_1673_, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Char_reduceVal___redArg___closed__12(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_box(0);
v___x_1680_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__11));
v___x_1681_ = l_Lean_Expr_const___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg(lean_object* v_e_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1682_, v_a_1684_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1741_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1741_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1741_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = l_Lean_Expr_cleanupAnnotations(v_a_1689_);
v___x_1699_ = l_Lean_Expr_isApp(v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v___x_1698_);
goto v___jp_1693_;
}
else
{
lean_object* v_arg_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_arg_1700_ = lean_ctor_get(v___x_1698_, 1);
lean_inc_ref(v_arg_1700_);
v___x_1701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1698_);
v___x_1702_ = ((lean_object*)(l_Char_reduceVal___redArg___closed__1));
v___x_1703_ = l_Lean_Expr_isConstOf(v___x_1701_, v___x_1702_);
lean_dec_ref(v___x_1701_);
if (v___x_1703_ == 0)
{
lean_dec_ref(v_arg_1700_);
goto v___jp_1693_;
}
else
{
lean_object* v___x_1704_; 
lean_del_object(v___x_1691_);
v___x_1704_ = l_Lean_Meta_getCharValue_x3f(v_arg_1700_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1732_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
if (lean_obj_tag(v_a_1705_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1727_; 
v_val_1709_ = lean_ctor_get(v_a_1705_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_a_1705_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1711_ = v_a_1705_;
v_isShared_1712_ = v_isSharedCheck_1727_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_val_1709_);
lean_dec(v_a_1705_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1727_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
uint32_t v___x_1713_; lean_object* v___x_1714_; lean_object* v_r_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1713_ = lean_unbox_uint32(v_val_1709_);
lean_dec(v_val_1709_);
v___x_1714_ = lean_uint32_to_nat(v___x_1713_);
v_r_1715_ = l_Lean_mkRawNatLit(v___x_1714_);
v___x_1716_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__6, &l_Char_reduceVal___redArg___closed__6_once, _init_l_Char_reduceVal___redArg___closed__6);
v___x_1717_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__9, &l_Char_reduceVal___redArg___closed__9_once, _init_l_Char_reduceVal___redArg___closed__9);
v___x_1718_ = lean_obj_once(&l_Char_reduceVal___redArg___closed__12, &l_Char_reduceVal___redArg___closed__12_once, _init_l_Char_reduceVal___redArg___closed__12);
lean_inc_ref(v_r_1715_);
v___x_1719_ = l_Lean_Expr_app___override(v___x_1718_, v_r_1715_);
v___x_1720_ = l_Lean_mkApp3(v___x_1716_, v___x_1717_, v_r_1715_, v___x_1719_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1720_);
v___x_1722_ = v___x_1711_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1722_);
v___x_1724_ = v___x_1707_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec(v_a_1705_);
v___x_1728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1728_);
v___x_1730_ = v___x_1707_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1704_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1704_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
v___jp_1693_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1688_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1688_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___redArg___boxed(lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Char_reduceVal___redArg(v_e_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal(lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Char_reduceVal___redArg(v_e_1757_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceVal___boxed(lean_object* v_e_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Char_reduceVal(v_e_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1793_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1794_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1791_, v___x_1792_, v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20____boxed(lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_();
return v_res_1796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_alloc_closure((void*)(l_Char_reduceVal___boxed), 9, 0);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1801_ = 1;
v___x_1802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_);
v___x_1803_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1800_, v___x_1801_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22____boxed(lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_();
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_20_));
v___x_1808_ = 1;
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_22_);
v___x_1810_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1807_, v___x_1808_, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24____boxed(lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_164368340____hygCtx___hyg_24_();
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg(lean_object* v_e_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = ((lean_object*)(l_Char_reduceLT___redArg___closed__2));
v___x_1825_ = lean_unsigned_to_nat(4u);
v___x_1826_ = l_Lean_Expr_isAppOfArity(v_e_1818_, v___x_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_e_1818_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = l_Lean_Expr_appFn_x21(v_e_1818_);
v___x_1830_ = l_Lean_Expr_appArg_x21(v___x_1829_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = l_Lean_Meta_getCharValue_x3f(v___x_1830_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1865_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1865_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1865_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (lean_obj_tag(v_a_1832_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1834_);
v_val_1836_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v_a_1832_, 1);
v___x_1837_ = l_Lean_Expr_appArg_x21(v_e_1818_);
v___x_1838_ = l_Lean_Meta_getCharValue_x3f(v___x_1837_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1852_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 1)
{
lean_object* v_val_1843_; uint32_t v___x_1844_; uint32_t v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1841_);
v_val_1843_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_val_1843_);
lean_dec_ref_known(v_a_1839_, 1);
v___x_1844_ = lean_unbox_uint32(v_val_1836_);
lean_dec(v_val_1836_);
v___x_1845_ = lean_unbox_uint32(v_val_1843_);
lean_dec(v_val_1843_);
v___x_1846_ = lean_uint32_dec_lt(v___x_1844_, v___x_1845_);
v___x_1847_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1818_, v___x_1846_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_a_1839_);
lean_dec(v_val_1836_);
lean_dec_ref(v_e_1818_);
v___x_1848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1848_);
v___x_1850_ = v___x_1841_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_val_1836_);
lean_dec_ref(v_e_1818_);
v_a_1853_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1838_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1838_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_e_1818_);
v___x_1861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1861_);
v___x_1863_ = v___x_1834_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_e_1818_);
v_a_1866_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1831_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1831_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___redArg___boxed(lean_object* v_e_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Char_reduceLT___redArg(v_e_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT(lean_object* v_e_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Char_reduceLT___redArg(v_e_1881_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLT___boxed(lean_object* v_e_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Char_reduceLT(v_e_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1921_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1922_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1919_, v___x_1920_, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27____boxed(lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_();
return v_res_1924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_alloc_closure((void*)(l_Char_reduceLT___boxed), 9, 0);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1929_ = 1;
v___x_1930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_);
v___x_1931_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1928_, v___x_1929_, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29____boxed(lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_();
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_1936_ = 1;
v___x_1937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_29_);
v___x_1938_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1935_, v___x_1936_, v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31____boxed(lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_31_();
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg(lean_object* v_e_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = ((lean_object*)(l_Char_reduceLE___redArg___closed__2));
v___x_1953_ = lean_unsigned_to_nat(4u);
v___x_1954_ = l_Lean_Expr_isAppOfArity(v_e_1946_, v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec_ref(v_e_1946_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = l_Lean_Expr_appFn_x21(v_e_1946_);
v___x_1958_ = l_Lean_Expr_appArg_x21(v___x_1957_);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l_Lean_Meta_getCharValue_x3f(v___x_1958_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1993_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1993_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1993_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
if (lean_obj_tag(v_a_1960_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_del_object(v___x_1962_);
v_val_1964_ = lean_ctor_get(v_a_1960_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v_a_1960_, 1);
v___x_1965_ = l_Lean_Expr_appArg_x21(v_e_1946_);
v___x_1966_ = l_Lean_Meta_getCharValue_x3f(v___x_1965_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1980_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1980_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1980_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
if (lean_obj_tag(v_a_1967_) == 1)
{
lean_object* v_val_1971_; uint32_t v___x_1972_; uint32_t v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1969_);
v_val_1971_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v_a_1967_, 1);
v___x_1972_ = lean_unbox_uint32(v_val_1964_);
lean_dec(v_val_1964_);
v___x_1973_ = lean_unbox_uint32(v_val_1971_);
lean_dec(v_val_1971_);
v___x_1974_ = lean_uint32_dec_le(v___x_1972_, v___x_1973_);
v___x_1975_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_1946_, v___x_1974_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec(v_a_1967_);
lean_dec(v_val_1964_);
lean_dec_ref(v_e_1946_);
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1976_);
v___x_1978_ = v___x_1969_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_val_1964_);
lean_dec_ref(v_e_1946_);
v_a_1981_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1966_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1966_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec(v_a_1960_);
lean_dec_ref(v_e_1946_);
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1989_);
v___x_1991_ = v___x_1962_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_e_1946_);
v_a_1994_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1959_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1959_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___redArg___boxed(lean_object* v_e_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Char_reduceLE___redArg(v_e_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE(lean_object* v_e_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Char_reduceLE___redArg(v_e_2009_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceLE___boxed(lean_object* v_e_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Char_reduceLE(v_e_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2049_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2050_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2047_, v___x_2048_, v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27____boxed(lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_();
return v_res_2052_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_alloc_closure((void*)(l_Char_reduceLE___boxed), 9, 0);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2057_ = 1;
v___x_2058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_);
v___x_2059_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2056_, v___x_2057_, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29____boxed(lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_();
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2064_ = 1;
v___x_2065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_29_);
v___x_2066_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2063_, v___x_2064_, v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31____boxed(lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_31_();
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg(lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2080_ = ((lean_object*)(l_Char_reduceGT___redArg___closed__2));
v___x_2081_ = lean_unsigned_to_nat(4u);
v___x_2082_ = l_Lean_Expr_isAppOfArity(v_e_2074_, v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v_e_2074_);
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = l_Lean_Expr_appFn_x21(v_e_2074_);
v___x_2086_ = l_Lean_Expr_appArg_x21(v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = l_Lean_Meta_getCharValue_x3f(v___x_2086_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2121_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2121_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2121_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
if (lean_obj_tag(v_a_2088_) == 1)
{
lean_object* v_val_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_del_object(v___x_2090_);
v_val_2092_ = lean_ctor_get(v_a_2088_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v_a_2088_, 1);
v___x_2093_ = l_Lean_Expr_appArg_x21(v_e_2074_);
v___x_2094_ = l_Lean_Meta_getCharValue_x3f(v___x_2093_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2108_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
if (lean_obj_tag(v_a_2095_) == 1)
{
lean_object* v_val_2099_; uint32_t v___x_2100_; uint32_t v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; 
lean_del_object(v___x_2097_);
v_val_2099_ = lean_ctor_get(v_a_2095_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v_a_2095_, 1);
v___x_2100_ = lean_unbox_uint32(v_val_2099_);
lean_dec(v_val_2099_);
v___x_2101_ = lean_unbox_uint32(v_val_2092_);
lean_dec(v_val_2092_);
v___x_2102_ = lean_uint32_dec_lt(v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2074_, v___x_2102_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
lean_dec(v_a_2095_);
lean_dec(v_val_2092_);
lean_dec_ref(v_e_2074_);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2104_);
v___x_2106_ = v___x_2097_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_val_2092_);
lean_dec_ref(v_e_2074_);
v_a_2109_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2094_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2094_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec(v_a_2088_);
lean_dec_ref(v_e_2074_);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2117_);
v___x_2119_ = v___x_2090_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_e_2074_);
v_a_2122_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2087_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2087_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___redArg___boxed(lean_object* v_e_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Char_reduceGT___redArg(v_e_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT(lean_object* v_e_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Char_reduceGT___redArg(v_e_2137_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGT___boxed(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Char_reduceGT(v_e_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1447824035____hygCtx___hyg_27_));
v___x_2164_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2165_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2162_, v___x_2163_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27____boxed(lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_();
return v_res_2167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_alloc_closure((void*)(l_Char_reduceGT___boxed), 9, 0);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2172_ = 1;
v___x_2173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_);
v___x_2174_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2171_, v___x_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29____boxed(lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_();
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_27_));
v___x_2179_ = 1;
v___x_2180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_29_);
v___x_2181_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2178_, v___x_2179_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31____boxed(lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_597559259____hygCtx___hyg_31_();
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg(lean_object* v_e_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = ((lean_object*)(l_Char_reduceGE___redArg___closed__2));
v___x_2196_ = lean_unsigned_to_nat(4u);
v___x_2197_ = l_Lean_Expr_isAppOfArity(v_e_2189_, v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v_e_2189_);
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = l_Lean_Expr_appFn_x21(v_e_2189_);
v___x_2201_ = l_Lean_Expr_appArg_x21(v___x_2200_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = l_Lean_Meta_getCharValue_x3f(v___x_2201_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2236_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2236_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2236_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
if (lean_obj_tag(v_a_2203_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_del_object(v___x_2205_);
v_val_2207_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v_a_2203_, 1);
v___x_2208_ = l_Lean_Expr_appArg_x21(v_e_2189_);
v___x_2209_ = l_Lean_Meta_getCharValue_x3f(v___x_2208_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2223_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2223_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2223_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
if (lean_obj_tag(v_a_2210_) == 1)
{
lean_object* v_val_2214_; uint32_t v___x_2215_; uint32_t v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; 
lean_del_object(v___x_2212_);
v_val_2214_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v_a_2210_, 1);
v___x_2215_ = lean_unbox_uint32(v_val_2214_);
lean_dec(v_val_2214_);
v___x_2216_ = lean_unbox_uint32(v_val_2207_);
lean_dec(v_val_2207_);
v___x_2217_ = lean_uint32_dec_le(v___x_2215_, v___x_2216_);
v___x_2218_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2189_, v___x_2217_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
lean_dec(v_a_2210_);
lean_dec(v_val_2207_);
lean_dec_ref(v_e_2189_);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2219_);
v___x_2221_ = v___x_2212_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_val_2207_);
lean_dec_ref(v_e_2189_);
v_a_2224_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2209_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2209_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec(v_a_2203_);
lean_dec_ref(v_e_2189_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2232_);
v___x_2234_ = v___x_2205_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_e_2189_);
v_a_2237_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2202_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2202_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___redArg___boxed(lean_object* v_e_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Char_reduceGE___redArg(v_e_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE(lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Char_reduceGE___redArg(v_e_2252_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceGE___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Char_reduceGE(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1444345829____hygCtx___hyg_27_));
v___x_2279_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2280_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2277_, v___x_2278_, v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27____boxed(lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_();
return v_res_2282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_alloc_closure((void*)(l_Char_reduceGE___boxed), 9, 0);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2287_ = 1;
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_);
v___x_2289_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2286_, v___x_2287_, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29____boxed(lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_();
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_27_));
v___x_2294_ = 1;
v___x_2295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_29_);
v___x_2296_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2293_, v___x_2294_, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31____boxed(lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3507066772____hygCtx___hyg_31_();
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg(lean_object* v_e_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_2309_ = lean_unsigned_to_nat(3u);
v___x_2310_ = l_Lean_Expr_isAppOfArity(v_e_2302_, v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_e_2302_);
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = l_Lean_Expr_appFn_x21(v_e_2302_);
v___x_2314_ = l_Lean_Expr_appArg_x21(v___x_2313_);
lean_dec_ref(v___x_2313_);
v___x_2315_ = l_Lean_Meta_getCharValue_x3f(v___x_2314_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2349_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2349_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2349_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_del_object(v___x_2318_);
v_val_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_a_2316_, 1);
v___x_2321_ = l_Lean_Expr_appArg_x21(v_e_2302_);
v___x_2322_ = l_Lean_Meta_getCharValue_x3f(v___x_2321_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2336_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2336_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2336_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
if (lean_obj_tag(v_a_2323_) == 1)
{
lean_object* v_val_2327_; uint32_t v___x_2328_; uint32_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
lean_del_object(v___x_2325_);
v_val_2327_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v_a_2323_, 1);
v___x_2328_ = lean_unbox_uint32(v_val_2320_);
lean_dec(v_val_2320_);
v___x_2329_ = lean_unbox_uint32(v_val_2327_);
lean_dec(v_val_2327_);
v___x_2330_ = lean_uint32_dec_eq(v___x_2328_, v___x_2329_);
v___x_2331_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2302_, v___x_2330_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec(v_a_2323_);
lean_dec(v_val_2320_);
lean_dec_ref(v_e_2302_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2332_);
v___x_2334_ = v___x_2325_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_val_2320_);
lean_dec_ref(v_e_2302_);
v_a_2337_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2322_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2322_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_a_2316_);
lean_dec_ref(v_e_2302_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2345_);
v___x_2347_ = v___x_2318_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_e_2302_);
v_a_2350_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2315_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2315_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___redArg___boxed(lean_object* v_e_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Char_reduceEq___redArg(v_e_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq(lean_object* v_e_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Char_reduceEq___redArg(v_e_2365_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceEq___boxed(lean_object* v_e_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Char_reduceEq(v_e_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2404_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2405_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2402_, v___x_2403_, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27____boxed(lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_();
return v_res_2407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_alloc_closure((void*)(l_Char_reduceEq___boxed), 9, 0);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2412_ = 1;
v___x_2413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_);
v___x_2414_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2411_, v___x_2412_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29____boxed(lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_();
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_27_));
v___x_2419_ = 1;
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_29_);
v___x_2421_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2418_, v___x_2419_, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31____boxed(lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_866257725____hygCtx___hyg_31_();
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg(lean_object* v_e_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2433_ = ((lean_object*)(l_Char_reduceNe___redArg___closed__1));
v___x_2434_ = lean_unsigned_to_nat(3u);
v___x_2435_ = l_Lean_Expr_isAppOfArity(v_e_2427_, v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref(v_e_2427_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_Expr_appFn_x21(v_e_2427_);
v___x_2439_ = l_Lean_Expr_appArg_x21(v___x_2438_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = l_Lean_Meta_getCharValue_x3f(v___x_2439_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2476_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2476_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2476_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
if (lean_obj_tag(v_a_2441_) == 1)
{
lean_object* v_val_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_del_object(v___x_2443_);
v_val_2445_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v_a_2441_, 1);
v___x_2446_ = l_Lean_Expr_appArg_x21(v_e_2427_);
v___x_2447_ = l_Lean_Meta_getCharValue_x3f(v___x_2446_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2463_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
if (lean_obj_tag(v_a_2448_) == 1)
{
lean_object* v_val_2452_; uint32_t v___x_2453_; uint32_t v___x_2454_; uint8_t v___x_2455_; 
lean_del_object(v___x_2450_);
v_val_2452_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v_a_2448_, 1);
v___x_2453_ = lean_unbox_uint32(v_val_2445_);
lean_dec(v_val_2445_);
v___x_2454_ = lean_unbox_uint32(v_val_2452_);
lean_dec(v_val_2452_);
v___x_2455_ = lean_uint32_dec_eq(v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2427_, v___x_2435_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2456_;
}
else
{
uint8_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = 0;
v___x_2458_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2427_, v___x_2457_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2458_;
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
lean_dec(v_a_2448_);
lean_dec(v_val_2445_);
lean_dec_ref(v_e_2427_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2459_);
v___x_2461_ = v___x_2450_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_val_2445_);
lean_dec_ref(v_e_2427_);
v_a_2464_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2447_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2447_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_a_2441_);
lean_dec_ref(v_e_2427_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2472_);
v___x_2474_ = v___x_2443_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_e_2427_);
v_a_2477_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2440_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2440_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___redArg___boxed(lean_object* v_e_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Char_reduceNe___redArg(v_e_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe(lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Char_reduceNe___redArg(v_e_2492_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceNe___boxed(lean_object* v_e_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Char_reduceNe(v_e_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2536_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2537_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2534_, v___x_2535_, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27____boxed(lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_();
return v_res_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_alloc_closure((void*)(l_Char_reduceNe___boxed), 9, 0);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2544_ = 1;
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_);
v___x_2546_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2543_, v___x_2544_, v___x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29____boxed(lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_();
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_27_));
v___x_2551_ = 1;
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_29_);
v___x_2553_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2550_, v___x_2551_, v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31____boxed(lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1172652665____hygCtx___hyg_31_();
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg(lean_object* v_e_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2567_ = ((lean_object*)(l_Char_reduceBEq___redArg___closed__2));
v___x_2568_ = lean_unsigned_to_nat(4u);
v___x_2569_ = l_Lean_Expr_isAppOfArity(v_e_2561_, v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = l_Lean_Expr_appFn_x21(v_e_2561_);
v___x_2573_ = l_Lean_Expr_appArg_x21(v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = l_Lean_Meta_getCharValue_x3f(v___x_2573_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2621_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2621_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2621_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
if (lean_obj_tag(v_a_2575_) == 1)
{
lean_object* v_val_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2616_; 
v_val_2579_ = lean_ctor_get(v_a_2575_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_a_2575_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2581_ = v_a_2575_;
v_isShared_2582_ = v_isSharedCheck_2616_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_val_2579_);
lean_dec(v_a_2575_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2616_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = l_Lean_Expr_appArg_x21(v_e_2561_);
v___x_2584_ = l_Lean_Meta_getCharValue_x3f(v___x_2583_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2607_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2607_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2607_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___y_2590_; 
if (lean_obj_tag(v_a_2585_) == 1)
{
lean_object* v_val_2597_; uint32_t v___x_2598_; uint32_t v___x_2599_; uint8_t v___x_2600_; 
lean_del_object(v___x_2577_);
v_val_2597_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_a_2585_, 1);
v___x_2598_ = lean_unbox_uint32(v_val_2579_);
lean_dec(v_val_2579_);
v___x_2599_ = lean_unbox_uint32(v_val_2597_);
lean_dec(v_val_2597_);
v___x_2600_ = lean_uint32_dec_eq(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_2590_ = v___x_2601_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_2590_ = v___x_2602_;
goto v___jp_2589_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_del_object(v___x_2587_);
lean_dec(v_a_2585_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
v___x_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2603_);
v___x_2605_ = v___x_2577_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
v___jp_2589_:
{
lean_object* v___x_2592_; 
lean_inc_ref(v___y_2590_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 0);
lean_ctor_set(v___x_2581_, 0, v___y_2590_);
v___x_2592_ = v___x_2581_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___y_2590_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2592_);
v___x_2594_ = v___x_2587_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2577_);
v_a_2608_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2584_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2584_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec(v_a_2575_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2617_);
v___x_2619_ = v___x_2577_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2574_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2574_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___redArg___boxed(lean_object* v_e_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Char_reduceBEq___redArg(v_e_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_e_2630_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq(lean_object* v_e_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Char_reduceBEq___redArg(v_e_2637_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBEq___boxed(lean_object* v_e_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Char_reduceBEq(v_e_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_e_2647_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2677_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2678_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2675_, v___x_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27____boxed(lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_();
return v_res_2680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_alloc_closure((void*)(l_Char_reduceBEq___boxed), 9, 0);
v___x_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2685_ = 1;
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_);
v___x_2687_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2684_, v___x_2685_, v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29____boxed(lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_();
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_27_));
v___x_2692_ = 1;
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_29_);
v___x_2694_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2691_, v___x_2692_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31____boxed(lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3820077784____hygCtx___hyg_31_();
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg(lean_object* v_e_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2706_ = ((lean_object*)(l_Char_reduceBNe___redArg___closed__1));
v___x_2707_ = lean_unsigned_to_nat(4u);
v___x_2708_ = l_Lean_Expr_isAppOfArity(v_e_2700_, v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = l_Lean_Expr_appFn_x21(v_e_2700_);
v___x_2712_ = l_Lean_Expr_appArg_x21(v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_Meta_getCharValue_x3f(v___x_2712_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2761_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2761_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2761_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
if (lean_obj_tag(v_a_2714_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2756_; 
v_val_2718_ = lean_ctor_get(v_a_2714_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2714_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2720_ = v_a_2714_;
v_isShared_2721_ = v_isSharedCheck_2756_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_val_2718_);
lean_dec(v_a_2714_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2756_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = l_Lean_Expr_appArg_x21(v_e_2700_);
v___x_2723_ = l_Lean_Meta_getCharValue_x3f(v___x_2722_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2747_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2747_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2747_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___y_2729_; 
if (lean_obj_tag(v_a_2724_) == 1)
{
lean_object* v_val_2738_; uint32_t v___x_2739_; uint32_t v___x_2740_; uint8_t v___x_2741_; 
lean_del_object(v___x_2716_);
v_val_2738_ = lean_ctor_get(v_a_2724_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v_a_2724_, 1);
v___x_2739_ = lean_unbox_uint32(v_val_2718_);
lean_dec(v_val_2718_);
v___x_2740_ = lean_unbox_uint32(v_val_2738_);
lean_dec(v_val_2738_);
v___x_2741_ = lean_uint32_dec_eq(v___x_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
if (v___x_2708_ == 0)
{
goto v___jp_2736_;
}
else
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__6);
v___y_2729_ = v___x_2742_;
goto v___jp_2728_;
}
}
else
{
goto v___jp_2736_;
}
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
lean_del_object(v___x_2726_);
lean_dec(v_a_2724_);
lean_del_object(v___x_2720_);
lean_dec(v_val_2718_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2743_);
v___x_2745_ = v___x_2716_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
v___jp_2728_:
{
lean_object* v___x_2731_; 
lean_inc_ref(v___y_2729_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 0);
lean_ctor_set(v___x_2720_, 0, v___y_2729_);
v___x_2731_ = v___x_2720_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___y_2729_);
v___x_2731_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2731_);
v___x_2733_ = v___x_2726_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
v___jp_2736_:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBoolPred___redArg___closed__3);
v___y_2729_ = v___x_2737_;
goto v___jp_2728_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_del_object(v___x_2720_);
lean_dec(v_val_2718_);
lean_del_object(v___x_2716_);
v_a_2748_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2723_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2723_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v_a_2714_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2757_);
v___x_2759_ = v___x_2716_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2713_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2713_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___redArg___boxed(lean_object* v_e_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Char_reduceBNe___redArg(v_e_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec_ref(v_e_2770_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe(lean_object* v_e_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Char_reduceBNe___redArg(v_e_2777_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceBNe___boxed(lean_object* v_e_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Char_reduceBNe(v_e_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_e_2787_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_(){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2817_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2818_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2815_, v___x_2816_, v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27____boxed(lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_();
return v_res_2820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_alloc_closure((void*)(l_Char_reduceBNe___boxed), 9, 0);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_(){
_start:
{
lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2825_ = 1;
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_);
v___x_2827_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2824_, v___x_2825_, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29____boxed(lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_();
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__111___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_27_));
v___x_2832_ = 1;
v___x_2833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_29_);
v___x_2834_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2831_, v___x_2832_, v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31____boxed(lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_83380857____hygCtx___hyg_31_();
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg(lean_object* v_e_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___x_2843_; 
lean_inc_ref(v_e_2837_);
v___x_2843_ = l_Lean_Meta_getCharValue_x3f(v_e_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2863_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2863_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2863_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_dec_ref(v_e_2837_);
v___x_2848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
else
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2861_; 
v_isSharedCheck_2861_ = !lean_is_exclusive(v_a_2844_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; 
v_unused_2862_ = lean_ctor_get(v_a_2844_, 0);
lean_dec(v_unused_2862_);
v___x_2853_ = v_a_2844_;
v_isShared_2854_ = v_isSharedCheck_2861_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v_a_2844_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2861_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 0);
lean_ctor_set(v___x_2853_, 0, v_e_2837_);
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_e_2837_);
v___x_2856_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2856_);
v___x_2858_ = v___x_2846_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_e_2837_);
v_a_2864_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2843_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2843_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_isValue___redArg___boxed(lean_object* v_e_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Char_isValue___redArg(v_e_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue(lean_object* v_e_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Char_isValue___redArg(v_e_2879_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Char_isValue___boxed(lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Char_isValue(v_e_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_2915_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_2916_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2913_, v___x_2914_, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20____boxed(lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_();
return v_res_2918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_alloc_closure((void*)(l_Char_isValue___boxed), 9, 0);
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_2923_ = 0;
v___x_2924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_);
v___x_2925_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2922_, v___x_2923_, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22____boxed(lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_();
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__116___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_20_));
v___x_2930_ = 0;
v___x_2931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_22_);
v___x_2932_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2929_, v___x_2930_, v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24____boxed(lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3090637354____hygCtx___hyg_24_();
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg(lean_object* v_e_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2939_, v_a_2941_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2997_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2997_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2997_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = l_Lean_Expr_cleanupAnnotations(v_a_2946_);
v___x_2956_ = l_Lean_Expr_isApp(v___x_2955_);
if (v___x_2956_ == 0)
{
lean_dec_ref(v___x_2955_);
goto v___jp_2950_;
}
else
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2955_);
v___x_2958_ = l_Lean_Expr_isApp(v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec_ref(v___x_2957_);
goto v___jp_2950_;
}
else
{
lean_object* v_arg_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v_arg_2959_ = lean_ctor_get(v___x_2957_, 1);
lean_inc_ref(v_arg_2959_);
v___x_2960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2957_);
v___x_2961_ = ((lean_object*)(l_Char_reduceOfNatAux___redArg___closed__1));
v___x_2962_ = l_Lean_Expr_isConstOf(v___x_2960_, v___x_2961_);
lean_dec_ref(v___x_2960_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v_arg_2959_);
goto v___jp_2950_;
}
else
{
lean_object* v___x_2963_; 
lean_del_object(v___x_2948_);
v___x_2963_ = l_Lean_Meta_getNatValue_x3f(v_arg_2959_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec_ref(v_arg_2959_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2988_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
if (lean_obj_tag(v_a_2964_) == 1)
{
lean_object* v_val_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2983_; 
v_val_2968_ = lean_ctor_get(v_a_2964_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_a_2964_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2970_ = v_a_2964_;
v_isShared_2971_ = v_isSharedCheck_2983_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_val_2968_);
lean_dec(v_a_2964_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2983_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint32_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2972_ = l_Char_ofNat(v_val_2968_);
lean_dec(v_val_2968_);
v___x_2973_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_2974_ = lean_uint32_to_nat(v___x_2972_);
v___x_2975_ = l_Lean_mkRawNatLit(v___x_2974_);
v___x_2976_ = l_Lean_Expr_app___override(v___x_2973_, v___x_2975_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2976_);
v___x_2978_ = v___x_2970_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2978_);
v___x_2980_ = v___x_2966_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
lean_dec(v_a_2964_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2984_);
v___x_2986_ = v___x_2966_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2963_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2963_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
v___jp_2950_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2951_);
v___x_2953_ = v___x_2948_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2945_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2945_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___redArg___boxed(lean_object* v_e_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Char_reduceOfNatAux___redArg(v_e_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux(lean_object* v_e_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Char_reduceOfNatAux___redArg(v_e_3013_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceOfNatAux___boxed(lean_object* v_e_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Char_reduceOfNatAux(v_e_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3050_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3051_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3048_, v___x_3049_, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21____boxed(lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_();
return v_res_3053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_alloc_closure((void*)(l_Char_reduceOfNatAux___boxed), 9, 0);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3058_ = 1;
v___x_3059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_);
v___x_3060_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3057_, v___x_3058_, v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23____boxed(lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_();
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_(){
_start:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__121___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_21_));
v___x_3065_ = 1;
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_23_);
v___x_3067_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3064_, v___x_3065_, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25____boxed(lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1474942826____hygCtx___hyg_25_();
return v_res_3069_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__3(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_unsigned_to_nat(65u);
v___x_3076_ = l_Lean_mkRawNatLit(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__4(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__3, &l_Char_reduceDefault___redArg___closed__3_once, _init_l_Char_reduceDefault___redArg___closed__3);
v___x_3078_ = lean_obj_once(&l_Char_reduceToLower___redArg___closed__5, &l_Char_reduceToLower___redArg___closed__5_once, _init_l_Char_reduceToLower___redArg___closed__5);
v___x_3079_ = l_Lean_Expr_app___override(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Char_reduceDefault___redArg___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__4, &l_Char_reduceDefault___redArg___closed__4_once, _init_l_Char_reduceDefault___redArg___closed__4);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg(lean_object* v_e_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3082_, v_a_3083_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3104_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3104_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3104_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3095_ = l_Lean_Expr_cleanupAnnotations(v_a_3086_);
v___x_3096_ = l_Lean_Expr_isApp(v___x_3095_);
if (v___x_3096_ == 0)
{
lean_dec_ref(v___x_3095_);
goto v___jp_3090_;
}
else
{
lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3095_);
v___x_3098_ = l_Lean_Expr_isApp(v___x_3097_);
if (v___x_3098_ == 0)
{
lean_dec_ref(v___x_3097_);
goto v___jp_3090_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3097_);
v___x_3100_ = ((lean_object*)(l_Char_reduceDefault___redArg___closed__2));
v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3099_, v___x_3100_);
lean_dec_ref(v___x_3099_);
if (v___x_3101_ == 0)
{
goto v___jp_3090_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_del_object(v___x_3088_);
v___x_3102_ = lean_obj_once(&l_Char_reduceDefault___redArg___closed__5, &l_Char_reduceDefault___redArg___closed__5_once, _init_l_Char_reduceDefault___redArg___closed__5);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
}
v___jp_3090_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceUnary___redArg___closed__0));
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3091_);
v___x_3093_ = v___x_3088_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3085_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3085_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___redArg___boxed(lean_object* v_e_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Char_reduceDefault___redArg(v_e_3113_, v_a_3114_);
lean_dec(v_a_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault(lean_object* v_e_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Char_reduceDefault___redArg(v_e_3117_, v_a_3122_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Char_reduceDefault___boxed(lean_object* v_e_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Char_reduceDefault(v_e_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3155_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3156_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3153_, v___x_3154_, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22____boxed(lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_();
return v_res_3158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_alloc_closure((void*)(l_Char_reduceDefault___boxed), 9, 0);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3163_ = 1;
v___x_3164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_);
v___x_3165_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3162_, v___x_3163_, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24____boxed(lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_();
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_(){
_start:
{
lean_object* v___x_3169_; uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__126___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_22_));
v___x_3170_ = 1;
v___x_3171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_24_);
v___x_3172_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3169_, v___x_3170_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26____boxed(lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1040352741____hygCtx___hyg_26_();
return v_res_3174_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(uint32_t v_a_3175_, lean_object* v_as_3176_, size_t v_i_3177_, size_t v_stop_3178_){
_start:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_eq(v_i_3177_, v_stop_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; uint32_t v___x_3181_; uint8_t v___x_3182_; 
v___x_3180_ = lean_array_uget_borrowed(v_as_3176_, v_i_3177_);
v___x_3181_ = lean_unbox_uint32(v___x_3180_);
v___x_3182_ = lean_uint32_dec_eq(v_a_3175_, v___x_3181_);
if (v___x_3182_ == 0)
{
size_t v___x_3183_; size_t v___x_3184_; 
v___x_3183_ = ((size_t)1ULL);
v___x_3184_ = lean_usize_add(v_i_3177_, v___x_3183_);
v_i_3177_ = v___x_3184_;
goto _start;
}
else
{
return v___x_3182_;
}
}
else
{
uint8_t v___x_3186_; 
v___x_3186_ = 0;
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0___boxed(lean_object* v_a_3187_, lean_object* v_as_3188_, lean_object* v_i_3189_, lean_object* v_stop_3190_){
_start:
{
uint32_t v_a_boxed_3191_; size_t v_i_boxed_3192_; size_t v_stop_boxed_3193_; uint8_t v_res_3194_; lean_object* v_r_3195_; 
v_a_boxed_3191_ = lean_unbox_uint32(v_a_3187_);
lean_dec(v_a_3187_);
v_i_boxed_3192_ = lean_unbox_usize(v_i_3189_);
lean_dec(v_i_3189_);
v_stop_boxed_3193_ = lean_unbox_usize(v_stop_3190_);
lean_dec(v_stop_3190_);
v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_boxed_3191_, v_as_3188_, v_i_boxed_3192_, v_stop_boxed_3193_);
lean_dec_ref(v_as_3188_);
v_r_3195_ = lean_box(v_res_3194_);
return v_r_3195_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(lean_object* v_as_3196_, uint32_t v_a_3197_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = lean_array_get_size(v_as_3196_);
v___x_3200_ = lean_nat_dec_lt(v___x_3198_, v___x_3199_);
if (v___x_3200_ == 0)
{
return v___x_3200_;
}
else
{
if (v___x_3200_ == 0)
{
return v___x_3200_;
}
else
{
size_t v___x_3201_; size_t v___x_3202_; uint8_t v___x_3203_; 
v___x_3201_ = ((size_t)0ULL);
v___x_3202_ = lean_usize_of_nat(v___x_3199_);
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_3197_, v_as_3196_, v___x_3201_, v___x_3202_);
return v___x_3203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0___boxed(lean_object* v_as_3204_, lean_object* v_a_3205_){
_start:
{
uint32_t v_a_boxed_3206_; uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_a_boxed_3206_ = lean_unbox_uint32(v_a_3205_);
lean_dec(v_a_3205_);
v_res_3207_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v_as_3204_, v_a_boxed_3206_);
lean_dec_ref(v_as_3204_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = 42;
v___x_3215_ = lean_box_uint32(v___x_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2(void){
_start:
{
uint32_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = 102;
v___x_3217_ = lean_box_uint32(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3(void){
_start:
{
uint32_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = 101;
v___x_3219_ = lean_box_uint32(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4(void){
_start:
{
uint32_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = 100;
v___x_3221_ = lean_box_uint32(v___x_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5(void){
_start:
{
uint32_t v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = 99;
v___x_3223_ = lean_box_uint32(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6(void){
_start:
{
uint32_t v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = 98;
v___x_3225_ = lean_box_uint32(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7(void){
_start:
{
uint32_t v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = 97;
v___x_3227_ = lean_box_uint32(v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8(void){
_start:
{
uint32_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = 57;
v___x_3229_ = lean_box_uint32(v___x_3228_);
return v___x_3229_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9(void){
_start:
{
uint32_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = 56;
v___x_3231_ = lean_box_uint32(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10(void){
_start:
{
uint32_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = 55;
v___x_3233_ = lean_box_uint32(v___x_3232_);
return v___x_3233_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11(void){
_start:
{
uint32_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = 54;
v___x_3235_ = lean_box_uint32(v___x_3234_);
return v___x_3235_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12(void){
_start:
{
uint32_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = 53;
v___x_3237_ = lean_box_uint32(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13(void){
_start:
{
uint32_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = 52;
v___x_3239_ = lean_box_uint32(v___x_3238_);
return v___x_3239_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14(void){
_start:
{
uint32_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = 51;
v___x_3241_ = lean_box_uint32(v___x_3240_);
return v___x_3241_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15(void){
_start:
{
uint32_t v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = 50;
v___x_3243_ = lean_box_uint32(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16(void){
_start:
{
uint32_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = 49;
v___x_3245_ = lean_box_uint32(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17(void){
_start:
{
uint32_t v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = 48;
v___x_3247_ = lean_box_uint32(v___x_3246_);
return v___x_3247_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3248_ = lean_unsigned_to_nat(17u);
v___x_3249_ = lean_mk_empty_array_with_capacity(v___x_3248_);
v___x_3250_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17;
v___x_3251_ = lean_array_push(v___x_3249_, v___x_3250_);
v___x_3252_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16;
v___x_3253_ = lean_array_push(v___x_3251_, v___x_3252_);
v___x_3254_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15;
v___x_3255_ = lean_array_push(v___x_3253_, v___x_3254_);
v___x_3256_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14;
v___x_3257_ = lean_array_push(v___x_3255_, v___x_3256_);
v___x_3258_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13;
v___x_3259_ = lean_array_push(v___x_3257_, v___x_3258_);
v___x_3260_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12;
v___x_3261_ = lean_array_push(v___x_3259_, v___x_3260_);
v___x_3262_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11;
v___x_3263_ = lean_array_push(v___x_3261_, v___x_3262_);
v___x_3264_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10;
v___x_3265_ = lean_array_push(v___x_3263_, v___x_3264_);
v___x_3266_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9;
v___x_3267_ = lean_array_push(v___x_3265_, v___x_3266_);
v___x_3268_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8;
v___x_3269_ = lean_array_push(v___x_3267_, v___x_3268_);
v___x_3270_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7;
v___x_3271_ = lean_array_push(v___x_3269_, v___x_3270_);
v___x_3272_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6;
v___x_3273_ = lean_array_push(v___x_3271_, v___x_3272_);
v___x_3274_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5;
v___x_3275_ = lean_array_push(v___x_3273_, v___x_3274_);
v___x_3276_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4;
v___x_3277_ = lean_array_push(v___x_3275_, v___x_3276_);
v___x_3278_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3;
v___x_3279_ = lean_array_push(v___x_3277_, v___x_3278_);
v___x_3280_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2;
v___x_3281_ = lean_array_push(v___x_3279_, v___x_3280_);
v___x_3282_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1;
v___x_3283_ = lean_array_push(v___x_3281_, v___x_3282_);
return v___x_3283_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_box(0);
v___x_3289_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__5));
v___x_3290_ = l_Lean_mkConst(v___x_3289_, v___x_3288_);
return v___x_3290_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__8));
v___x_3296_ = l_Lean_mkConst(v___x_3295_, v___x_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__11));
v___x_3302_ = l_Lean_mkConst(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg(lean_object* v_e_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3309_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3310_ = lean_unsigned_to_nat(3u);
v___x_3311_ = l_Lean_Expr_isAppOfArity(v_e_3303_, v___x_3309_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec_ref(v_e_3303_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; lean_object* v_lhs_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3314_ = l_Lean_Expr_appFn_x21(v_e_3303_);
v_lhs_3315_ = l_Lean_Expr_appArg_x21(v___x_3314_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = l_Lean_Expr_isAppOfArity(v_lhs_3315_, v___x_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_e_3303_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
else
{
lean_object* v_rhs_3321_; lean_object* v___x_3322_; 
v_rhs_3321_ = l_Lean_Expr_appArg_x21(v_e_3303_);
lean_inc_ref(v_rhs_3321_);
v___x_3322_ = l_Lean_Meta_getCharValue_x3f(v_rhs_3321_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3358_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_a_3323_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3353_; 
v_val_3327_ = lean_ctor_get(v_a_3323_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_a_3323_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3329_ = v_a_3323_;
v_isShared_3330_ = v_isSharedCheck_3353_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_val_3327_);
lean_dec(v_a_3323_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3353_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; uint32_t v___x_3332_; uint8_t v___x_3333_; 
v___x_3331_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3332_ = lean_unbox_uint32(v_val_3327_);
lean_dec(v_val_3327_);
v___x_3333_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3334_ = l_Lean_Expr_appArg_x21(v_lhs_3315_);
lean_dec_ref(v_lhs_3315_);
v___x_3335_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3336_ = l_Lean_eagerReflBoolTrue;
v___x_3337_ = l_Lean_mkApp3(v___x_3335_, v___x_3334_, v_rhs_3321_, v___x_3336_);
v___x_3338_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3339_ = l_Lean_mkAppB(v___x_3338_, v_e_3303_, v___x_3337_);
v___x_3340_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3339_);
v___x_3342_ = v___x_3329_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3339_);
v___x_3342_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3343_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3343_, 0, v___x_3340_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*2, v___x_3318_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3344_);
v___x_3346_ = v___x_3325_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_del_object(v___x_3329_);
lean_dec_ref(v_rhs_3321_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_e_3303_);
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3349_);
v___x_3351_ = v___x_3325_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_a_3323_);
lean_dec_ref(v_rhs_3321_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_e_3303_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3354_);
v___x_3356_ = v___x_3325_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v_rhs_3321_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_e_3303_);
v_a_3359_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3322_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3322_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___redArg___boxed(lean_object* v_e_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq(lean_object* v_e_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Char_Nat_reduceDigitCharEq___redArg(v_e_3374_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceDigitCharEq___boxed(lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Char_Nat_reduceDigitCharEq(v_e_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3416_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3417_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3414_, v___x_3415_, v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31____boxed(lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_();
return v_res_3419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_alloc_closure((void*)(l_Char_Nat_reduceDigitCharEq___boxed), 9, 0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3424_ = 1;
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_);
v___x_3426_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3423_, v___x_3424_, v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33____boxed(lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_();
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_(){
_start:
{
lean_object* v___x_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__131___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_31_));
v___x_3431_ = 1;
v___x_3432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_33_);
v___x_3433_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3430_, v___x_3431_, v___x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35____boxed(lean_object* v_a_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2988815265____hygCtx___hyg_35_();
return v_res_3435_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_Level_succ___override(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__2, &l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2);
v___x_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v___x_3442_);
return v___x_3444_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__3, &l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3);
v___x_3446_ = ((lean_object*)(l_Char_Nat_reduceEqDigitChar___redArg___closed__1));
v___x_3447_ = l_Lean_mkConst(v___x_3446_, v___x_3445_);
return v___x_3447_;
}
}
static lean_object* _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = lean_box(0);
v___x_3449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3888730479____hygCtx___hyg_23_));
v___x_3450_ = l_Lean_mkConst(v___x_3449_, v___x_3448_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg(lean_object* v_e_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3457_ = ((lean_object*)(l_Char_reduceEq___redArg___closed__1));
v___x_3458_ = lean_unsigned_to_nat(3u);
v___x_3459_ = l_Lean_Expr_isAppOfArity(v_e_3451_, v___x_3457_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_e_3451_);
v___x_3460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
else
{
lean_object* v_digitCharExpr_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v_digitCharExpr_3462_ = l_Lean_Expr_appArg_x21(v_e_3451_);
v___x_3463_ = ((lean_object*)(l_Char_Nat_reduceDigitCharEq___redArg___closed__2));
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = l_Lean_Expr_isAppOfArity(v_digitCharExpr_3462_, v___x_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v_digitCharExpr_3462_);
lean_dec_ref(v_e_3451_);
v___x_3466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v_charExpr_3469_; lean_object* v___x_3470_; 
v___x_3468_ = l_Lean_Expr_appFn_x21(v_e_3451_);
v_charExpr_3469_ = l_Lean_Expr_appArg_x21(v___x_3468_);
lean_dec_ref(v___x_3468_);
lean_inc_ref(v_charExpr_3469_);
v___x_3470_ = l_Lean_Meta_getCharValue_x3f(v_charExpr_3469_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3509_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3509_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3509_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
if (lean_obj_tag(v_a_3471_) == 1)
{
lean_object* v_val_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3504_; 
v_val_3475_ = lean_ctor_get(v_a_3471_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_a_3471_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3477_ = v_a_3471_;
v_isShared_3478_ = v_isSharedCheck_3504_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_val_3475_);
lean_dec(v_a_3471_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3504_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; uint32_t v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__3, &l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3);
v___x_3480_ = lean_unbox_uint32(v_val_3475_);
lean_dec(v_val_3475_);
v___x_3481_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3482_ = l_Lean_Expr_appArg_x21(v_digitCharExpr_3462_);
v___x_3483_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__6, &l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6);
v___x_3484_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_charExpr_3469_);
v___x_3485_ = l_Lean_mkApp3(v___x_3483_, v___x_3482_, v_charExpr_3469_, v___x_3484_);
v___x_3486_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__4, &l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4);
v___x_3487_ = lean_obj_once(&l_Char_Nat_reduceEqDigitChar___redArg___closed__5, &l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once, _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5);
v___x_3488_ = l_Lean_mkApp4(v___x_3486_, v___x_3487_, v_digitCharExpr_3462_, v_charExpr_3469_, v___x_3485_);
v___x_3489_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__9, &l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9);
v___x_3490_ = l_Lean_mkAppB(v___x_3489_, v_e_3451_, v___x_3488_);
v___x_3491_ = lean_obj_once(&l_Char_Nat_reduceDigitCharEq___redArg___closed__12, &l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once, _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3490_);
v___x_3493_ = v___x_3477_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3490_);
v___x_3493_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3494_, 0, v___x_3491_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*2, v___x_3465_);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3495_);
v___x_3497_ = v___x_3473_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_del_object(v___x_3477_);
lean_dec_ref(v_charExpr_3469_);
lean_dec_ref(v_digitCharExpr_3462_);
lean_dec_ref(v_e_3451_);
v___x_3500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3500_);
v___x_3502_ = v___x_3473_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec(v_a_3471_);
lean_dec_ref(v_charExpr_3469_);
lean_dec_ref(v_digitCharExpr_3462_);
lean_dec_ref(v_e_3451_);
v___x_3505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBinPred___redArg___closed__0));
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3505_);
v___x_3507_ = v___x_3473_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_charExpr_3469_);
lean_dec_ref(v_digitCharExpr_3462_);
lean_dec_ref(v_e_3451_);
v_a_3510_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3470_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3470_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___redArg___boxed(lean_object* v_e_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar(lean_object* v_e_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Char_Nat_reduceEqDigitChar___redArg(v_e_3525_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Char_Nat_reduceEqDigitChar___boxed(lean_object* v_e_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Char_Nat_reduceEqDigitChar(v_e_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_(){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3564_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3565_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3562_, v___x_3563_, v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31____boxed(lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_();
return v_res_3567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_alloc_closure((void*)(l_Char_Nat_reduceEqDigitChar___boxed), 9, 0);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_(){
_start:
{
lean_object* v___x_3571_; uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3572_ = 1;
v___x_3573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_);
v___x_3574_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3571_, v___x_3572_, v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33____boxed(lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_();
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_(){
_start:
{
lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__136___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_31_));
v___x_3579_ = 1;
v___x_3580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_33_);
v___x_3581_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3578_, v___x_3579_, v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35____boxed(lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4167788095____hygCtx___hyg_35_();
return v_res_3583_;
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
