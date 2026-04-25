// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
// Imports: public import Init.Simproc public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util public import Lean.Meta.LitValues public import Lean.Meta.Offset import Lean.Util.SafeExponentiation import Init.Data.Nat.Dvd import Init.Data.Nat.Simproc
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_reduceUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_reduceUnary___redArg___closed__0 = (const lean_object*)&l_Nat_reduceUnary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_reduceBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Nat_reduceBinPred___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBinPred___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Nat_reduceBoolPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Nat_reduceBoolPred___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBoolPred___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceBoolPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Nat_reduceBoolPred___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBoolPred___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceBoolPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Nat_reduceBoolPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Nat_reduceBoolPred___redArg___closed__2 = (const lean_object*)&l_Nat_reduceBoolPred___redArg___closed__2_value;
static lean_once_cell_t l_Nat_reduceBoolPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBoolPred___redArg___closed__3;
static const lean_string_object l_Nat_reduceBoolPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Nat_reduceBoolPred___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBoolPred___redArg___closed__4_value;
static const lean_ctor_object l_Nat_reduceBoolPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Nat_reduceBoolPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Nat_reduceBoolPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Nat_reduceBoolPred___redArg___closed__5 = (const lean_object*)&l_Nat_reduceBoolPred___redArg___closed__5_value;
static lean_once_cell_t l_Nat_reduceBoolPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBoolPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Nat_reduceSucc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Nat_reduceSucc___redArg___closed__0 = (const lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceSucc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Nat_reduceSucc___redArg___closed__1 = (const lean_object*)&l_Nat_reduceSucc___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceSucc___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSucc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSucc___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceSucc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Nat_reduceSucc___redArg___closed__2 = (const lean_object*)&l_Nat_reduceSucc___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceSucc"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(103, 57, 115, 133, 251, 27, 153, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceSucc___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17____boxed(lean_object*);
static const lean_string_object l_Nat_reduceAdd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Nat_reduceAdd___redArg___closed__0 = (const lean_object*)&l_Nat_reduceAdd___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceAdd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Nat_reduceAdd___redArg___closed__1 = (const lean_object*)&l_Nat_reduceAdd___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceAdd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceAdd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Nat_reduceAdd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceAdd___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceAdd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Nat_reduceAdd___redArg___closed__2 = (const lean_object*)&l_Nat_reduceAdd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(209, 55, 73, 242, 185, 51, 64, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAdd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceMul___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Nat_reduceMul___redArg___closed__0 = (const lean_object*)&l_Nat_reduceMul___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceMul___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Nat_reduceMul___redArg___closed__1 = (const lean_object*)&l_Nat_reduceMul___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceMul___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceMul___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Nat_reduceMul___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceMul___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceMul___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Nat_reduceMul___redArg___closed__2 = (const lean_object*)&l_Nat_reduceMul___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(167, 230, 249, 145, 254, 156, 61, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMul___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceSub___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Nat_reduceSub___redArg___closed__0 = (const lean_object*)&l_Nat_reduceSub___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceSub___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Nat_reduceSub___redArg___closed__1 = (const lean_object*)&l_Nat_reduceSub___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceSub___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSub___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Nat_reduceSub___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSub___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceSub___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Nat_reduceSub___redArg___closed__2 = (const lean_object*)&l_Nat_reduceSub___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(171, 95, 24, 58, 17, 176, 174, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceSub___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceDiv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Nat_reduceDiv___redArg___closed__0 = (const lean_object*)&l_Nat_reduceDiv___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceDiv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Nat_reduceDiv___redArg___closed__1 = (const lean_object*)&l_Nat_reduceDiv___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceDiv___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceDiv___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Nat_reduceDiv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceDiv___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceDiv___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Nat_reduceDiv___redArg___closed__2 = (const lean_object*)&l_Nat_reduceDiv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(231, 215, 207, 13, 249, 183, 176, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDiv___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceMod___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Nat_reduceMod___redArg___closed__0 = (const lean_object*)&l_Nat_reduceMod___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceMod___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Nat_reduceMod___redArg___closed__1 = (const lean_object*)&l_Nat_reduceMod___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceMod___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceMod___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Nat_reduceMod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceMod___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceMod___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Nat_reduceMod___redArg___closed__2 = (const lean_object*)&l_Nat_reduceMod___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(183, 226, 154, 210, 11, 244, 146, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceMod___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reducePow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Nat_reducePow___redArg___closed__0 = (const lean_object*)&l_Nat_reducePow___redArg___closed__0_value;
static const lean_string_object l_Nat_reducePow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Nat_reducePow___redArg___closed__1 = (const lean_object*)&l_Nat_reducePow___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reducePow___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reducePow___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Nat_reducePow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reducePow___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reducePow___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Nat_reducePow___redArg___closed__2 = (const lean_object*)&l_Nat_reducePow___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducePow"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(60, 231, 124, 151, 108, 38, 1, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reducePow___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceAnd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l_Nat_reduceAnd___redArg___closed__0 = (const lean_object*)&l_Nat_reduceAnd___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceAnd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l_Nat_reduceAnd___redArg___closed__1 = (const lean_object*)&l_Nat_reduceAnd___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceAnd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceAnd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l_Nat_reduceAnd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceAnd___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceAnd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l_Nat_reduceAnd___redArg___closed__2 = (const lean_object*)&l_Nat_reduceAnd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(148, 61, 72, 84, 221, 248, 138, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceAnd___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceXor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l_Nat_reduceXor___redArg___closed__0 = (const lean_object*)&l_Nat_reduceXor___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceXor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l_Nat_reduceXor___redArg___closed__1 = (const lean_object*)&l_Nat_reduceXor___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceXor___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceXor___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l_Nat_reduceXor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceXor___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceXor___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l_Nat_reduceXor___redArg___closed__2 = (const lean_object*)&l_Nat_reduceXor___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceXor"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(247, 188, 94, 215, 20, 109, 242, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceXor___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HOr"};
static const lean_object* l_Nat_reduceOr___redArg___closed__0 = (const lean_object*)&l_Nat_reduceOr___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hOr"};
static const lean_object* l_Nat_reduceOr___redArg___closed__1 = (const lean_object*)&l_Nat_reduceOr___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceOr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 77, 185, 226, 52, 149, 89, 139)}};
static const lean_ctor_object l_Nat_reduceOr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceOr___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceOr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 86, 165, 237, 21, 139, 25, 132)}};
static const lean_object* l_Nat_reduceOr___redArg___closed__2 = (const lean_object*)&l_Nat_reduceOr___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(221, 174, 173, 61, 215, 145, 106, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceOr___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceShiftLeft___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Nat_reduceShiftLeft___redArg___closed__0 = (const lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceShiftLeft___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Nat_reduceShiftLeft___redArg___closed__1 = (const lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceShiftLeft___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Nat_reduceShiftLeft___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Nat_reduceShiftLeft___redArg___closed__2 = (const lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(207, 233, 59, 9, 218, 201, 108, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftLeft___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceShiftRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l_Nat_reduceShiftRight___redArg___closed__0 = (const lean_object*)&l_Nat_reduceShiftRight___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceShiftRight___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l_Nat_reduceShiftRight___redArg___closed__1 = (const lean_object*)&l_Nat_reduceShiftRight___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceShiftRight___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l_Nat_reduceShiftRight___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l_Nat_reduceShiftRight___redArg___closed__2 = (const lean_object*)&l_Nat_reduceShiftRight___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reduceShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(243, 57, 160, 187, 200, 59, 234, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceShiftRight___redArg___closed__2_value),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceGcd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gcd"};
static const lean_object* l_Nat_reduceGcd___redArg___closed__0 = (const lean_object*)&l_Nat_reduceGcd___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceGcd___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceGcd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceGcd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 94, 240, 174, 21, 113, 54, 0)}};
static const lean_object* l_Nat_reduceGcd___redArg___closed__1 = (const lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceGcd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(82, 32, 179, 68, 111, 80, 212, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceGcd___redArg___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l_Nat_reduceLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Nat_reduceLT___redArg___closed__0 = (const lean_object*)&l_Nat_reduceLT___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Nat_reduceLT___redArg___closed__1 = (const lean_object*)&l_Nat_reduceLT___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Nat_reduceLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLT___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceLT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Nat_reduceLT___redArg___closed__2 = (const lean_object*)&l_Nat_reduceLT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(226, 122, 83, 255, 56, 112, 58, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceLT___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceGT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Nat_reduceGT___redArg___closed__0 = (const lean_object*)&l_Nat_reduceGT___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceGT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Nat_reduceGT___redArg___closed__1 = (const lean_object*)&l_Nat_reduceGT___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceGT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceGT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Nat_reduceGT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceGT___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceGT___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Nat_reduceGT___redArg___closed__2 = (const lean_object*)&l_Nat_reduceGT___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reduceGT"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(188, 136, 66, 184, 194, 15, 6, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Nat_reduceBEq___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBEq___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceBEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Nat_reduceBEq___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBEq___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceBEq___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceBEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Nat_reduceBEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBEq___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceBEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Nat_reduceBEq___redArg___closed__2 = (const lean_object*)&l_Nat_reduceBEq___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(103, 209, 103, 202, 56, 43, 177, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBEq___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBNe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l_Nat_reduceBNe___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBNe___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBNe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceBNe___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l_Nat_reduceBNe___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBNe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceBNe"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(177, 23, 93, 29, 19, 120, 61, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceBNe___redArg___closed__1_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_isValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Nat_isValue___redArg___closed__0 = (const lean_object*)&l_Nat_isValue___redArg___closed__0_value;
static const lean_string_object l_Nat_isValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Nat_isValue___redArg___closed__1 = (const lean_object*)&l_Nat_isValue___redArg___closed__1_value;
static const lean_ctor_object l_Nat_isValue___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_isValue___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Nat_isValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_isValue___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_isValue___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Nat_isValue___redArg___closed__2 = (const lean_object*)&l_Nat_isValue___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(190, 70, 159, 136, 109, 243, 67, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_isValue___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__5_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instSubNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 126, 242, 252, 139, 96, 73, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instBEqOfDecidableEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 219, 5, 21, 176, 98, 250, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instDecidableEqNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 141, 250, 24, 208, 103, 93, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Nat_reduceNatEqExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reduceNatEqExpr___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__0 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__1 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_gt"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__2 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__2_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__3_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__3_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 49, 75, 205, 14, 153, 197, 197)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__3 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__3_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_add_le"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__4 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__4_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__5_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__5_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(151, 221, 155, 114, 230, 4, 170, 85)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__5 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__5_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_gt"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__6 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__7_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__7_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(222, 96, 15, 118, 250, 229, 166, 121)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__7 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__7_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_eq_le"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__8 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__8_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__9_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__9_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(251, 19, 99, 115, 28, 102, 68, 41)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__9 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__9_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_le"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__10 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__10_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__11_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__11_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(63, 34, 5, 84, 182, 212, 65, 53)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__11 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__11_value;
static const lean_string_object l_Nat_reduceNatEqExpr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_eq_add_ge"};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__12 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__12_value;
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__13_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceNatEqExpr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__13_value_aux_1),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(145, 96, 71, 238, 158, 249, 159, 245)}};
static const lean_object* l_Nat_reduceNatEqExpr___redArg___closed__13 = (const lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Nat_reduceEqDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceEqDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceEqDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceEqDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceEqDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceEqDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceEqDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceEqDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceEqDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceEqDiff___redArg___closed__5;
static const lean_string_object l_Nat_reduceEqDiff___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__6 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceEqDiff___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceEqDiff___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__7 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__7_value;
static lean_once_cell_t l_Nat_reduceEqDiff___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceEqDiff___redArg___closed__8;
static const lean_string_object l_Nat_reduceEqDiff___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__9 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__9_value;
static const lean_ctor_object l_Nat_reduceEqDiff___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceEqDiff___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Nat_reduceEqDiff___redArg___closed__10 = (const lean_object*)&l_Nat_reduceEqDiff___redArg___closed__10_value;
static lean_once_cell_t l_Nat_reduceEqDiff___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceEqDiff___redArg___closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceEqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(254, 236, 88, 131, 52, 249, 43, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "beqFalseOfEqFalse"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 37, 109, 252, 57, 80, 240, 250)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBeqDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "beqEqOfEqEq"};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBeqDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 102, 212, 241, 77, 109, 37)}};
static const lean_object* l_Nat_reduceBeqDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBeqDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBeqDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBeqDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(241, 192, 105, 34, 163, 55, 67, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "bneTrueOfEqFalse"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 18, 96, 112, 23, 126, 226, 206)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__1_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__2;
static const lean_string_object l_Nat_reduceBneDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bneEqOfEqEq"};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceBneDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value_aux_1),((lean_object*)&l_Nat_reduceBneDiff___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 158, 215, 107, 79, 237, 39, 137)}};
static const lean_object* l_Nat_reduceBneDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceBneDiff___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceBneDiff___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___redArg___closed__5;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceBneDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(187, 243, 98, 188, 219, 83, 246, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_le"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__0 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 38, 194, 84, 75, 182, 180, 195)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__1 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__1_value;
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_ge"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__2 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__2_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__3_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__3_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 240, 107, 221, 21, 179, 249, 17)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__3 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__3_value;
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_add_le"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__4 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__4_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__5_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__5_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 232, 2, 112, 26, 243, 197, 145)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__5 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__5_value;
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_gt"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__6 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__7_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__7_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(184, 68, 207, 87, 108, 168, 176, 41)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__7 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__7_value;
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_le_le"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__8 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__8_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__9_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__9_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 9, 215, 28, 195, 38, 233, 114)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__9 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__9_value;
static const lean_string_object l_Nat_reduceLTLE___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_le_add_ge"};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__10 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__10_value;
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__11_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceLTLE___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceLTLE___redArg___closed__11_value_aux_1),((lean_object*)&l_Nat_reduceLTLE___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 197, 80, 96, 198, 252, 127, 88)}};
static const lean_object* l_Nat_reduceLTLE___redArg___closed__11 = (const lean_object*)&l_Nat_reduceLTLE___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceLeDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value),LEAN_SCALAR_PTR_LITERAL(46, 217, 224, 205, 36, 202, 222, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24____boxed(lean_object*);
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sub_add_eq_comm"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__0 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 127, 24, 115, 7, 168, 162, 198)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__1 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__1_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "add_sub_le"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__2 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__2_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 216, 225, 85, 93, 18, 232, 126)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__3 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__3_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "add_sub_assoc"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__4 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__4_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__5_value_aux_0),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(159, 186, 201, 236, 181, 193, 225, 53)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__5 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__5_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "add_sub_add_le"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__6 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(3, 51, 84, 134, 180, 46, 92, 43)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__7 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__7_value;
static const lean_string_object l_Nat_reduceSubDiff___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "add_sub_add_ge"};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__8 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value;
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_0),((lean_object*)&l_Nat_reduceNatEqExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 105, 31, 171, 182, 103, 187, 41)}};
static const lean_ctor_object l_Nat_reduceSubDiff___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value_aux_1),((lean_object*)&l_Nat_reduceSubDiff___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(48, 27, 181, 35, 241, 165, 108, 235)}};
static const lean_object* l_Nat_reduceSubDiff___redArg___closed__9 = (const lean_object*)&l_Nat_reduceSubDiff___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reduceSubDiff"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(56, 43, 140, 205, 20, 127, 167, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23____boxed(lean_object*);
static const lean_string_object l_Nat_reduceDvd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Nat_reduceDvd___redArg___closed__0 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__0_value;
static const lean_string_object l_Nat_reduceDvd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Nat_reduceDvd___redArg___closed__1 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__1_value;
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceDvd___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__2_value_aux_0),((lean_object*)&l_Nat_reduceDvd___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Nat_reduceDvd___redArg___closed__2 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__2_value;
static const lean_string_object l_Nat_reduceDvd___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Nat_reduceDvd___redArg___closed__3 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__3_value;
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__4_value_aux_0),((lean_object*)&l_Nat_reduceDvd___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(154, 210, 229, 77, 176, 177, 112, 145)}};
static const lean_object* l_Nat_reduceDvd___redArg___closed__4 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__4_value;
static lean_once_cell_t l_Nat_reduceDvd___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceDvd___redArg___closed__5;
static const lean_string_object l_Nat_reduceDvd___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "dvd_eq_false_of_mod_ne_zero"};
static const lean_object* l_Nat_reduceDvd___redArg___closed__6 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__6_value;
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__7_value_aux_0),((lean_object*)&l_Nat_reduceDvd___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(213, 219, 204, 94, 158, 176, 97, 60)}};
static const lean_object* l_Nat_reduceDvd___redArg___closed__7 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__7_value;
static lean_once_cell_t l_Nat_reduceDvd___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceDvd___redArg___closed__8;
static const lean_string_object l_Nat_reduceDvd___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "dvd_eq_true_of_mod_eq_zero"};
static const lean_object* l_Nat_reduceDvd___redArg___closed__9 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__9_value;
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Nat_reduceDvd___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__10_value_aux_0),((lean_object*)&l_Nat_reduceDvd___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(239, 86, 77, 69, 239, 181, 11, 160)}};
static const lean_object* l_Nat_reduceDvd___redArg___closed__10 = (const lean_object*)&l_Nat_reduceDvd___redArg___closed__10_value;
static lean_once_cell_t l_Nat_reduceDvd___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceDvd___redArg___closed__11;
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceDvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_reduceSucc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value),LEAN_SCALAR_PTR_LITERAL(113, 66, 62, 145, 3, 197, 80, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Nat_reduceDvd___redArg___closed__2_value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getNatValue_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___redArg___boxed(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Nat_fromExpr_x3f___redArg(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec_ref(v_e_8_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f(lean_object* v_e_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_getNatValue_x3f(v_e_15_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Nat_fromExpr_x3f___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Nat_fromExpr_x3f(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_e_25_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg(lean_object* v_declName_37_, lean_object* v_arity_38_, lean_object* v_op_39_, lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_Expr_isAppOfArity(v_e_40_, v_declName_37_, v_arity_38_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec_ref(v_op_39_);
v___x_47_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = l_Lean_Expr_appArg_x21(v_e_40_);
v___x_50_ = l_Lean_Meta_getNatValue_x3f(v___x_49_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec_ref(v___x_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_72_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_72_ == 0)
{
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_72_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_72_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
if (lean_obj_tag(v_a_51_) == 1)
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_67_; 
v_val_55_ = lean_ctor_get(v_a_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_a_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_57_ = v_a_51_;
v_isShared_58_ = v_isSharedCheck_67_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v_a_51_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_67_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_59_ = lean_apply_1(v_op_39_, v_val_55_);
v___x_60_ = l_Lean_mkNatLit(v___x_59_);
if (v_isShared_58_ == 0)
{
lean_ctor_set_tag(v___x_57_, 0);
lean_ctor_set(v___x_57_, 0, v___x_60_);
v___x_62_ = v___x_57_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_60_);
v___x_62_ = v_reuseFailAlloc_66_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_62_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_70_; 
lean_dec(v_a_51_);
lean_dec_ref(v_op_39_);
v___x_68_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_68_);
v___x_70_ = v___x_53_;
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
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_op_39_);
v_a_73_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_50_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_50_);
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
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___redArg___boxed(lean_object* v_declName_81_, lean_object* v_arity_82_, lean_object* v_op_83_, lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Nat_reduceUnary___redArg(v_declName_81_, v_arity_82_, v_op_83_, v_e_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_e_84_);
lean_dec(v_declName_81_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary(lean_object* v_declName_91_, lean_object* v_arity_92_, lean_object* v_op_93_, lean_object* v_e_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_Expr_isAppOfArity(v_e_94_, v_declName_91_, v_arity_92_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec_ref(v_op_93_);
v___x_104_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = l_Lean_Expr_appArg_x21(v_e_94_);
v___x_107_ = l_Lean_Meta_getNatValue_x3f(v___x_106_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec_ref(v___x_106_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_129_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 1)
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_124_; 
v_val_112_ = lean_ctor_get(v_a_108_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_a_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_114_ = v_a_108_;
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v_a_108_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = lean_apply_1(v_op_93_, v_val_112_);
v___x_117_ = l_Lean_mkNatLit(v___x_116_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 0);
lean_ctor_set(v___x_114_, 0, v___x_117_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_119_);
v___x_121_ = v___x_110_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec(v_a_108_);
lean_dec_ref(v_op_93_);
v___x_125_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_125_);
v___x_127_ = v___x_110_;
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
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec_ref(v_op_93_);
v_a_130_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_107_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_107_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceUnary___boxed(lean_object* v_declName_138_, lean_object* v_arity_139_, lean_object* v_op_140_, lean_object* v_e_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Nat_reduceUnary(v_declName_138_, v_arity_139_, v_op_140_, v_e_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_e_141_);
lean_dec(v_declName_138_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg(lean_object* v_declName_151_, lean_object* v_arity_152_, lean_object* v_op_153_, lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_Expr_isAppOfArity(v_e_154_, v_declName_151_, v_arity_152_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec_ref(v_op_153_);
v___x_161_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = l_Lean_Expr_appFn_x21(v_e_154_);
v___x_164_ = l_Lean_Expr_appArg_x21(v___x_163_);
lean_dec_ref(v___x_163_);
v___x_165_ = l_Lean_Meta_getNatValue_x3f(v___x_164_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec_ref(v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_207_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_207_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_207_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_207_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
if (lean_obj_tag(v_a_166_) == 1)
{
lean_object* v_val_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_del_object(v___x_168_);
v_val_170_ = lean_ctor_get(v_a_166_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v_a_166_);
v___x_171_ = l_Lean_Expr_appArg_x21(v_e_154_);
v___x_172_ = l_Lean_Meta_getNatValue_x3f(v___x_171_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec_ref(v___x_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_194_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_194_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
if (lean_obj_tag(v_a_173_) == 1)
{
lean_object* v_val_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_189_; 
v_val_177_ = lean_ctor_get(v_a_173_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_173_);
if (v_isSharedCheck_189_ == 0)
{
v___x_179_ = v_a_173_;
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_val_177_);
lean_dec(v_a_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_181_ = lean_apply_2(v_op_153_, v_val_170_, v_val_177_);
v___x_182_ = l_Lean_mkNatLit(v___x_181_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 0);
lean_ctor_set(v___x_179_, 0, v___x_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_184_);
v___x_186_ = v___x_175_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_a_173_);
lean_dec(v_val_170_);
lean_dec_ref(v_op_153_);
v___x_190_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_190_);
v___x_192_ = v___x_175_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_val_170_);
lean_dec_ref(v_op_153_);
v_a_195_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_172_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_172_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec(v_a_166_);
lean_dec_ref(v_op_153_);
v___x_203_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_203_);
v___x_205_ = v___x_168_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
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
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_op_153_);
v_a_208_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_165_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_165_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___redArg___boxed(lean_object* v_declName_216_, lean_object* v_arity_217_, lean_object* v_op_218_, lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Nat_reduceBin___redArg(v_declName_216_, v_arity_217_, v_op_218_, v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec_ref(v_e_219_);
lean_dec(v_declName_216_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin(lean_object* v_declName_226_, lean_object* v_arity_227_, lean_object* v_op_228_, lean_object* v_e_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_Expr_isAppOfArity(v_e_229_, v_declName_226_, v_arity_227_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v_op_228_);
v___x_239_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = l_Lean_Expr_appFn_x21(v_e_229_);
v___x_242_ = l_Lean_Expr_appArg_x21(v___x_241_);
lean_dec_ref(v___x_241_);
v___x_243_ = l_Lean_Meta_getNatValue_x3f(v___x_242_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec_ref(v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_285_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_285_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_285_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_285_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
if (lean_obj_tag(v_a_244_) == 1)
{
lean_object* v_val_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_del_object(v___x_246_);
v_val_248_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_val_248_);
lean_dec_ref(v_a_244_);
v___x_249_ = l_Lean_Expr_appArg_x21(v_e_229_);
v___x_250_ = l_Lean_Meta_getNatValue_x3f(v___x_249_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec_ref(v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_272_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_272_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_272_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_272_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
if (lean_obj_tag(v_a_251_) == 1)
{
lean_object* v_val_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_267_; 
v_val_255_ = lean_ctor_get(v_a_251_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_a_251_);
if (v_isSharedCheck_267_ == 0)
{
v___x_257_ = v_a_251_;
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_val_255_);
lean_dec(v_a_251_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_apply_2(v_op_228_, v_val_248_, v_val_255_);
v___x_260_ = l_Lean_mkNatLit(v___x_259_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 0);
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_262_ = v___x_257_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_262_);
v___x_264_ = v___x_253_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_dec(v_a_251_);
lean_dec(v_val_248_);
lean_dec_ref(v_op_228_);
v___x_268_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_268_);
v___x_270_ = v___x_253_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
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
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_val_248_);
lean_dec_ref(v_op_228_);
v_a_273_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_250_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_250_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec(v_a_244_);
lean_dec_ref(v_op_228_);
v___x_281_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_281_);
v___x_283_ = v___x_246_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
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
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_op_228_);
v_a_286_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_243_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_243_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBin___boxed(lean_object* v_declName_294_, lean_object* v_arity_295_, lean_object* v_op_296_, lean_object* v_e_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Nat_reduceBin(v_declName_294_, v_arity_295_, v_op_296_, v_e_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_e_297_);
lean_dec(v_declName_294_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg(lean_object* v_declName_309_, lean_object* v_arity_310_, lean_object* v_op_311_, lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_Expr_isAppOfArity(v_e_312_, v_declName_309_, v_arity_310_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v___x_319_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = l_Lean_Expr_appFn_x21(v_e_312_);
v___x_322_ = l_Lean_Expr_appArg_x21(v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_Lean_Meta_getNatValue_x3f(v___x_322_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec_ref(v___x_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_356_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_356_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
if (lean_obj_tag(v_a_324_) == 1)
{
lean_object* v_val_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_del_object(v___x_326_);
v_val_328_ = lean_ctor_get(v_a_324_, 0);
lean_inc(v_val_328_);
lean_dec_ref(v_a_324_);
v___x_329_ = l_Lean_Expr_appArg_x21(v_e_312_);
v___x_330_ = l_Lean_Meta_getNatValue_x3f(v___x_329_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec_ref(v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_343_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_343_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
lean_del_object(v___x_333_);
v_val_335_ = lean_ctor_get(v_a_331_, 0);
lean_inc(v_val_335_);
lean_dec_ref(v_a_331_);
v___x_336_ = lean_apply_2(v_op_311_, v_val_328_, v_val_335_);
v___x_337_ = lean_unbox(v___x_336_);
v___x_338_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_312_, v___x_337_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_a_331_);
lean_dec(v_val_328_);
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v___x_339_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_339_);
v___x_341_ = v___x_333_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_val_328_);
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v_a_344_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_330_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_330_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v_a_324_);
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v___x_352_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_352_);
v___x_354_ = v___x_326_;
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
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_e_312_);
lean_dec_ref(v_op_311_);
v_a_357_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_323_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_323_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___redArg___boxed(lean_object* v_declName_365_, lean_object* v_arity_366_, lean_object* v_op_367_, lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Nat_reduceBinPred___redArg(v_declName_365_, v_arity_366_, v_op_367_, v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_declName_365_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred(lean_object* v_declName_375_, lean_object* v_arity_376_, lean_object* v_op_377_, lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Expr_isAppOfArity(v_e_378_, v_declName_375_, v_arity_376_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v___x_388_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = l_Lean_Expr_appFn_x21(v_e_378_);
v___x_391_ = l_Lean_Expr_appArg_x21(v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = l_Lean_Meta_getNatValue_x3f(v___x_391_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec_ref(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_425_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
if (lean_obj_tag(v_a_393_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_del_object(v___x_395_);
v_val_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_a_393_);
v___x_398_ = l_Lean_Expr_appArg_x21(v_e_378_);
v___x_399_ = l_Lean_Meta_getNatValue_x3f(v___x_398_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec_ref(v___x_398_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_412_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_412_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
if (lean_obj_tag(v_a_400_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; 
lean_del_object(v___x_402_);
v_val_404_ = lean_ctor_get(v_a_400_, 0);
lean_inc(v_val_404_);
lean_dec_ref(v_a_400_);
v___x_405_ = lean_apply_2(v_op_377_, v_val_397_, v_val_404_);
v___x_406_ = lean_unbox(v___x_405_);
v___x_407_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_378_, v___x_406_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec(v_a_400_);
lean_dec(v_val_397_);
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v___x_408_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_408_);
v___x_410_ = v___x_402_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_val_397_);
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v_a_413_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_399_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_399_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v_a_393_);
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v___x_421_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_421_);
v___x_423_ = v___x_395_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_e_378_);
lean_dec_ref(v_op_377_);
v_a_426_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_392_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_392_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBinPred___boxed(lean_object* v_declName_434_, lean_object* v_arity_435_, lean_object* v_op_436_, lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Nat_reduceBinPred(v_declName_434_, v_arity_435_, v_op_436_, v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_declName_434_);
return v_res_446_;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l_Nat_reduceBoolPred___redArg___closed__2));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Nat_reduceBoolPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l_Nat_reduceBoolPred___redArg___closed__5));
v___x_461_ = l_Lean_mkConst(v___x_460_, v___x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg(lean_object* v_declName_462_, lean_object* v_arity_463_, lean_object* v_op_464_, lean_object* v_e_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Lean_Expr_isAppOfArity(v_e_465_, v_declName_462_, v_arity_463_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_op_464_);
v___x_472_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = l_Lean_Expr_appFn_x21(v_e_465_);
v___x_475_ = l_Lean_Expr_appArg_x21(v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = l_Lean_Meta_getNatValue_x3f(v___x_475_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec_ref(v___x_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_522_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_522_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_522_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_522_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
if (lean_obj_tag(v_a_477_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_517_; 
v_val_481_ = lean_ctor_get(v_a_477_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_517_ == 0)
{
v___x_483_ = v_a_477_;
v_isShared_484_ = v_isSharedCheck_517_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_a_477_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_517_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = l_Lean_Expr_appArg_x21(v_e_465_);
v___x_486_ = l_Lean_Meta_getNatValue_x3f(v___x_485_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec_ref(v___x_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_508_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_508_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___y_492_; 
if (lean_obj_tag(v_a_487_) == 1)
{
lean_object* v_val_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
lean_del_object(v___x_479_);
v_val_499_ = lean_ctor_get(v_a_487_, 0);
lean_inc(v_val_499_);
lean_dec_ref(v_a_487_);
v___x_500_ = lean_apply_2(v_op_464_, v_val_481_, v_val_499_);
v___x_501_ = lean_unbox(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_492_ = v___x_502_;
goto v___jp_491_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_492_ = v___x_503_;
goto v___jp_491_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_del_object(v___x_489_);
lean_dec(v_a_487_);
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_dec_ref(v_op_464_);
v___x_504_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_504_);
v___x_506_ = v___x_479_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
v___jp_491_:
{
lean_object* v___x_494_; 
lean_inc_ref(v___y_492_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
lean_ctor_set(v___x_483_, 0, v___y_492_);
v___x_494_ = v___x_483_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___y_492_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_494_);
v___x_496_ = v___x_489_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_del_object(v___x_479_);
lean_dec_ref(v_op_464_);
v_a_509_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_486_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_486_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec(v_a_477_);
lean_dec_ref(v_op_464_);
v___x_518_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_518_);
v___x_520_ = v___x_479_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_op_464_);
v_a_523_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_476_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_476_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___redArg___boxed(lean_object* v_declName_531_, lean_object* v_arity_532_, lean_object* v_op_533_, lean_object* v_e_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Nat_reduceBoolPred___redArg(v_declName_531_, v_arity_532_, v_op_533_, v_e_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_e_534_);
lean_dec(v_declName_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred(lean_object* v_declName_541_, lean_object* v_arity_542_, lean_object* v_op_543_, lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Expr_isAppOfArity(v_e_544_, v_declName_541_, v_arity_542_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_op_543_);
v___x_554_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_Expr_appFn_x21(v_e_544_);
v___x_557_ = l_Lean_Expr_appArg_x21(v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = l_Lean_Meta_getNatValue_x3f(v___x_557_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec_ref(v___x_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_604_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_604_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_604_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_604_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_599_; 
v_val_563_ = lean_ctor_get(v_a_559_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_599_ == 0)
{
v___x_565_ = v_a_559_;
v_isShared_566_ = v_isSharedCheck_599_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_dec(v_a_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_599_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = l_Lean_Expr_appArg_x21(v_e_544_);
v___x_568_ = l_Lean_Meta_getNatValue_x3f(v___x_567_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec_ref(v___x_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_590_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_590_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_590_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_590_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___y_574_; 
if (lean_obj_tag(v_a_569_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
lean_del_object(v___x_561_);
v_val_581_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v_a_569_);
v___x_582_ = lean_apply_2(v_op_543_, v_val_563_, v_val_581_);
v___x_583_ = lean_unbox(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_574_ = v___x_584_;
goto v___jp_573_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_574_ = v___x_585_;
goto v___jp_573_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_del_object(v___x_571_);
lean_dec(v_a_569_);
lean_del_object(v___x_565_);
lean_dec(v_val_563_);
lean_dec_ref(v_op_543_);
v___x_586_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_586_);
v___x_588_ = v___x_561_;
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
v___jp_573_:
{
lean_object* v___x_576_; 
lean_inc_ref(v___y_574_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 0);
lean_ctor_set(v___x_565_, 0, v___y_574_);
v___x_576_ = v___x_565_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___y_574_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_576_);
v___x_578_ = v___x_571_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_del_object(v___x_565_);
lean_dec(v_val_563_);
lean_del_object(v___x_561_);
lean_dec_ref(v_op_543_);
v_a_591_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_568_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_568_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_a_559_);
lean_dec_ref(v_op_543_);
v___x_600_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_600_);
v___x_602_ = v___x_561_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_op_543_);
v_a_605_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_558_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_558_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBoolPred___boxed(lean_object* v_declName_613_, lean_object* v_arity_614_, lean_object* v_op_615_, lean_object* v_e_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Nat_reduceBoolPred(v_declName_613_, v_arity_614_, v_op_615_, v_e_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_e_616_);
lean_dec(v_declName_613_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg(lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = ((lean_object*)(l_Nat_reduceSucc___redArg___closed__2));
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = l_Lean_Expr_isAppOfArity(v_e_631_, v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_Expr_appArg_x21(v_e_631_);
v___x_643_ = l_Lean_Meta_getNatValue_x3f(v___x_642_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec_ref(v___x_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_665_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_665_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
if (lean_obj_tag(v_a_644_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_660_; 
v_val_648_ = lean_ctor_get(v_a_644_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_660_ == 0)
{
v___x_650_ = v_a_644_;
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v_a_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_652_ = lean_nat_add(v_val_648_, v___x_638_);
lean_dec(v_val_648_);
v___x_653_ = l_Lean_mkNatLit(v___x_652_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
lean_ctor_set(v___x_650_, 0, v___x_653_);
v___x_655_ = v___x_650_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_655_);
v___x_657_ = v___x_646_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v_a_644_);
v___x_661_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_661_);
v___x_663_ = v___x_646_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_643_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_643_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___redArg___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Nat_reduceSucc___redArg(v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec_ref(v_e_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc(lean_object* v_e_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Nat_reduceSucc___redArg(v_e_681_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___boxed(lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Nat_reduceSucc(v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_e_691_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_717_ = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
v___x_718_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13____boxed(lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_();
return v_res_720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_725_ = 1;
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_);
v___x_727_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_724_, v___x_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15____boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_732_ = 1;
v___x_733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_);
v___x_734_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_731_, v___x_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17____boxed(lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_749_ = lean_unsigned_to_nat(6u);
v___x_750_ = l_Lean_Expr_isAppOfArity(v_e_742_, v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = l_Lean_Expr_appFn_x21(v_e_742_);
v___x_754_ = l_Lean_Expr_appArg_x21(v___x_753_);
lean_dec_ref(v___x_753_);
v___x_755_ = l_Lean_Meta_getNatValue_x3f(v___x_754_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_797_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_797_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_797_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_797_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
if (lean_obj_tag(v_a_756_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_del_object(v___x_758_);
v_val_760_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_val_760_);
lean_dec_ref(v_a_756_);
v___x_761_ = l_Lean_Expr_appArg_x21(v_e_742_);
v___x_762_ = l_Lean_Meta_getNatValue_x3f(v___x_761_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec_ref(v___x_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_784_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_784_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
if (lean_obj_tag(v_a_763_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
v_val_767_ = lean_ctor_get(v_a_763_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_779_ == 0)
{
v___x_769_ = v_a_763_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v_a_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_nat_add(v_val_760_, v_val_767_);
lean_dec(v_val_767_);
lean_dec(v_val_760_);
v___x_772_ = l_Lean_mkNatLit(v___x_771_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 0);
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_774_);
v___x_776_ = v___x_765_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v_a_763_);
lean_dec(v_val_760_);
v___x_780_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_780_);
v___x_782_ = v___x_765_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_val_760_);
v_a_785_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_762_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_762_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec(v_a_756_);
v___x_793_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_793_);
v___x_795_ = v___x_758_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_755_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_755_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___redArg___boxed(lean_object* v_e_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Nat_reduceAdd___redArg(v_e_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_e_806_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd(lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Nat_reduceAdd___redArg(v_e_813_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___boxed(lean_object* v_e_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Nat_reduceAdd(v_e_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_e_823_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_860_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_861_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_858_, v___x_859_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19____boxed(lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_();
return v_res_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_868_ = 1;
v___x_869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_);
v___x_870_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_867_, v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21____boxed(lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_875_ = 1;
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_);
v___x_877_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_874_, v___x_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23____boxed(lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = ((lean_object*)(l_Nat_reduceMul___redArg___closed__2));
v___x_892_ = lean_unsigned_to_nat(6u);
v___x_893_ = l_Lean_Expr_isAppOfArity(v_e_885_, v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = l_Lean_Expr_appFn_x21(v_e_885_);
v___x_897_ = l_Lean_Expr_appArg_x21(v___x_896_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Lean_Meta_getNatValue_x3f(v___x_897_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec_ref(v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_940_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_940_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_940_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_940_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
if (lean_obj_tag(v_a_899_) == 1)
{
lean_object* v_val_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_del_object(v___x_901_);
v_val_903_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_val_903_);
lean_dec_ref(v_a_899_);
v___x_904_ = l_Lean_Expr_appArg_x21(v_e_885_);
v___x_905_ = l_Lean_Meta_getNatValue_x3f(v___x_904_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec_ref(v___x_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_927_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_927_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_927_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_927_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_val_910_ = lean_ctor_get(v_a_906_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v_a_906_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_a_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = lean_nat_mul(v_val_903_, v_val_910_);
lean_dec(v_val_910_);
lean_dec(v_val_903_);
v___x_915_ = l_Lean_mkNatLit(v___x_914_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 0);
lean_ctor_set(v___x_912_, 0, v___x_915_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_917_);
v___x_919_ = v___x_908_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v_a_906_);
lean_dec(v_val_903_);
v___x_923_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_923_);
v___x_925_ = v___x_908_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_val_903_);
v_a_928_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_905_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_905_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec(v_a_899_);
v___x_936_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_936_);
v___x_938_ = v___x_901_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_898_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_898_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___redArg___boxed(lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Nat_reduceMul___redArg(v_e_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec_ref(v_e_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Nat_reduceMul___redArg(v_e_956_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___boxed(lean_object* v_e_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Nat_reduceMul(v_e_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_e_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_998_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_999_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_996_, v___x_997_, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19____boxed(lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_();
return v_res_1001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_1006_ = 1;
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_);
v___x_1008_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1005_, v___x_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21____boxed(lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_1013_ = 1;
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_);
v___x_1015_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1012_, v___x_1013_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23____boxed(lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg(lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1029_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_1030_ = lean_unsigned_to_nat(6u);
v___x_1031_ = l_Lean_Expr_isAppOfArity(v_e_1023_, v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = l_Lean_Expr_appFn_x21(v_e_1023_);
v___x_1035_ = l_Lean_Expr_appArg_x21(v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_Meta_getNatValue_x3f(v___x_1035_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1078_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1078_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1078_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
if (lean_obj_tag(v_a_1037_) == 1)
{
lean_object* v_val_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_del_object(v___x_1039_);
v_val_1041_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_val_1041_);
lean_dec_ref(v_a_1037_);
v___x_1042_ = l_Lean_Expr_appArg_x21(v_e_1023_);
v___x_1043_ = l_Lean_Meta_getNatValue_x3f(v___x_1042_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v___x_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1065_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1065_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1065_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
if (lean_obj_tag(v_a_1044_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1060_; 
v_val_1048_ = lean_ctor_get(v_a_1044_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1050_ = v_a_1044_;
v_isShared_1051_ = v_isSharedCheck_1060_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_dec(v_a_1044_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1060_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = lean_nat_sub(v_val_1041_, v_val_1048_);
lean_dec(v_val_1048_);
lean_dec(v_val_1041_);
v___x_1053_ = l_Lean_mkNatLit(v___x_1052_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1055_);
v___x_1057_ = v___x_1046_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_a_1044_);
lean_dec(v_val_1041_);
v___x_1061_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1061_);
v___x_1063_ = v___x_1046_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_val_1041_);
v_a_1066_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1043_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1043_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec(v_a_1037_);
v___x_1074_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1074_);
v___x_1076_ = v___x_1039_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
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
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1036_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1036_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___redArg___boxed(lean_object* v_e_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Nat_reduceSub___redArg(v_e_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec_ref(v_e_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub(lean_object* v_e_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Nat_reduceSub___redArg(v_e_1094_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___boxed(lean_object* v_e_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Nat_reduceSub(v_e_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_e_1104_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1136_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1137_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1134_, v___x_1135_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19____boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_();
return v_res_1139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1144_ = 1;
v___x_1145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_);
v___x_1146_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1143_, v___x_1144_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21____boxed(lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1151_ = 1;
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_);
v___x_1153_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1150_, v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23____boxed(lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1167_ = ((lean_object*)(l_Nat_reduceDiv___redArg___closed__2));
v___x_1168_ = lean_unsigned_to_nat(6u);
v___x_1169_ = l_Lean_Expr_isAppOfArity(v_e_1161_, v___x_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = l_Lean_Expr_appFn_x21(v_e_1161_);
v___x_1173_ = l_Lean_Expr_appArg_x21(v___x_1172_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = l_Lean_Meta_getNatValue_x3f(v___x_1173_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec_ref(v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1216_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1216_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1216_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
if (lean_obj_tag(v_a_1175_) == 1)
{
lean_object* v_val_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1177_);
v_val_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_val_1179_);
lean_dec_ref(v_a_1175_);
v___x_1180_ = l_Lean_Expr_appArg_x21(v_e_1161_);
v___x_1181_ = l_Lean_Meta_getNatValue_x3f(v___x_1180_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec_ref(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1203_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1203_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1203_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
if (lean_obj_tag(v_a_1182_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1198_; 
v_val_1186_ = lean_ctor_get(v_a_1182_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1188_ = v_a_1182_;
v_isShared_1189_ = v_isSharedCheck_1198_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v_a_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1198_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1190_ = lean_nat_div(v_val_1179_, v_val_1186_);
lean_dec(v_val_1186_);
lean_dec(v_val_1179_);
v___x_1191_ = l_Lean_mkNatLit(v___x_1190_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1193_);
v___x_1195_ = v___x_1184_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec(v_a_1182_);
lean_dec(v_val_1179_);
v___x_1199_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1199_);
v___x_1201_ = v___x_1184_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_val_1179_);
v_a_1204_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1181_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1181_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec(v_a_1175_);
v___x_1212_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1212_);
v___x_1214_ = v___x_1177_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_a_1217_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1174_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1174_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___redArg___boxed(lean_object* v_e_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Nat_reduceDiv___redArg(v_e_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_e_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv(lean_object* v_e_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Nat_reduceDiv___redArg(v_e_1232_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___boxed(lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Nat_reduceDiv(v_e_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_e_1242_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1274_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1275_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1272_, v___x_1273_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19____boxed(lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_();
return v_res_1277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1282_ = 1;
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_);
v___x_1284_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21____boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1289_ = 1;
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_);
v___x_1291_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23____boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = ((lean_object*)(l_Nat_reduceMod___redArg___closed__2));
v___x_1306_ = lean_unsigned_to_nat(6u);
v___x_1307_ = l_Lean_Expr_isAppOfArity(v_e_1299_, v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = l_Lean_Expr_appFn_x21(v_e_1299_);
v___x_1311_ = l_Lean_Expr_appArg_x21(v___x_1310_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = l_Lean_Meta_getNatValue_x3f(v___x_1311_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec_ref(v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1354_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1354_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1354_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
if (lean_obj_tag(v_a_1313_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_del_object(v___x_1315_);
v_val_1317_ = lean_ctor_get(v_a_1313_, 0);
lean_inc(v_val_1317_);
lean_dec_ref(v_a_1313_);
v___x_1318_ = l_Lean_Expr_appArg_x21(v_e_1299_);
v___x_1319_ = l_Lean_Meta_getNatValue_x3f(v___x_1318_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec_ref(v___x_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1341_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
if (lean_obj_tag(v_a_1320_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1336_; 
v_val_1324_ = lean_ctor_get(v_a_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1326_ = v_a_1320_;
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_dec(v_a_1320_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_nat_mod(v_val_1317_, v_val_1324_);
lean_dec(v_val_1324_);
lean_dec(v_val_1317_);
v___x_1329_ = l_Lean_mkNatLit(v___x_1328_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1331_);
v___x_1333_ = v___x_1322_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec(v_a_1320_);
lean_dec(v_val_1317_);
v___x_1337_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1337_);
v___x_1339_ = v___x_1322_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_val_1317_);
v_a_1342_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1319_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1319_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_a_1313_);
v___x_1350_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1350_);
v___x_1352_ = v___x_1315_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1312_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1312_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___redArg___boxed(lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Nat_reduceMod___redArg(v_e_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_e_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod(lean_object* v_e_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Nat_reduceMod___redArg(v_e_1370_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___boxed(lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Nat_reduceMod(v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_e_1380_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1412_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1413_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1410_, v___x_1411_, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19____boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_();
return v_res_1415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1420_ = 1;
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_);
v___x_1422_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1419_, v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21____boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1427_ = 1;
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_);
v___x_1429_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1426_, v___x_1427_, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23____boxed(lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg(lean_object* v_e_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = l_Lean_Expr_cleanupAnnotations(v_e_1437_);
v___x_1448_ = l_Lean_Expr_isApp(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v___x_1447_);
goto v___jp_1444_;
}
else
{
lean_object* v_arg_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_arg_1449_ = lean_ctor_get(v___x_1447_, 1);
lean_inc_ref(v_arg_1449_);
v___x_1450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1447_);
v___x_1451_ = l_Lean_Expr_isApp(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec_ref(v___x_1450_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v_arg_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_arg_1452_ = lean_ctor_get(v___x_1450_, 1);
lean_inc_ref(v_arg_1452_);
v___x_1453_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1450_);
v___x_1454_ = l_Lean_Expr_isApp(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1453_);
v___x_1456_ = l_Lean_Expr_isApp(v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec_ref(v___x_1455_);
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1455_);
v___x_1458_ = l_Lean_Expr_isApp(v___x_1457_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v___x_1457_);
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1457_);
v___x_1460_ = l_Lean_Expr_isApp(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1459_);
v___x_1462_ = ((lean_object*)(l_Nat_reducePow___redArg___closed__2));
v___x_1463_ = l_Lean_Expr_isConstOf(v___x_1461_, v___x_1462_);
lean_dec_ref(v___x_1461_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v_arg_1452_);
lean_dec_ref(v_arg_1449_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Meta_getNatValue_x3f(v_arg_1452_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec_ref(v_arg_1452_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1526_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1526_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1526_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
if (lean_obj_tag(v_a_1465_) == 1)
{
lean_object* v_val_1469_; lean_object* v___x_1470_; 
lean_del_object(v___x_1467_);
v_val_1469_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_val_1469_);
lean_dec_ref(v_a_1465_);
v___x_1470_ = l_Lean_Meta_getNatValue_x3f(v_arg_1449_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec_ref(v_arg_1449_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1513_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1513_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1513_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_config_1475_; lean_object* v_val_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1473_);
v_config_1475_ = lean_ctor_get(v_a_1438_, 0);
v_val_1476_ = lean_ctor_get(v_a_1471_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1478_ = v_a_1471_;
v_isShared_1479_ = v_isSharedCheck_1508_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_val_1476_);
lean_dec(v_a_1471_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1508_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
uint8_t v_warnExponents_1480_; lean_object* v___x_1481_; 
v_warnExponents_1480_ = lean_ctor_get_uint8(v_config_1475_, sizeof(void*)*3 + 25);
lean_inc(v_val_1476_);
v___x_1481_ = l_Lean_checkExponent(v_val_1476_, v_warnExponents_1480_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1499_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1499_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1499_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_unbox(v_a_1482_);
lean_dec(v_a_1482_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_del_object(v___x_1478_);
lean_dec(v_val_1476_);
lean_dec(v_val_1469_);
v___x_1487_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1491_ = lean_nat_pow(v_val_1469_, v_val_1476_);
lean_dec(v_val_1476_);
lean_dec(v_val_1469_);
v___x_1492_ = l_Lean_mkNatLit(v___x_1491_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1492_);
v___x_1494_ = v___x_1478_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1494_);
v___x_1496_ = v___x_1484_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1478_);
lean_dec(v_val_1476_);
lean_dec(v_val_1469_);
v_a_1500_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1481_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1481_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec(v_a_1471_);
lean_dec(v_val_1469_);
v___x_1509_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1509_);
v___x_1511_ = v___x_1473_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_val_1469_);
v_a_1514_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1470_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1470_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec(v_a_1465_);
lean_dec_ref(v_arg_1449_);
v___x_1522_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1522_);
v___x_1524_ = v___x_1467_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_arg_1449_);
v_a_1527_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1464_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1464_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
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
v___jp_1444_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object* v_e_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Nat_reducePow___redArg(v_e_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec_ref(v_a_1536_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Nat_reducePow___redArg(v_e_1543_, v_a_1545_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* v_e_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Nat_reducePow(v_e_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1585_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1586_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1583_, v___x_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19____boxed(lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
return v_res_1588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1593_ = 1;
v___x_1594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_);
v___x_1595_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1592_, v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21____boxed(lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1600_ = 1;
v___x_1601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_);
v___x_1602_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1599_, v___x_1600_, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23____boxed(lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = ((lean_object*)(l_Nat_reduceAnd___redArg___closed__2));
v___x_1617_ = lean_unsigned_to_nat(6u);
v___x_1618_ = l_Lean_Expr_isAppOfArity(v_e_1610_, v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = l_Lean_Expr_appFn_x21(v_e_1610_);
v___x_1622_ = l_Lean_Expr_appArg_x21(v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = l_Lean_Meta_getNatValue_x3f(v___x_1622_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1665_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1665_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1665_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
if (lean_obj_tag(v_a_1624_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_del_object(v___x_1626_);
v_val_1628_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v_a_1624_);
v___x_1629_ = l_Lean_Expr_appArg_x21(v_e_1610_);
v___x_1630_ = l_Lean_Meta_getNatValue_x3f(v___x_1629_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec_ref(v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1652_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1652_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1652_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
if (lean_obj_tag(v_a_1631_) == 1)
{
lean_object* v_val_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1647_; 
v_val_1635_ = lean_ctor_get(v_a_1631_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1631_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1637_ = v_a_1631_;
v_isShared_1638_ = v_isSharedCheck_1647_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_val_1635_);
lean_dec(v_a_1631_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1647_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_nat_land(v_val_1628_, v_val_1635_);
lean_dec(v_val_1635_);
lean_dec(v_val_1628_);
v___x_1640_ = l_Lean_mkNatLit(v___x_1639_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1642_);
v___x_1644_ = v___x_1633_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec(v_a_1631_);
lean_dec(v_val_1628_);
v___x_1648_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1648_);
v___x_1650_ = v___x_1633_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_val_1628_);
v_a_1653_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1630_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1630_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_a_1624_);
v___x_1661_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1661_);
v___x_1663_ = v___x_1626_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1623_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1623_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object* v_e_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Nat_reduceAnd___redArg(v_e_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec_ref(v_e_1674_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object* v_e_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Nat_reduceAnd___redArg(v_e_1681_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object* v_e_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Nat_reduceAnd(v_e_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_e_1691_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1723_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1724_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1721_, v___x_1722_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19____boxed(lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
return v_res_1726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1731_ = 1;
v___x_1732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_);
v___x_1733_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1730_, v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21____boxed(lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1738_ = 1;
v___x_1739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_);
v___x_1740_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1737_, v___x_1738_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23____boxed(lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = ((lean_object*)(l_Nat_reduceXor___redArg___closed__2));
v___x_1755_ = lean_unsigned_to_nat(6u);
v___x_1756_ = l_Lean_Expr_isAppOfArity(v_e_1748_, v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = l_Lean_Expr_appFn_x21(v_e_1748_);
v___x_1760_ = l_Lean_Expr_appArg_x21(v___x_1759_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Lean_Meta_getNatValue_x3f(v___x_1760_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec_ref(v___x_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1803_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1803_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1803_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
if (lean_obj_tag(v_a_1762_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_del_object(v___x_1764_);
v_val_1766_ = lean_ctor_get(v_a_1762_, 0);
lean_inc(v_val_1766_);
lean_dec_ref(v_a_1762_);
v___x_1767_ = l_Lean_Expr_appArg_x21(v_e_1748_);
v___x_1768_ = l_Lean_Meta_getNatValue_x3f(v___x_1767_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec_ref(v___x_1767_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1790_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1790_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1790_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_a_1769_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1785_; 
v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_a_1769_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1775_ = v_a_1769_;
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_val_1773_);
lean_dec(v_a_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = lean_nat_lxor(v_val_1766_, v_val_1773_);
lean_dec(v_val_1773_);
lean_dec(v_val_1766_);
v___x_1778_ = l_Lean_mkNatLit(v___x_1777_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1780_);
v___x_1782_ = v___x_1771_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_a_1769_);
lean_dec(v_val_1766_);
v___x_1786_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1786_);
v___x_1788_ = v___x_1771_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_val_1766_);
v_a_1791_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1768_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1768_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_dec(v_a_1762_);
v___x_1799_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1799_);
v___x_1801_ = v___x_1764_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
v_a_1804_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1761_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1761_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object* v_e_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Nat_reduceXor___redArg(v_e_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_e_1812_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object* v_e_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Nat_reduceXor___redArg(v_e_1819_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object* v_e_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Nat_reduceXor(v_e_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_e_1829_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1861_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1862_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1859_, v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19____boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
return v_res_1864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1869_ = 1;
v___x_1870_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_);
v___x_1871_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1868_, v___x_1869_, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21____boxed(lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1876_ = 1;
v___x_1877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_);
v___x_1878_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1875_, v___x_1876_, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23____boxed(lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object* v_e_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = ((lean_object*)(l_Nat_reduceOr___redArg___closed__2));
v___x_1893_ = lean_unsigned_to_nat(6u);
v___x_1894_ = l_Lean_Expr_isAppOfArity(v_e_1886_, v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_Expr_appFn_x21(v_e_1886_);
v___x_1898_ = l_Lean_Expr_appArg_x21(v___x_1897_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_Meta_getNatValue_x3f(v___x_1898_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec_ref(v___x_1898_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1941_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1941_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1941_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
if (lean_obj_tag(v_a_1900_) == 1)
{
lean_object* v_val_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_del_object(v___x_1902_);
v_val_1904_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1904_);
lean_dec_ref(v_a_1900_);
v___x_1905_ = l_Lean_Expr_appArg_x21(v_e_1886_);
v___x_1906_ = l_Lean_Meta_getNatValue_x3f(v___x_1905_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1928_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
if (lean_obj_tag(v_a_1907_) == 1)
{
lean_object* v_val_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1923_; 
v_val_1911_ = lean_ctor_get(v_a_1907_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_a_1907_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1913_ = v_a_1907_;
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_val_1911_);
lean_dec(v_a_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1915_ = lean_nat_lor(v_val_1904_, v_val_1911_);
lean_dec(v_val_1911_);
lean_dec(v_val_1904_);
v___x_1916_ = l_Lean_mkNatLit(v___x_1915_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1916_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1918_);
v___x_1920_ = v___x_1909_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec(v_a_1907_);
lean_dec(v_val_1904_);
v___x_1924_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1924_);
v___x_1926_ = v___x_1909_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_val_1904_);
v_a_1929_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1906_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1906_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
lean_dec(v_a_1900_);
v___x_1937_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1937_);
v___x_1939_ = v___x_1902_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1899_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1899_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object* v_e_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Nat_reduceOr___redArg(v_e_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_e_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object* v_e_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Nat_reduceOr___redArg(v_e_1957_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Nat_reduceOr(v_e_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_e_1967_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_1999_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2000_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1997_, v___x_1998_, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19____boxed(lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
return v_res_2002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_2007_ = 1;
v___x_2008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_);
v___x_2009_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2006_, v___x_2007_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21____boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_2014_ = 1;
v___x_2015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_);
v___x_2016_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2013_, v___x_2014_, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23____boxed(lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object* v_e_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = ((lean_object*)(l_Nat_reduceShiftLeft___redArg___closed__2));
v___x_2031_ = lean_unsigned_to_nat(6u);
v___x_2032_ = l_Lean_Expr_isAppOfArity(v_e_2024_, v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = l_Lean_Expr_appFn_x21(v_e_2024_);
v___x_2036_ = l_Lean_Expr_appArg_x21(v___x_2035_);
lean_dec_ref(v___x_2035_);
v___x_2037_ = l_Lean_Meta_getNatValue_x3f(v___x_2036_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec_ref(v___x_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2079_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_del_object(v___x_2040_);
v_val_2042_ = lean_ctor_get(v_a_2038_, 0);
lean_inc(v_val_2042_);
lean_dec_ref(v_a_2038_);
v___x_2043_ = l_Lean_Expr_appArg_x21(v_e_2024_);
v___x_2044_ = l_Lean_Meta_getNatValue_x3f(v___x_2043_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec_ref(v___x_2043_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2066_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2066_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2066_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
if (lean_obj_tag(v_a_2045_) == 1)
{
lean_object* v_val_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2061_; 
v_val_2049_ = lean_ctor_get(v_a_2045_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_a_2045_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2051_ = v_a_2045_;
v_isShared_2052_ = v_isSharedCheck_2061_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_val_2049_);
lean_dec(v_a_2045_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2061_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2053_ = lean_nat_shiftl(v_val_2042_, v_val_2049_);
lean_dec(v_val_2049_);
lean_dec(v_val_2042_);
v___x_2054_ = l_Lean_mkNatLit(v___x_2053_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2056_);
v___x_2058_ = v___x_2047_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec(v_a_2045_);
lean_dec(v_val_2042_);
v___x_2062_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2062_);
v___x_2064_ = v___x_2047_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_val_2042_);
v_a_2067_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2044_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2044_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec(v_a_2038_);
v___x_2075_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2075_);
v___x_2077_ = v___x_2040_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2037_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2037_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object* v_e_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Nat_reduceShiftLeft___redArg(v_e_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_e_2088_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object* v_e_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Nat_reduceShiftLeft___redArg(v_e_2095_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object* v_e_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Nat_reduceShiftLeft(v_e_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_e_2105_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2137_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2138_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2135_, v___x_2136_, v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19____boxed(lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_();
return v_res_2140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2145_ = 1;
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_);
v___x_2147_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2144_, v___x_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21____boxed(lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2152_ = 1;
v___x_2153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_);
v___x_2154_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2151_, v___x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23____boxed(lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = ((lean_object*)(l_Nat_reduceShiftRight___redArg___closed__2));
v___x_2169_ = lean_unsigned_to_nat(6u);
v___x_2170_ = l_Lean_Expr_isAppOfArity(v_e_2162_, v___x_2168_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = l_Lean_Expr_appFn_x21(v_e_2162_);
v___x_2174_ = l_Lean_Expr_appArg_x21(v___x_2173_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_Lean_Meta_getNatValue_x3f(v___x_2174_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec_ref(v___x_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2217_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_del_object(v___x_2178_);
v_val_2180_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2180_);
lean_dec_ref(v_a_2176_);
v___x_2181_ = l_Lean_Expr_appArg_x21(v_e_2162_);
v___x_2182_ = l_Lean_Meta_getNatValue_x3f(v___x_2181_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec_ref(v___x_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2204_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2204_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2204_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
if (lean_obj_tag(v_a_2183_) == 1)
{
lean_object* v_val_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2199_; 
v_val_2187_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2189_ = v_a_2183_;
v_isShared_2190_ = v_isSharedCheck_2199_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_val_2187_);
lean_dec(v_a_2183_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2199_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = lean_nat_shiftr(v_val_2180_, v_val_2187_);
lean_dec(v_val_2187_);
lean_dec(v_val_2180_);
v___x_2192_ = l_Lean_mkNatLit(v___x_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2194_);
v___x_2196_ = v___x_2185_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_dec(v_a_2183_);
lean_dec(v_val_2180_);
v___x_2200_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2200_);
v___x_2202_ = v___x_2185_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_val_2180_);
v_a_2205_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2182_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2182_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec(v_a_2176_);
v___x_2213_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2213_);
v___x_2215_ = v___x_2178_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2175_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2175_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object* v_e_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Nat_reduceShiftRight___redArg(v_e_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec_ref(v_e_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Nat_reduceShiftRight___redArg(v_e_2233_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Nat_reduceShiftRight(v_e_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_e_2243_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2275_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2276_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2273_, v___x_2274_, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19____boxed(lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_();
return v_res_2278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2283_ = 1;
v___x_2284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_);
v___x_2285_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2282_, v___x_2283_, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21____boxed(lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2290_ = 1;
v___x_2291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_);
v___x_2292_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2289_, v___x_2290_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23____boxed(lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2305_ = ((lean_object*)(l_Nat_reduceGcd___redArg___closed__1));
v___x_2306_ = lean_unsigned_to_nat(2u);
v___x_2307_ = l_Lean_Expr_isAppOfArity(v_e_2299_, v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = l_Lean_Expr_appFn_x21(v_e_2299_);
v___x_2311_ = l_Lean_Expr_appArg_x21(v___x_2310_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l_Lean_Meta_getNatValue_x3f(v___x_2311_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec_ref(v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2354_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2354_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2354_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
if (lean_obj_tag(v_a_2313_) == 1)
{
lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_del_object(v___x_2315_);
v_val_2317_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_val_2317_);
lean_dec_ref(v_a_2313_);
v___x_2318_ = l_Lean_Expr_appArg_x21(v_e_2299_);
v___x_2319_ = l_Lean_Meta_getNatValue_x3f(v___x_2318_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec_ref(v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2341_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2341_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2341_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
if (lean_obj_tag(v_a_2320_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2336_; 
v_val_2324_ = lean_ctor_get(v_a_2320_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2326_ = v_a_2320_;
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_a_2320_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = lean_nat_gcd(v_val_2317_, v_val_2324_);
lean_dec(v_val_2324_);
lean_dec(v_val_2317_);
v___x_2329_ = l_Lean_mkNatLit(v___x_2328_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2331_);
v___x_2333_ = v___x_2322_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_dec(v_a_2320_);
lean_dec(v_val_2317_);
v___x_2337_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2337_);
v___x_2339_ = v___x_2322_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_val_2317_);
v_a_2342_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2319_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2319_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
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
lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_dec(v_a_2313_);
v___x_2350_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2350_);
v___x_2352_ = v___x_2315_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2312_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2312_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object* v_e_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Nat_reduceGcd___redArg(v_e_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec_ref(v_e_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object* v_e_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Nat_reduceGcd___redArg(v_e_2370_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* v_e_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Nat_reduceGcd(v_e_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_e_2380_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2407_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2408_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2405_, v___x_2406_, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14____boxed(lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_();
return v_res_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2415_ = 1;
v___x_2416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_);
v___x_2417_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2414_, v___x_2415_, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16____boxed(lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2422_ = 1;
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_);
v___x_2424_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2421_, v___x_2422_, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18____boxed(lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object* v_e_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_2439_ = lean_unsigned_to_nat(4u);
v___x_2440_ = l_Lean_Expr_isAppOfArity(v_e_2432_, v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_e_2432_);
v___x_2441_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = l_Lean_Expr_appFn_x21(v_e_2432_);
v___x_2444_ = l_Lean_Expr_appArg_x21(v___x_2443_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = l_Lean_Meta_getNatValue_x3f(v___x_2444_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec_ref(v___x_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2477_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2477_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2477_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
if (lean_obj_tag(v_a_2446_) == 1)
{
lean_object* v_val_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_del_object(v___x_2448_);
v_val_2450_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_val_2450_);
lean_dec_ref(v_a_2446_);
v___x_2451_ = l_Lean_Expr_appArg_x21(v_e_2432_);
v___x_2452_ = l_Lean_Meta_getNatValue_x3f(v___x_2451_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec_ref(v___x_2451_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2464_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2464_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
if (lean_obj_tag(v_a_2453_) == 1)
{
lean_object* v_val_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; 
lean_del_object(v___x_2455_);
v_val_2457_ = lean_ctor_get(v_a_2453_, 0);
lean_inc(v_val_2457_);
lean_dec_ref(v_a_2453_);
v___x_2458_ = lean_nat_dec_lt(v_val_2450_, v_val_2457_);
lean_dec(v_val_2457_);
lean_dec(v_val_2450_);
v___x_2459_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2432_, v___x_2458_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
return v___x_2459_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_dec(v_a_2453_);
lean_dec(v_val_2450_);
lean_dec_ref(v_e_2432_);
v___x_2460_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2460_);
v___x_2462_ = v___x_2455_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_val_2450_);
lean_dec_ref(v_e_2432_);
v_a_2465_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2452_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2452_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_dec(v_a_2446_);
lean_dec_ref(v_e_2432_);
v___x_2473_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2473_);
v___x_2475_ = v___x_2448_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_e_2432_);
v_a_2478_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2445_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2445_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg___boxed(lean_object* v_e_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Nat_reduceLT___redArg(v_e_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object* v_e_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Nat_reduceLT___redArg(v_e_2493_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object* v_e_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Nat_reduceLT(v_e_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2533_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2534_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2531_, v___x_2532_, v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20____boxed(lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_();
return v_res_2536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2541_ = 1;
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_);
v___x_2543_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2540_, v___x_2541_, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22____boxed(lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2548_ = 1;
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_);
v___x_2550_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2547_, v___x_2548_, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24____boxed(lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object* v_e_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2564_ = ((lean_object*)(l_Nat_reduceGT___redArg___closed__2));
v___x_2565_ = lean_unsigned_to_nat(4u);
v___x_2566_ = l_Lean_Expr_isAppOfArity(v_e_2558_, v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref(v_e_2558_);
v___x_2567_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = l_Lean_Expr_appFn_x21(v_e_2558_);
v___x_2570_ = l_Lean_Expr_appArg_x21(v___x_2569_);
lean_dec_ref(v___x_2569_);
v___x_2571_ = l_Lean_Meta_getNatValue_x3f(v___x_2570_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec_ref(v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2603_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2603_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2603_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
if (lean_obj_tag(v_a_2572_) == 1)
{
lean_object* v_val_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_del_object(v___x_2574_);
v_val_2576_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_val_2576_);
lean_dec_ref(v_a_2572_);
v___x_2577_ = l_Lean_Expr_appArg_x21(v_e_2558_);
v___x_2578_ = l_Lean_Meta_getNatValue_x3f(v___x_2577_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec_ref(v___x_2577_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2590_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_a_2579_) == 1)
{
lean_object* v_val_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
lean_del_object(v___x_2581_);
v_val_2583_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_val_2583_);
lean_dec_ref(v_a_2579_);
v___x_2584_ = lean_nat_dec_lt(v_val_2583_, v_val_2576_);
lean_dec(v_val_2576_);
lean_dec(v_val_2583_);
v___x_2585_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2558_, v___x_2584_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_dec(v_a_2579_);
lean_dec(v_val_2576_);
lean_dec_ref(v_e_2558_);
v___x_2586_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2586_);
v___x_2588_ = v___x_2581_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_val_2576_);
lean_dec_ref(v_e_2558_);
v_a_2591_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2578_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2578_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_a_2572_);
lean_dec_ref(v_e_2558_);
v___x_2599_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2599_);
v___x_2601_ = v___x_2574_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_e_2558_);
v_a_2604_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2571_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2571_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg___boxed(lean_object* v_e_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Nat_reduceGT___redArg(v_e_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object* v_e_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Nat_reduceGT___redArg(v_e_2619_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Nat_reduceGT(v_e_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2646_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2647_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2644_, v___x_2645_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20____boxed(lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_();
return v_res_2649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2654_ = 1;
v___x_2655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_);
v___x_2656_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2653_, v___x_2654_, v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22____boxed(lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2661_ = 1;
v___x_2662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_);
v___x_2663_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2660_, v___x_2661_, v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24____boxed(lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object* v_e_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_2678_ = lean_unsigned_to_nat(4u);
v___x_2679_ = l_Lean_Expr_isAppOfArity(v_e_2671_, v___x_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = l_Lean_Expr_appFn_x21(v_e_2671_);
v___x_2683_ = l_Lean_Expr_appArg_x21(v___x_2682_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = l_Lean_Meta_getNatValue_x3f(v___x_2683_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec_ref(v___x_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2729_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2729_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2729_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
if (lean_obj_tag(v_a_2685_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2724_; 
v_val_2689_ = lean_ctor_get(v_a_2685_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_a_2685_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2691_ = v_a_2685_;
v_isShared_2692_ = v_isSharedCheck_2724_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_val_2689_);
lean_dec(v_a_2685_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2724_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = l_Lean_Expr_appArg_x21(v_e_2671_);
v___x_2694_ = l_Lean_Meta_getNatValue_x3f(v___x_2693_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec_ref(v___x_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2715_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2715_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2715_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___y_2700_; 
if (lean_obj_tag(v_a_2695_) == 1)
{
lean_object* v_val_2707_; uint8_t v___x_2708_; 
lean_del_object(v___x_2687_);
v_val_2707_ = lean_ctor_get(v_a_2695_, 0);
lean_inc(v_val_2707_);
lean_dec_ref(v_a_2695_);
v___x_2708_ = lean_nat_dec_eq(v_val_2689_, v_val_2707_);
lean_dec(v_val_2707_);
lean_dec(v_val_2689_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_2700_ = v___x_2709_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_2700_ = v___x_2710_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_del_object(v___x_2697_);
lean_dec(v_a_2695_);
lean_del_object(v___x_2691_);
lean_dec(v_val_2689_);
v___x_2711_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2711_);
v___x_2713_ = v___x_2687_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
v___jp_2699_:
{
lean_object* v___x_2702_; 
lean_inc_ref(v___y_2700_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2700_);
v___x_2702_ = v___x_2691_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___y_2700_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2702_);
v___x_2704_ = v___x_2697_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2691_);
lean_dec(v_val_2689_);
lean_del_object(v___x_2687_);
v_a_2716_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2694_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2694_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v_a_2685_);
v___x_2725_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2725_);
v___x_2727_ = v___x_2687_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_a_2730_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2684_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2684_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object* v_e_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Nat_reduceBEq___redArg(v_e_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_e_2738_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object* v_e_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Nat_reduceBEq___redArg(v_e_2745_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object* v_e_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Nat_reduceBEq(v_e_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_e_2755_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2785_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2786_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2783_, v___x_2784_, v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20____boxed(lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_();
return v_res_2788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2793_ = 1;
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_);
v___x_2795_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2792_, v___x_2793_, v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22____boxed(lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2800_ = 1;
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_);
v___x_2802_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2799_, v___x_2800_, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24____boxed(lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object* v_e_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2814_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_2815_ = lean_unsigned_to_nat(4u);
v___x_2816_ = l_Lean_Expr_isAppOfArity(v_e_2808_, v___x_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = l_Lean_Expr_appFn_x21(v_e_2808_);
v___x_2820_ = l_Lean_Expr_appArg_x21(v___x_2819_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = l_Lean_Meta_getNatValue_x3f(v___x_2820_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec_ref(v___x_2820_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2867_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2867_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2867_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
if (lean_obj_tag(v_a_2822_) == 1)
{
lean_object* v_val_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2862_; 
v_val_2826_ = lean_ctor_get(v_a_2822_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_a_2822_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2828_ = v_a_2822_;
v_isShared_2829_ = v_isSharedCheck_2862_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_val_2826_);
lean_dec(v_a_2822_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2862_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = l_Lean_Expr_appArg_x21(v_e_2808_);
v___x_2831_ = l_Lean_Meta_getNatValue_x3f(v___x_2830_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec_ref(v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2853_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2853_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2853_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___y_2837_; 
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_val_2846_; uint8_t v___x_2847_; 
lean_del_object(v___x_2824_);
v_val_2846_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2846_);
lean_dec_ref(v_a_2832_);
v___x_2847_ = lean_nat_dec_eq(v_val_2826_, v_val_2846_);
lean_dec(v_val_2846_);
lean_dec(v_val_2826_);
if (v___x_2847_ == 0)
{
if (v___x_2816_ == 0)
{
goto v___jp_2844_;
}
else
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_2837_ = v___x_2848_;
goto v___jp_2836_;
}
}
else
{
goto v___jp_2844_;
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_del_object(v___x_2834_);
lean_dec(v_a_2832_);
lean_del_object(v___x_2828_);
lean_dec(v_val_2826_);
v___x_2849_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2849_);
v___x_2851_ = v___x_2824_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
v___jp_2836_:
{
lean_object* v___x_2839_; 
lean_inc_ref(v___y_2837_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 0);
lean_ctor_set(v___x_2828_, 0, v___y_2837_);
v___x_2839_ = v___x_2828_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___y_2837_);
v___x_2839_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2839_);
v___x_2841_ = v___x_2834_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
v___jp_2844_:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_2837_ = v___x_2845_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_del_object(v___x_2828_);
lean_dec(v_val_2826_);
lean_del_object(v___x_2824_);
v_a_2854_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2831_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2831_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_dec(v_a_2822_);
v___x_2863_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2863_);
v___x_2865_ = v___x_2824_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_a_2868_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2821_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2821_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object* v_e_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Nat_reduceBNe___redArg(v_e_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec_ref(v_e_2876_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object* v_e_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Nat_reduceBNe___redArg(v_e_2883_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object* v_e_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Nat_reduceBNe(v_e_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_e_2893_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2923_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2924_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2921_, v___x_2922_, v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20____boxed(lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_();
return v_res_2926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2931_ = 1;
v___x_2932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_);
v___x_2933_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2930_, v___x_2931_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22____boxed(lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2938_ = 1;
v___x_2939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_);
v___x_2940_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2937_, v___x_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24____boxed(lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object* v_e_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v___x_2951_; 
lean_inc_ref(v_e_2948_);
v___x_2951_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2948_, v_a_2949_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2972_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = l_Lean_Expr_cleanupAnnotations(v_a_2952_);
v___x_2962_ = l_Lean_Expr_isApp(v___x_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v___x_2961_);
lean_dec_ref(v_e_2948_);
goto v___jp_2956_;
}
else
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2961_);
v___x_2964_ = l_Lean_Expr_isApp(v___x_2963_);
if (v___x_2964_ == 0)
{
lean_dec_ref(v___x_2963_);
lean_dec_ref(v_e_2948_);
goto v___jp_2956_;
}
else
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2963_);
v___x_2966_ = l_Lean_Expr_isApp(v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v___x_2965_);
lean_dec_ref(v_e_2948_);
goto v___jp_2956_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2965_);
v___x_2968_ = ((lean_object*)(l_Nat_isValue___redArg___closed__2));
v___x_2969_ = l_Lean_Expr_isConstOf(v___x_2967_, v___x_2968_);
lean_dec_ref(v___x_2967_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v_e_2948_);
goto v___jp_2956_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_del_object(v___x_2954_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_e_2948_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
}
}
}
v___jp_2956_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2957_);
v___x_2959_ = v___x_2954_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_e_2948_);
v_a_2973_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2951_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2951_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object* v_e_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Nat_isValue___redArg(v_e_2981_, v_a_2982_);
lean_dec(v_a_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* v_e_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Nat_isValue___redArg(v_e_2985_, v_a_2990_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object* v_e_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Nat_isValue(v_e_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3024_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3025_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3022_, v___x_3023_, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16____boxed(lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_();
return v_res_3027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3032_ = 1;
v___x_3033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_);
v___x_3034_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3031_, v___x_3032_, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18____boxed(lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx(lean_object* v_x_3037_){
_start:
{
if (lean_obj_tag(v_x_3037_) == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_unsigned_to_nat(1u);
return v___x_3039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___boxed(lean_object* v_x_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx(v_x_3040_);
lean_dec_ref(v_x_3040_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(lean_object* v_t_3042_, lean_object* v_k_3043_){
_start:
{
if (lean_obj_tag(v_t_3042_) == 0)
{
lean_object* v_n_3044_; lean_object* v___x_3045_; 
v_n_3044_ = lean_ctor_get(v_t_3042_, 0);
lean_inc(v_n_3044_);
lean_dec_ref(v_t_3042_);
v___x_3045_ = lean_apply_1(v_k_3043_, v_n_3044_);
return v___x_3045_;
}
else
{
lean_object* v_e_3046_; lean_object* v_o_3047_; lean_object* v_n_3048_; lean_object* v___x_3049_; 
v_e_3046_ = lean_ctor_get(v_t_3042_, 0);
lean_inc_ref(v_e_3046_);
v_o_3047_ = lean_ctor_get(v_t_3042_, 1);
lean_inc_ref(v_o_3047_);
v_n_3048_ = lean_ctor_get(v_t_3042_, 2);
lean_inc(v_n_3048_);
lean_dec_ref(v_t_3042_);
v___x_3049_ = lean_apply_3(v_k_3043_, v_e_3046_, v_o_3047_, v_n_3048_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(lean_object* v_motive_3050_, lean_object* v_ctorIdx_3051_, lean_object* v_t_3052_, lean_object* v_h_3053_, lean_object* v_k_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3052_, v_k_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___boxed(lean_object* v_motive_3056_, lean_object* v_ctorIdx_3057_, lean_object* v_t_3058_, lean_object* v_h_3059_, lean_object* v_k_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(v_motive_3056_, v_ctorIdx_3057_, v_t_3058_, v_h_3059_, v_k_3060_);
lean_dec(v_ctorIdx_3057_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim___redArg(lean_object* v_t_3062_, lean_object* v_const_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3062_, v_const_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim(lean_object* v_motive_3065_, lean_object* v_t_3066_, lean_object* v_h_3067_, lean_object* v_const_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3066_, v_const_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim___redArg(lean_object* v_t_3070_, lean_object* v_offset_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3070_, v_offset_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim(lean_object* v_motive_3073_, lean_object* v_t_3074_, lean_object* v_h_3075_, lean_object* v_offset_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3074_, v_offset_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3092_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3093_ = lean_unsigned_to_nat(6u);
v___x_3094_ = l_Lean_Expr_isAppOfArity(v_e_3086_, v___x_3092_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2));
v___x_3096_ = lean_unsigned_to_nat(4u);
v___x_3097_ = l_Lean_Expr_isAppOfArity(v_e_3086_, v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3));
v___x_3099_ = lean_unsigned_to_nat(2u);
v___x_3100_ = l_Lean_Expr_isAppOfArity(v_e_3086_, v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = ((lean_object*)(l_Nat_reduceSucc___redArg___closed__2));
v___x_3102_ = lean_unsigned_to_nat(1u);
v___x_3103_ = l_Lean_Expr_isAppOfArity(v_e_3086_, v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v_b_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_b_3106_ = l_Lean_Expr_appArg_x21(v_e_3086_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_b_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3102_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = l_Lean_Expr_appArg_x21(v_e_3086_);
v___x_3111_ = l_Lean_Meta_getNatValue_x3f(v___x_3110_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec_ref(v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3134_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3134_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3134_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
if (lean_obj_tag(v_a_3112_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3129_; 
v_val_3116_ = lean_ctor_get(v_a_3112_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3118_ = v_a_3112_;
v_isShared_3119_ = v_isSharedCheck_3129_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_val_3116_);
lean_dec(v_a_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3129_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v_b_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3120_ = l_Lean_Expr_appFn_x21(v_e_3086_);
v_b_3121_ = l_Lean_Expr_appArg_x21(v___x_3120_);
lean_dec_ref(v___x_3120_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_b_3121_);
lean_ctor_set(v___x_3122_, 1, v_val_3116_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3122_);
v___x_3124_ = v___x_3118_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3124_);
v___x_3126_ = v___x_3114_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
lean_dec(v_a_3112_);
v___x_3130_ = lean_box(0);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3130_);
v___x_3132_ = v___x_3114_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_a_3135_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3111_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3111_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v_inst_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3143_ = l_Lean_Expr_appFn_x21(v_e_3086_);
v___x_3144_ = l_Lean_Expr_appFn_x21(v___x_3143_);
v_inst_3145_ = l_Lean_Expr_appArg_x21(v___x_3144_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = l_Lean_Nat_mkInstAdd;
v___x_3147_ = l_Lean_Meta_matchesInstance(v_inst_3145_, v___x_3146_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3189_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3189_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3189_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_dec_ref(v___x_3143_);
v___x_3153_ = lean_box(0);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3153_);
v___x_3155_ = v___x_3150_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_del_object(v___x_3150_);
v___x_3157_ = l_Lean_Expr_appArg_x21(v_e_3086_);
v___x_3158_ = l_Lean_Meta_getNatValue_x3f(v___x_3157_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec_ref(v___x_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3180_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
if (lean_obj_tag(v_a_3159_) == 1)
{
lean_object* v_val_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3175_; 
v_val_3163_ = lean_ctor_get(v_a_3159_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3159_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3165_ = v_a_3159_;
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_val_3163_);
lean_dec(v_a_3159_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3167_ = l_Lean_Expr_appArg_x21(v___x_3143_);
lean_dec_ref(v___x_3143_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_val_3163_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3168_);
v___x_3170_ = v___x_3165_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3172_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3170_);
v___x_3172_ = v___x_3161_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_dec(v_a_3159_);
lean_dec_ref(v___x_3143_);
v___x_3176_ = lean_box(0);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3176_);
v___x_3178_ = v___x_3161_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v___x_3143_);
v_a_3181_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3158_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3158_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___x_3143_);
v_a_3190_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3147_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3147_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_inst_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3198_ = l_Lean_Expr_appFn_x21(v_e_3086_);
v___x_3199_ = l_Lean_Expr_appFn_x21(v___x_3198_);
v_inst_3200_ = l_Lean_Expr_appArg_x21(v___x_3199_);
lean_dec_ref(v___x_3199_);
v___x_3201_ = l_Lean_Nat_mkInstHAdd;
v___x_3202_ = l_Lean_Meta_matchesInstance(v_inst_3200_, v___x_3201_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3244_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3244_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3244_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_unbox(v_a_3203_);
lean_dec(v_a_3203_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_dec_ref(v___x_3198_);
v___x_3208_ = lean_box(0);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3208_);
v___x_3210_ = v___x_3205_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_del_object(v___x_3205_);
v___x_3212_ = l_Lean_Expr_appArg_x21(v_e_3086_);
v___x_3213_ = l_Lean_Meta_getNatValue_x3f(v___x_3212_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec_ref(v___x_3212_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3235_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3235_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3235_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
if (lean_obj_tag(v_a_3214_) == 1)
{
lean_object* v_val_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3230_; 
v_val_3218_ = lean_ctor_get(v_a_3214_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_a_3214_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3220_ = v_a_3214_;
v_isShared_3221_ = v_isSharedCheck_3230_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_val_3218_);
lean_dec(v_a_3214_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3230_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3222_ = l_Lean_Expr_appArg_x21(v___x_3198_);
lean_dec_ref(v___x_3198_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v_val_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3223_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3227_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3225_);
v___x_3227_ = v___x_3216_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_dec(v_a_3214_);
lean_dec_ref(v___x_3198_);
v___x_3231_ = lean_box(0);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3231_);
v___x_3233_ = v___x_3216_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v___x_3198_);
v_a_3236_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3213_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3213_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___x_3198_);
v_a_3245_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3202_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3202_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object* v_e_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec_ref(v_e_3253_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object* v_e_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3260_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object* v_e_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(v_e_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_e_3270_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object* v_e_3280_, lean_object* v_inc_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_e_3287_; lean_object* v___x_3288_; 
v_e_3287_ = l_Lean_Expr_consumeMData(v_e_3280_);
lean_dec_ref(v_e_3280_);
v___x_3288_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3287_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
if (lean_obj_tag(v_a_3289_) == 0)
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_nat_dec_eq(v_inc_3281_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3300_; 
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v___x_3288_, 0);
lean_dec(v_unused_3301_);
v___x_3293_ = v___x_3288_;
v_isShared_3294_ = v_isSharedCheck_3300_;
goto v_resetjp_3292_;
}
else
{
lean_dec(v___x_3288_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3300_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_e_3287_);
lean_ctor_set(v___x_3295_, 1, v_inc_3281_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3296_);
v___x_3298_ = v___x_3293_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
else
{
lean_dec_ref(v_e_3287_);
lean_dec(v_inc_3281_);
return v___x_3288_;
}
}
else
{
lean_object* v_val_3302_; lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v___x_3288_);
lean_dec_ref(v_e_3287_);
v_val_3302_ = lean_ctor_get(v_a_3289_, 0);
lean_inc(v_val_3302_);
lean_dec_ref(v_a_3289_);
v_fst_3303_ = lean_ctor_get(v_val_3302_, 0);
lean_inc(v_fst_3303_);
v_snd_3304_ = lean_ctor_get(v_val_3302_, 1);
lean_inc(v_snd_3304_);
lean_dec(v_val_3302_);
v___x_3305_ = lean_nat_add(v_inc_3281_, v_snd_3304_);
lean_dec(v_snd_3304_);
lean_dec(v_inc_3281_);
v_e_3280_ = v_fst_3303_;
v_inc_3281_ = v___x_3305_;
goto _start;
}
}
else
{
lean_dec_ref(v_e_3287_);
lean_dec(v_inc_3281_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg___boxed(lean_object* v_e_3307_, lean_object* v_inc_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3307_, v_inc_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object* v_e_3315_, lean_object* v_inc_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3315_, v_inc_3316_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object* v_e_3326_, lean_object* v_inc_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(v_e_3326_, v_inc_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object* v_e_3337_, lean_object* v_inc_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_Meta_getNatValue_x3f(v_e_3337_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3395_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3395_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3395_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
if (lean_obj_tag(v_a_3345_) == 0)
{
lean_object* v___x_3349_; 
lean_del_object(v___x_3347_);
v___x_3349_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3337_, v_inc_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3373_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3373_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3373_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
if (lean_obj_tag(v_a_3350_) == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_box(0);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3354_);
v___x_3356_ = v___x_3352_;
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
else
{
lean_object* v_val_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3372_; 
v_val_3358_ = lean_ctor_get(v_a_3350_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_a_3350_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3360_ = v_a_3350_;
v_isShared_3361_ = v_isSharedCheck_3372_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_val_3358_);
lean_dec(v_a_3350_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3372_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
v_fst_3362_ = lean_ctor_get(v_val_3358_, 0);
lean_inc(v_fst_3362_);
v_snd_3363_ = lean_ctor_get(v_val_3358_, 1);
lean_inc_n(v_snd_3363_, 2);
lean_dec(v_val_3358_);
v___x_3364_ = l_Lean_mkNatLit(v_snd_3363_);
v___x_3365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3365_, 0, v_fst_3362_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_ctor_set(v___x_3365_, 2, v_snd_3363_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3365_);
v___x_3367_ = v___x_3360_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3367_);
v___x_3369_ = v___x_3352_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3374_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3349_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3349_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_e_3337_);
v_val_3382_ = lean_ctor_get(v_a_3345_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_a_3345_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3384_ = v_a_3345_;
v_isShared_3385_ = v_isSharedCheck_3394_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v_a_3345_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3394_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3386_ = lean_nat_add(v_val_3382_, v_inc_3338_);
lean_dec(v_inc_3338_);
lean_dec(v_val_3382_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3387_);
v___x_3389_ = v___x_3384_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3389_);
v___x_3391_ = v___x_3347_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_inc_3338_);
lean_dec_ref(v_e_3337_);
v_a_3396_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3344_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3344_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg___boxed(lean_object* v_e_3404_, lean_object* v_inc_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3404_, v_inc_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object* v_e_3412_, lean_object* v_inc_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3412_, v_inc_3413_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object* v_e_3423_, lean_object* v_inc_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(v_e_3423_, v_inc_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
lean_dec(v_a_3425_);
return v_res_3433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_nat_3436_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v_nat_3436_ = l_Lean_mkConst(v___x_3435_, v___x_3434_);
return v_nat_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2));
v___x_3445_ = l_Lean_mkConst(v___x_3444_, v___x_3443_);
return v___x_3445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7(void){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_box(0);
v___x_3450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6));
v___x_3451_ = l_Lean_mkConst(v___x_3450_, v___x_3449_);
return v___x_3451_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8(void){
_start:
{
lean_object* v___x_3452_; lean_object* v_nat_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7);
v_nat_3453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3454_ = lean_unsigned_to_nat(2u);
v___x_3455_ = lean_mk_empty_array_with_capacity(v___x_3454_);
v___x_3456_ = lean_array_push(v___x_3455_, v_nat_3453_);
v___x_3457_ = lean_array_push(v___x_3456_, v___x_3452_);
return v___x_3457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_instHAdd_3460_; 
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8);
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4);
v_instHAdd_3460_ = l_Lean_mkAppN(v___x_3459_, v___x_3458_);
return v_instHAdd_3460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3468_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3469_ = l_Lean_mkConst(v___x_3468_, v___x_3467_);
return v___x_3469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13(void){
_start:
{
lean_object* v_nat_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_nat_3470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3471_ = lean_unsigned_to_nat(6u);
v___x_3472_ = lean_mk_empty_array_with_capacity(v___x_3471_);
v___x_3473_ = lean_array_push(v___x_3472_, v_nat_3470_);
return v___x_3473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14(void){
_start:
{
lean_object* v_nat_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_nat_3474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13);
v___x_3476_ = lean_array_push(v___x_3475_, v_nat_3474_);
return v___x_3476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15(void){
_start:
{
lean_object* v_nat_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_nat_3477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14);
v___x_3479_ = lean_array_push(v___x_3478_, v_nat_3477_);
return v___x_3479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16(void){
_start:
{
lean_object* v_instHAdd_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_instHAdd_3480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9);
v___x_3481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3482_ = lean_array_push(v___x_3481_, v_instHAdd_3480_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object* v_x_3483_, lean_object* v_y_3484_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12);
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16);
v___x_3487_ = lean_array_push(v___x_3486_, v_x_3483_);
v___x_3488_ = lean_array_push(v___x_3487_, v_y_3484_);
v___x_3489_ = l_Lean_mkAppN(v___x_3485_, v___x_3488_);
lean_dec_ref(v___x_3488_);
return v___x_3489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v_instSub_3495_; 
v___x_3493_ = lean_box(0);
v___x_3494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1));
v_instSub_3495_ = l_Lean_mkConst(v___x_3494_, v___x_3493_);
return v_instSub_3495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4));
v___x_3501_ = l_Lean_mkConst(v___x_3500_, v___x_3499_);
return v___x_3501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6(void){
_start:
{
lean_object* v_instSub_3502_; lean_object* v_nat_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_instSub_3502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2);
v_nat_3503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3504_ = lean_unsigned_to_nat(2u);
v___x_3505_ = lean_mk_empty_array_with_capacity(v___x_3504_);
v___x_3506_ = lean_array_push(v___x_3505_, v_nat_3503_);
v___x_3507_ = lean_array_push(v___x_3506_, v_instSub_3502_);
return v___x_3507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_instHSub_3510_; 
v___x_3508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6);
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5);
v_instHSub_3510_ = l_Lean_mkAppN(v___x_3509_, v___x_3508_);
return v_instHSub_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3512_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_3513_ = l_Lean_mkConst(v___x_3512_, v___x_3511_);
return v___x_3513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9(void){
_start:
{
lean_object* v_instHSub_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_instHSub_3514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7);
v___x_3515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3516_ = lean_array_push(v___x_3515_, v_instHSub_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object* v_x_3517_, lean_object* v_y_3518_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8);
v___x_3520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9);
v___x_3521_ = lean_array_push(v___x_3520_, v_x_3517_);
v___x_3522_ = lean_array_push(v___x_3521_, v_y_3518_);
v___x_3523_ = l_Lean_mkAppN(v___x_3519_, v___x_3522_);
lean_dec_ref(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_box(0);
v___x_3528_ = l_Lean_Level_succ___override(v___x_3527_);
return v___x_3528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2);
v___x_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
return v___x_3531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3);
v___x_3533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_3534_ = l_Lean_mkConst(v___x_3533_, v___x_3532_);
return v___x_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3536_ = lean_unsigned_to_nat(3u);
v___x_3537_ = lean_mk_empty_array_with_capacity(v___x_3536_);
v___x_3538_ = lean_array_push(v___x_3537_, v___x_3535_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object* v_x_3539_, lean_object* v_y_3540_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4);
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5);
v___x_3543_ = lean_array_push(v___x_3542_, v_x_3539_);
v___x_3544_ = lean_array_push(v___x_3543_, v_y_3540_);
v___x_3545_ = l_Lean_mkAppN(v___x_3541_, v___x_3544_);
lean_dec_ref(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1));
v___x_3551_ = l_Lean_mkConst(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_box(0);
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4));
v___x_3557_ = l_Lean_mkConst(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3560_ = lean_unsigned_to_nat(2u);
v___x_3561_ = lean_mk_empty_array_with_capacity(v___x_3560_);
v___x_3562_ = lean_array_push(v___x_3561_, v___x_3559_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3558_);
return v___x_3563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6);
v___x_3565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2);
v___x_3566_ = l_Lean_mkAppN(v___x_3565_, v___x_3564_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance(void){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3569_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_3570_ = l_Lean_mkConst(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3572_ = lean_unsigned_to_nat(4u);
v___x_3573_ = lean_mk_empty_array_with_capacity(v___x_3572_);
v___x_3574_ = lean_array_push(v___x_3573_, v___x_3571_);
return v___x_3574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3577_ = lean_array_push(v___x_3576_, v___x_3575_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object* v_x_3578_, lean_object* v_y_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0);
v___x_3581_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3582_ = lean_array_push(v___x_3581_, v_x_3578_);
v___x_3583_ = lean_array_push(v___x_3582_, v_y_3579_);
v___x_3584_ = l_Lean_mkAppN(v___x_3580_, v___x_3583_);
lean_dec_ref(v___x_3583_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3586_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_3587_ = l_Lean_mkConst(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object* v_x_3588_, lean_object* v_y_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0);
v___x_3591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3592_ = lean_array_push(v___x_3591_, v_x_3588_);
v___x_3593_ = lean_array_push(v___x_3592_, v_y_3589_);
v___x_3594_ = l_Lean_mkAppN(v___x_3590_, v___x_3593_);
lean_dec_ref(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_3602_ = l_Lean_Expr_const___override(v___x_3601_, v___x_3600_);
return v___x_3602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = lean_box(0);
v___x_3607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5));
v___x_3608_ = l_Lean_mkConst(v___x_3607_, v___x_3606_);
return v___x_3608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6);
v___x_3610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3611_ = lean_array_push(v___x_3610_, v___x_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* v_x_3612_, lean_object* v_y_3613_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3);
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7);
v___x_3616_ = lean_array_push(v___x_3615_, v_x_3612_);
v___x_3617_ = lean_array_push(v___x_3616_, v_y_3613_);
v___x_3618_ = l_Lean_mkAppN(v___x_3614_, v___x_3617_);
lean_dec_ref(v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* v_x_3619_, lean_object* v_y_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_y_3620_, v_x_3619_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3623_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_3624_ = l_Lean_Expr_const___override(v___x_3623_, v___x_3622_);
return v___x_3624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = lean_box(0);
v___x_3629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2));
v___x_3630_ = l_Lean_mkConst(v___x_3629_, v___x_3628_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3);
v___x_3632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3633_ = lean_array_push(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* v_x_3634_, lean_object* v_y_3635_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0);
v___x_3637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4);
v___x_3638_ = lean_array_push(v___x_3637_, v_x_3634_);
v___x_3639_ = lean_array_push(v___x_3638_, v_y_3635_);
v___x_3640_ = l_Lean_mkAppN(v___x_3636_, v___x_3639_);
lean_dec_ref(v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* v_x_3641_, lean_object* v_y_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_3642_, v_x_3641_);
return v___x_3643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(0);
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1));
v___x_3649_ = l_Lean_mkConst(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* v_p_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; 
lean_inc_ref(v_p_3650_);
v___x_3656_ = l_Lean_Meta_mkDecide(v_p_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___x_3659_ = l_Lean_Meta_mkEqRefl(v___x_3658_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3675_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3675_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3675_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2);
v___x_3665_ = l_Lean_Expr_appArg_x21(v_a_3657_);
lean_dec(v_a_3657_);
v___x_3666_ = lean_unsigned_to_nat(3u);
v___x_3667_ = lean_mk_empty_array_with_capacity(v___x_3666_);
v___x_3668_ = lean_array_push(v___x_3667_, v_p_3650_);
v___x_3669_ = lean_array_push(v___x_3668_, v___x_3665_);
v___x_3670_ = lean_array_push(v___x_3669_, v_a_3660_);
v___x_3671_ = l_Lean_mkAppN(v___x_3664_, v___x_3670_);
lean_dec_ref(v___x_3670_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3671_);
v___x_3673_ = v___x_3662_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_dec(v_a_3657_);
lean_dec_ref(v_p_3650_);
return v___x_3659_;
}
}
else
{
lean_dec_ref(v_p_3650_);
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___boxed(lean_object* v_p_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v_p_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg(lean_object* v_expr_3683_, lean_object* v_nm_3684_, lean_object* v_args_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___x_3688_; lean_object* v_env_3689_; uint8_t v___x_3690_; uint8_t v___x_3691_; 
v___x_3688_ = lean_st_ref_get(v_a_3686_);
v_env_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc_ref(v_env_3689_);
lean_dec(v___x_3688_);
v___x_3690_ = 1;
lean_inc(v_nm_3684_);
v___x_3691_ = l_Lean_Environment_contains(v_env_3689_, v_nm_3684_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_dec(v_nm_3684_);
lean_dec_ref(v_expr_3683_);
v___x_3692_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = l_Lean_mkConst(v_nm_3684_, v___x_3694_);
v___x_3696_ = l_Lean_mkAppN(v___x_3695_, v_args_3685_);
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
v___x_3698_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3698_, 0, v_expr_3683_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*2, v___x_3690_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg___boxed(lean_object* v_expr_3701_, lean_object* v_nm_3702_, lean_object* v_args_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Nat_applySimprocConst___redArg(v_expr_3701_, v_nm_3702_, v_args_3703_, v_a_3704_);
lean_dec(v_a_3704_);
lean_dec_ref(v_args_3703_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object* v_expr_3707_, lean_object* v_nm_3708_, lean_object* v_args_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Nat_applySimprocConst___redArg(v_expr_3707_, v_nm_3708_, v_args_3709_, v_a_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object* v_expr_3719_, lean_object* v_nm_3720_, lean_object* v_args_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Nat_applySimprocConst(v_expr_3719_, v_nm_3720_, v_args_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_args_3721_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx(lean_object* v_x_3731_){
_start:
{
switch(lean_obj_tag(v_x_3731_))
{
case 0:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_unsigned_to_nat(0u);
return v___x_3732_;
}
case 1:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_unsigned_to_nat(1u);
return v___x_3733_;
}
default: 
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_unsigned_to_nat(2u);
return v___x_3734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx___boxed(lean_object* v_x_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Nat_EqResult_ctorIdx(v_x_3735_);
lean_dec_ref(v_x_3735_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___redArg(lean_object* v_t_3737_, lean_object* v_k_3738_){
_start:
{
switch(lean_obj_tag(v_t_3737_))
{
case 0:
{
uint8_t v_b_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_b_3739_ = lean_ctor_get_uint8(v_t_3737_, 0);
lean_dec_ref(v_t_3737_);
v___x_3740_ = lean_box(v_b_3739_);
v___x_3741_ = lean_apply_1(v_k_3738_, v___x_3740_);
return v___x_3741_;
}
case 1:
{
lean_object* v_p_3742_; lean_object* v___x_3743_; 
v_p_3742_ = lean_ctor_get(v_t_3737_, 0);
lean_inc_ref(v_p_3742_);
lean_dec_ref(v_t_3737_);
v___x_3743_ = lean_apply_1(v_k_3738_, v_p_3742_);
return v___x_3743_;
}
default: 
{
lean_object* v_x_3744_; lean_object* v_y_3745_; lean_object* v_p_3746_; lean_object* v___x_3747_; 
v_x_3744_ = lean_ctor_get(v_t_3737_, 0);
lean_inc_ref(v_x_3744_);
v_y_3745_ = lean_ctor_get(v_t_3737_, 1);
lean_inc_ref(v_y_3745_);
v_p_3746_ = lean_ctor_get(v_t_3737_, 2);
lean_inc_ref(v_p_3746_);
lean_dec_ref(v_t_3737_);
v___x_3747_ = lean_apply_3(v_k_3738_, v_x_3744_, v_y_3745_, v_p_3746_);
return v___x_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim(lean_object* v_motive_3748_, lean_object* v_ctorIdx_3749_, lean_object* v_t_3750_, lean_object* v_h_3751_, lean_object* v_k_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Nat_EqResult_ctorElim___redArg(v_t_3750_, v_k_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___boxed(lean_object* v_motive_3754_, lean_object* v_ctorIdx_3755_, lean_object* v_t_3756_, lean_object* v_h_3757_, lean_object* v_k_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Nat_EqResult_ctorElim(v_motive_3754_, v_ctorIdx_3755_, v_t_3756_, v_h_3757_, v_k_3758_);
lean_dec(v_ctorIdx_3755_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim___redArg(lean_object* v_t_3760_, lean_object* v_decide_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Nat_EqResult_ctorElim___redArg(v_t_3760_, v_decide_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim(lean_object* v_motive_3763_, lean_object* v_t_3764_, lean_object* v_h_3765_, lean_object* v_decide_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Nat_EqResult_ctorElim___redArg(v_t_3764_, v_decide_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim___redArg(lean_object* v_t_3768_, lean_object* v_false_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Nat_EqResult_ctorElim___redArg(v_t_3768_, v_false_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim(lean_object* v_motive_3771_, lean_object* v_t_3772_, lean_object* v_h_3773_, lean_object* v_false_3774_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Nat_EqResult_ctorElim___redArg(v_t_3772_, v_false_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim___redArg(lean_object* v_t_3776_, lean_object* v_eq_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Nat_EqResult_ctorElim___redArg(v_t_3776_, v_eq_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim(lean_object* v_motive_3779_, lean_object* v_t_3780_, lean_object* v_h_3781_, lean_object* v_eq_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Nat_EqResult_ctorElim___redArg(v_t_3780_, v_eq_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg(lean_object* v_e_3784_, lean_object* v_lemmaName_3785_, lean_object* v_args_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v___x_3789_; lean_object* v_env_3790_; uint8_t v___x_3791_; uint8_t v___x_3792_; 
v___x_3789_ = lean_st_ref_get(v_a_3787_);
v_env_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc_ref(v_env_3790_);
lean_dec(v___x_3789_);
v___x_3791_ = 1;
lean_inc(v_lemmaName_3785_);
v___x_3792_ = l_Lean_Environment_contains(v_env_3790_, v_lemmaName_3785_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_lemmaName_3785_);
lean_dec_ref(v_e_3784_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3795_ = lean_box(0);
v___x_3796_ = l_Lean_mkConst(v_lemmaName_3785_, v___x_3795_);
v___x_3797_ = l_Lean_mkAppN(v___x_3796_, v_args_3786_);
v___x_3798_ = lean_apply_1(v_e_3784_, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg___boxed(lean_object* v_e_3801_, lean_object* v_lemmaName_3802_, lean_object* v_args_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Nat_applyEqLemma___redArg(v_e_3801_, v_lemmaName_3802_, v_args_3803_, v_a_3804_);
lean_dec(v_a_3804_);
lean_dec_ref(v_args_3803_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object* v_e_3807_, lean_object* v_lemmaName_3808_, lean_object* v_args_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Nat_applyEqLemma___redArg(v_e_3807_, v_lemmaName_3808_, v_args_3809_, v_a_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object* v_e_3819_, lean_object* v_lemmaName_3820_, lean_object* v_args_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Nat_applyEqLemma(v_e_3819_, v_lemmaName_3820_, v_args_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_args_3821_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__0(lean_object* v_p_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_p_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1(lean_object* v_n_3833_, lean_object* v_n_3834_, lean_object* v_e_3835_, lean_object* v_p_3836_){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_nat_sub(v_n_3833_, v_n_3834_);
v___x_3838_ = l_Lean_mkNatLit(v___x_3837_);
v___x_3839_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3839_, 0, v_e_3835_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
lean_ctor_set(v___x_3839_, 2, v_p_3836_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1___boxed(lean_object* v_n_3840_, lean_object* v_n_3841_, lean_object* v_e_3842_, lean_object* v_p_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Nat_reduceNatEqExpr___redArg___lam__1(v_n_3840_, v_n_3841_, v_e_3842_, v_p_3843_);
lean_dec(v_n_3841_);
lean_dec(v_n_3840_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__4(lean_object* v___x_3845_, lean_object* v_e_3846_, lean_object* v_p_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3845_);
lean_ctor_set(v___x_3848_, 1, v_e_3846_);
lean_ctor_set(v___x_3848_, 2, v_p_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__2(lean_object* v_e_3849_, lean_object* v___y_3850_, lean_object* v_p_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3852_, 0, v_e_3849_);
lean_ctor_set(v___x_3852_, 1, v___y_3850_);
lean_ctor_set(v___x_3852_, 2, v_p_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg(lean_object* v_x_3885_, lean_object* v_y_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_x_3885_);
v___x_3893_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_3885_, v___x_3892_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_4085_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_4085_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_4085_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_a_3894_) == 1)
{
lean_object* v_val_3898_; lean_object* v___x_3899_; 
lean_del_object(v___x_3896_);
v_val_3898_ = lean_ctor_get(v_a_3894_, 0);
lean_inc(v_val_3898_);
lean_dec_ref(v_a_3894_);
lean_inc_ref(v_y_3886_);
v___x_3899_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_3886_, v___x_3892_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_4072_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_4072_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_4072_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
if (lean_obj_tag(v_a_3900_) == 1)
{
if (lean_obj_tag(v_val_3898_) == 0)
{
lean_object* v_val_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v_y_3886_);
v_val_3904_ = lean_ctor_get(v_a_3900_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_a_3900_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3906_ = v_a_3900_;
v_isShared_3907_ = v_isSharedCheck_3963_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_val_3904_);
lean_dec(v_a_3900_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3963_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
if (lean_obj_tag(v_val_3904_) == 0)
{
lean_object* v_n_3908_; lean_object* v_n_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec_ref(v_x_3885_);
v_n_3908_ = lean_ctor_get(v_val_3898_, 0);
lean_inc(v_n_3908_);
lean_dec_ref(v_val_3898_);
v_n_3909_ = lean_ctor_get(v_val_3904_, 0);
lean_inc(v_n_3909_);
lean_dec_ref(v_val_3904_);
v___x_3910_ = lean_nat_dec_eq(v_n_3908_, v_n_3909_);
lean_dec(v_n_3909_);
lean_dec(v_n_3908_);
v___x_3911_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3911_, 0, v___x_3910_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3911_);
v___x_3913_ = v___x_3906_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3913_);
v___x_3915_ = v___x_3902_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
else
{
lean_object* v_n_3918_; lean_object* v_e_3919_; lean_object* v_o_3920_; lean_object* v_n_3921_; uint8_t v___x_3922_; 
lean_del_object(v___x_3906_);
lean_del_object(v___x_3902_);
v_n_3918_ = lean_ctor_get(v_val_3898_, 0);
lean_inc(v_n_3918_);
lean_dec_ref(v_val_3898_);
v_e_3919_ = lean_ctor_get(v_val_3904_, 0);
lean_inc_ref(v_e_3919_);
v_o_3920_ = lean_ctor_get(v_val_3904_, 1);
lean_inc_ref(v_o_3920_);
v_n_3921_ = lean_ctor_get(v_val_3904_, 2);
lean_inc(v_n_3921_);
lean_dec_ref(v_val_3904_);
v___x_3922_ = lean_nat_dec_le(v_n_3921_, v_n_3918_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec(v_n_3921_);
lean_dec(v_n_3918_);
lean_inc_ref(v_o_3920_);
lean_inc_ref(v_x_3885_);
v___x_3923_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_x_3885_, v_o_3920_);
v___x_3924_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3923_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3924_);
v___f_3926_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__0));
v___x_3927_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__3));
v___x_3928_ = lean_unsigned_to_nat(4u);
v___x_3929_ = lean_mk_empty_array_with_capacity(v___x_3928_);
v___x_3930_ = lean_array_push(v___x_3929_, v_x_3885_);
v___x_3931_ = lean_array_push(v___x_3930_, v_e_3919_);
v___x_3932_ = lean_array_push(v___x_3931_, v_o_3920_);
v___x_3933_ = lean_array_push(v___x_3932_, v_a_3925_);
v___x_3934_ = l_Nat_applyEqLemma___redArg(v___f_3926_, v___x_3927_, v___x_3933_, v_a_3890_);
lean_dec_ref(v___x_3933_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_o_3920_);
lean_dec_ref(v_e_3919_);
lean_dec_ref(v_x_3885_);
v_a_3935_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3924_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3924_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_inc_ref(v_x_3885_);
lean_inc_ref(v_o_3920_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_3920_, v_x_3885_);
v___x_3944_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3943_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___f_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v___x_3944_);
lean_inc_ref(v_e_3919_);
v___f_3946_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3946_, 0, v_n_3918_);
lean_closure_set(v___f_3946_, 1, v_n_3921_);
lean_closure_set(v___f_3946_, 2, v_e_3919_);
v___x_3947_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__5));
v___x_3948_ = lean_unsigned_to_nat(4u);
v___x_3949_ = lean_mk_empty_array_with_capacity(v___x_3948_);
v___x_3950_ = lean_array_push(v___x_3949_, v_x_3885_);
v___x_3951_ = lean_array_push(v___x_3950_, v_e_3919_);
v___x_3952_ = lean_array_push(v___x_3951_, v_o_3920_);
v___x_3953_ = lean_array_push(v___x_3952_, v_a_3945_);
v___x_3954_ = l_Nat_applyEqLemma___redArg(v___f_3946_, v___x_3947_, v___x_3953_, v_a_3890_);
lean_dec_ref(v___x_3953_);
return v___x_3954_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_n_3921_);
lean_dec_ref(v_o_3920_);
lean_dec_ref(v_e_3919_);
lean_dec(v_n_3918_);
lean_dec_ref(v_x_3885_);
v_a_3955_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3944_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3944_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_3964_; 
lean_del_object(v___x_3902_);
lean_dec_ref(v_x_3885_);
v_val_3964_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_val_3964_);
lean_dec_ref(v_a_3900_);
if (lean_obj_tag(v_val_3964_) == 0)
{
lean_object* v_e_3965_; lean_object* v_o_3966_; lean_object* v_n_3967_; lean_object* v_n_3968_; uint8_t v___x_3969_; 
v_e_3965_ = lean_ctor_get(v_val_3898_, 0);
lean_inc_ref(v_e_3965_);
v_o_3966_ = lean_ctor_get(v_val_3898_, 1);
lean_inc_ref(v_o_3966_);
v_n_3967_ = lean_ctor_get(v_val_3898_, 2);
lean_inc(v_n_3967_);
lean_dec_ref(v_val_3898_);
v_n_3968_ = lean_ctor_get(v_val_3964_, 0);
lean_inc(v_n_3968_);
lean_dec_ref(v_val_3964_);
v___x_3969_ = lean_nat_dec_le(v_n_3967_, v_n_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec(v_n_3968_);
lean_dec(v_n_3967_);
lean_inc_ref(v_o_3966_);
lean_inc_ref(v_y_3886_);
v___x_3970_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_3886_, v_o_3966_);
v___x_3971_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3970_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___f_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref(v___x_3971_);
v___f_3973_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__0));
v___x_3974_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__7));
v___x_3975_ = lean_unsigned_to_nat(4u);
v___x_3976_ = lean_mk_empty_array_with_capacity(v___x_3975_);
v___x_3977_ = lean_array_push(v___x_3976_, v_e_3965_);
v___x_3978_ = lean_array_push(v___x_3977_, v_o_3966_);
v___x_3979_ = lean_array_push(v___x_3978_, v_y_3886_);
v___x_3980_ = lean_array_push(v___x_3979_, v_a_3972_);
v___x_3981_ = l_Nat_applyEqLemma___redArg(v___f_3973_, v___x_3974_, v___x_3980_, v_a_3890_);
lean_dec_ref(v___x_3980_);
return v___x_3981_;
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_o_3966_);
lean_dec_ref(v_e_3965_);
lean_dec_ref(v_y_3886_);
v_a_3982_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3971_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3971_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_inc_ref(v_y_3886_);
lean_inc_ref(v_o_3966_);
v___x_3990_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_3966_, v_y_3886_);
v___x_3991_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3990_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref(v___x_3991_);
lean_inc_ref(v_e_3965_);
v___f_3993_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3993_, 0, v_n_3968_);
lean_closure_set(v___f_3993_, 1, v_n_3967_);
lean_closure_set(v___f_3993_, 2, v_e_3965_);
v___x_3994_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__9));
v___x_3995_ = lean_unsigned_to_nat(4u);
v___x_3996_ = lean_mk_empty_array_with_capacity(v___x_3995_);
v___x_3997_ = lean_array_push(v___x_3996_, v_e_3965_);
v___x_3998_ = lean_array_push(v___x_3997_, v_o_3966_);
v___x_3999_ = lean_array_push(v___x_3998_, v_y_3886_);
v___x_4000_ = lean_array_push(v___x_3999_, v_a_3992_);
v___x_4001_ = l_Nat_applyEqLemma___redArg(v___f_3993_, v___x_3994_, v___x_4000_, v_a_3890_);
lean_dec_ref(v___x_4000_);
return v___x_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_n_3968_);
lean_dec(v_n_3967_);
lean_dec_ref(v_o_3966_);
lean_dec_ref(v_e_3965_);
lean_dec_ref(v_y_3886_);
v_a_4002_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3991_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3991_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
else
{
lean_object* v_e_4010_; lean_object* v_o_4011_; lean_object* v_n_4012_; lean_object* v_e_4013_; lean_object* v_o_4014_; lean_object* v_n_4015_; lean_object* v___y_4017_; uint8_t v___x_4039_; 
lean_dec_ref(v_y_3886_);
v_e_4010_ = lean_ctor_get(v_val_3898_, 0);
lean_inc_ref(v_e_4010_);
v_o_4011_ = lean_ctor_get(v_val_3898_, 1);
lean_inc_ref(v_o_4011_);
v_n_4012_ = lean_ctor_get(v_val_3898_, 2);
lean_inc(v_n_4012_);
lean_dec_ref(v_val_3898_);
v_e_4013_ = lean_ctor_get(v_val_3964_, 0);
lean_inc_ref(v_e_4013_);
v_o_4014_ = lean_ctor_get(v_val_3964_, 1);
lean_inc_ref(v_o_4014_);
v_n_4015_ = lean_ctor_get(v_val_3964_, 2);
lean_inc(v_n_4015_);
lean_dec_ref(v_val_3964_);
v___x_4039_ = lean_nat_dec_le(v_n_4012_, v_n_4015_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_inc_ref(v_o_4011_);
lean_inc_ref(v_o_4014_);
v___x_4040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4014_, v_o_4011_);
v___x_4041_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4040_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___f_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref(v___x_4041_);
v___x_4043_ = lean_nat_sub(v_n_4012_, v_n_4015_);
lean_dec(v_n_4015_);
lean_dec(v_n_4012_);
v___x_4044_ = l_Lean_mkNatLit(v___x_4043_);
lean_inc_ref(v_e_4010_);
v___x_4045_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4010_, v___x_4044_);
lean_inc_ref(v_e_4013_);
v___f_4046_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__4), 3, 2);
lean_closure_set(v___f_4046_, 0, v___x_4045_);
lean_closure_set(v___f_4046_, 1, v_e_4013_);
v___x_4047_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__13));
v___x_4048_ = lean_unsigned_to_nat(5u);
v___x_4049_ = lean_mk_empty_array_with_capacity(v___x_4048_);
v___x_4050_ = lean_array_push(v___x_4049_, v_e_4010_);
v___x_4051_ = lean_array_push(v___x_4050_, v_e_4013_);
v___x_4052_ = lean_array_push(v___x_4051_, v_o_4011_);
v___x_4053_ = lean_array_push(v___x_4052_, v_o_4014_);
v___x_4054_ = lean_array_push(v___x_4053_, v_a_4042_);
v___x_4055_ = l_Nat_applyEqLemma___redArg(v___f_4046_, v___x_4047_, v___x_4054_, v_a_3890_);
lean_dec_ref(v___x_4054_);
return v___x_4055_;
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_n_4015_);
lean_dec_ref(v_o_4014_);
lean_dec_ref(v_e_4013_);
lean_dec(v_n_4012_);
lean_dec_ref(v_o_4011_);
lean_dec_ref(v_e_4010_);
v_a_4056_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4041_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4041_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
uint8_t v___x_4064_; 
v___x_4064_ = lean_nat_dec_eq(v_n_4012_, v_n_4015_);
if (v___x_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_nat_sub(v_n_4015_, v_n_4012_);
lean_dec(v_n_4012_);
lean_dec(v_n_4015_);
v___x_4066_ = l_Lean_mkNatLit(v___x_4065_);
lean_inc_ref(v_e_4013_);
v___x_4067_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4013_, v___x_4066_);
v___y_4017_ = v___x_4067_;
goto v___jp_4016_;
}
else
{
lean_dec(v_n_4015_);
lean_dec(v_n_4012_);
lean_inc_ref(v_e_4013_);
v___y_4017_ = v_e_4013_;
goto v___jp_4016_;
}
}
v___jp_4016_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_inc_ref(v_o_4014_);
lean_inc_ref(v_o_4011_);
v___x_4018_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4011_, v_o_4014_);
v___x_4019_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4018_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___f_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4019_);
lean_inc_ref(v_e_4010_);
v___f_4021_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__2), 3, 2);
lean_closure_set(v___f_4021_, 0, v_e_4010_);
lean_closure_set(v___f_4021_, 1, v___y_4017_);
v___x_4022_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__11));
v___x_4023_ = lean_unsigned_to_nat(5u);
v___x_4024_ = lean_mk_empty_array_with_capacity(v___x_4023_);
v___x_4025_ = lean_array_push(v___x_4024_, v_e_4010_);
v___x_4026_ = lean_array_push(v___x_4025_, v_e_4013_);
v___x_4027_ = lean_array_push(v___x_4026_, v_o_4011_);
v___x_4028_ = lean_array_push(v___x_4027_, v_o_4014_);
v___x_4029_ = lean_array_push(v___x_4028_, v_a_4020_);
v___x_4030_ = l_Nat_applyEqLemma___redArg(v___f_4021_, v___x_4022_, v___x_4029_, v_a_3890_);
lean_dec_ref(v___x_4029_);
return v___x_4030_;
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec_ref(v___y_4017_);
lean_dec_ref(v_o_4014_);
lean_dec_ref(v_e_4013_);
lean_dec_ref(v_o_4011_);
lean_dec_ref(v_e_4010_);
v_a_4031_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4019_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4019_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec(v_a_3900_);
lean_dec(v_val_3898_);
lean_dec_ref(v_y_3886_);
lean_dec_ref(v_x_3885_);
v___x_4068_ = lean_box(0);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_4068_);
v___x_4070_ = v___x_3902_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_val_3898_);
lean_dec_ref(v_y_3886_);
lean_dec_ref(v_x_3885_);
v_a_4073_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_3899_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_3899_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
lean_dec(v_a_3894_);
lean_dec_ref(v_y_3886_);
lean_dec_ref(v_x_3885_);
v___x_4081_ = lean_box(0);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_4081_);
v___x_4083_ = v___x_3896_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v_y_3886_);
lean_dec_ref(v_x_3885_);
v_a_4086_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_3893_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_3893_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___boxed(lean_object* v_x_4094_, lean_object* v_y_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Nat_reduceNatEqExpr___redArg(v_x_4094_, v_y_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object* v_x_4102_, lean_object* v_y_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l_Nat_reduceNatEqExpr___redArg(v_x_4102_, v_y_4103_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object* v_x_4113_, lean_object* v_y_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Nat_reduceNatEqExpr(v_x_4113_, v_y_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec(v_a_4115_);
return v_res_4123_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = lean_box(0);
v___x_4128_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__1));
v___x_4129_ = l_Lean_mkConst(v___x_4128_, v___x_4127_);
return v___x_4129_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__4));
v___x_4135_ = l_Lean_mkConst(v___x_4134_, v___x_4133_);
return v___x_4135_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__8(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = lean_box(0);
v___x_4140_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__7));
v___x_4141_ = l_Lean_mkConst(v___x_4140_, v___x_4139_);
return v___x_4141_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__11(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = lean_box(0);
v___x_4146_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__10));
v___x_4147_ = l_Lean_mkConst(v___x_4146_, v___x_4145_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object* v_e_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_4155_ = lean_unsigned_to_nat(3u);
v___x_4156_ = l_Lean_Expr_isAppOfArity(v_e_4148_, v___x_4154_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec_ref(v_e_4148_);
v___x_4157_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; lean_object* v_x_4160_; lean_object* v_y_4161_; lean_object* v___x_4162_; 
v___x_4159_ = l_Lean_Expr_appFn_x21(v_e_4148_);
v_x_4160_ = l_Lean_Expr_appArg_x21(v___x_4159_);
lean_dec_ref(v___x_4159_);
v_y_4161_ = l_Lean_Expr_appArg_x21(v_e_4148_);
v___x_4162_ = l_Nat_reduceNatEqExpr___redArg(v_x_4160_, v_y_4161_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4287_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4287_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4287_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
if (lean_obj_tag(v_a_4163_) == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
lean_dec_ref(v_e_4148_);
v___x_4167_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4167_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
else
{
lean_object* v_val_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4286_; 
v_val_4171_ = lean_ctor_get(v_a_4163_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_a_4163_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4173_ = v_a_4163_;
v_isShared_4174_ = v_isSharedCheck_4286_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_val_4171_);
lean_dec(v_a_4163_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4286_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
switch(lean_obj_tag(v_val_4171_))
{
case 0:
{
uint8_t v_b_4175_; 
lean_del_object(v___x_4165_);
v_b_4175_ = lean_ctor_get_uint8(v_val_4171_, 0);
lean_dec_ref(v_val_4171_);
if (v_b_4175_ == 0)
{
lean_object* v___x_4176_; 
lean_inc_ref(v_e_4148_);
v___x_4176_ = l_Lean_Meta_mkDecide(v_e_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___x_4179_ = l_Lean_Meta_mkEqRefl(v___x_4178_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4200_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4200_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4200_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4184_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__2, &l_Nat_reduceEqDiff___redArg___closed__2_once, _init_l_Nat_reduceEqDiff___redArg___closed__2);
v___x_4185_ = l_Lean_Expr_appArg_x21(v_a_4177_);
lean_dec(v_a_4177_);
v___x_4186_ = lean_mk_empty_array_with_capacity(v___x_4155_);
v___x_4187_ = lean_array_push(v___x_4186_, v_e_4148_);
v___x_4188_ = lean_array_push(v___x_4187_, v___x_4185_);
v___x_4189_ = lean_array_push(v___x_4188_, v_a_4180_);
v___x_4190_ = l_Lean_mkAppN(v___x_4184_, v___x_4189_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4190_);
v___x_4193_ = v___x_4173_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4190_);
v___x_4193_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4194_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4194_, 0, v___x_4191_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
lean_ctor_set_uint8(v___x_4194_, sizeof(void*)*2, v___x_4156_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4195_);
v___x_4197_ = v___x_4182_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_a_4177_);
lean_del_object(v___x_4173_);
lean_dec_ref(v_e_4148_);
v_a_4201_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4179_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4179_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_del_object(v___x_4173_);
lean_dec_ref(v_e_4148_);
v_a_4209_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4176_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4176_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v___x_4217_; 
lean_inc_ref(v_e_4148_);
v___x_4217_ = l_Lean_Meta_mkDecide(v_e_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4217_);
v___x_4219_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___x_4220_ = l_Lean_Meta_mkEqRefl(v___x_4219_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4241_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4241_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4241_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4225_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__8, &l_Nat_reduceEqDiff___redArg___closed__8_once, _init_l_Nat_reduceEqDiff___redArg___closed__8);
v___x_4226_ = l_Lean_Expr_appArg_x21(v_a_4218_);
lean_dec(v_a_4218_);
v___x_4227_ = lean_mk_empty_array_with_capacity(v___x_4155_);
v___x_4228_ = lean_array_push(v___x_4227_, v_e_4148_);
v___x_4229_ = lean_array_push(v___x_4228_, v___x_4226_);
v___x_4230_ = lean_array_push(v___x_4229_, v_a_4221_);
v___x_4231_ = l_Lean_mkAppN(v___x_4225_, v___x_4230_);
lean_dec_ref(v___x_4230_);
v___x_4232_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4231_);
v___x_4234_ = v___x_4173_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4231_);
v___x_4234_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4235_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4235_, 0, v___x_4232_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
lean_ctor_set_uint8(v___x_4235_, sizeof(void*)*2, v___x_4156_);
v___x_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4236_);
v___x_4238_ = v___x_4223_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec(v_a_4218_);
lean_del_object(v___x_4173_);
lean_dec_ref(v_e_4148_);
v_a_4242_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4220_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4220_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_del_object(v___x_4173_);
lean_dec_ref(v_e_4148_);
v_a_4250_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4217_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4217_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
case 1:
{
lean_object* v_p_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4273_; 
lean_dec_ref(v_e_4148_);
v_p_4258_ = lean_ctor_get(v_val_4171_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_val_4171_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4260_ = v_val_4171_;
v_isShared_4261_ = v_isSharedCheck_4273_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_p_4258_);
lean_dec(v_val_4171_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4273_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4262_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_p_4258_);
v___x_4264_ = v___x_4173_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_p_4258_);
v___x_4264_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4265_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4265_, 0, v___x_4262_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
lean_ctor_set_uint8(v___x_4265_, sizeof(void*)*2, v___x_4156_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4265_);
v___x_4267_ = v___x_4260_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4269_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4267_);
v___x_4269_ = v___x_4165_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
default: 
{
lean_object* v_x_4274_; lean_object* v_y_4275_; lean_object* v_p_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; 
lean_dec_ref(v_e_4148_);
v_x_4274_ = lean_ctor_get(v_val_4171_, 0);
lean_inc_ref(v_x_4274_);
v_y_4275_ = lean_ctor_get(v_val_4171_, 1);
lean_inc_ref(v_y_4275_);
v_p_4276_ = lean_ctor_get(v_val_4171_, 2);
lean_inc_ref(v_p_4276_);
lean_dec_ref(v_val_4171_);
v___x_4277_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(v_x_4274_, v_y_4275_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_p_4276_);
v___x_4279_ = v___x_4173_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_p_4276_);
v___x_4279_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4283_; 
v___x_4280_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4280_, 0, v___x_4277_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2, v___x_4156_);
v___x_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4281_);
v___x_4283_ = v___x_4165_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
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
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_e_4148_);
v_a_4288_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4162_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4162_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg___boxed(lean_object* v_e_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Nat_reduceEqDiff___redArg(v_e_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* v_e_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Nat_reduceEqDiff___redArg(v_e_4303_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* v_e_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Nat_reduceEqDiff(v_e_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4342_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4343_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4340_, v___x_4341_, v___x_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20____boxed(lean_object* v_a_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_();
return v_res_4345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4349_; uint8_t v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4350_ = 1;
v___x_4351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_);
v___x_4352_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4349_, v___x_4350_, v___x_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22____boxed(lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4356_; uint8_t v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4357_ = 1;
v___x_4358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_);
v___x_4359_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4356_, v___x_4357_, v___x_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24____boxed(lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
return v_res_4361_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4367_ = lean_box(0);
v___x_4368_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__1));
v___x_4369_ = l_Lean_mkConst(v___x_4368_, v___x_4367_);
return v___x_4369_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_box(0);
v___x_4376_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__4));
v___x_4377_ = l_Lean_mkConst(v___x_4376_, v___x_4375_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object* v_e_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4384_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_4385_ = lean_unsigned_to_nat(4u);
v___x_4386_ = l_Lean_Expr_isAppOfArity(v_e_4378_, v___x_4384_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; lean_object* v_x_4390_; lean_object* v_y_4391_; lean_object* v___x_4392_; 
v___x_4389_ = l_Lean_Expr_appFn_x21(v_e_4378_);
v_x_4390_ = l_Lean_Expr_appArg_x21(v___x_4389_);
lean_dec_ref(v___x_4389_);
v_y_4391_ = l_Lean_Expr_appArg_x21(v_e_4378_);
lean_inc_ref(v_y_4391_);
lean_inc_ref(v_x_4390_);
v___x_4392_ = l_Nat_reduceNatEqExpr___redArg(v_x_4390_, v_y_4391_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4455_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4455_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4455_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___y_4398_; 
if (lean_obj_tag(v_a_4393_) == 0)
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
lean_del_object(v___x_4395_);
lean_dec_ref(v_y_4391_);
lean_dec_ref(v_x_4390_);
v___x_4405_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
return v___x_4406_;
}
else
{
lean_object* v_val_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4454_; 
v_val_4407_ = lean_ctor_get(v_a_4393_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4409_ = v_a_4393_;
v_isShared_4410_ = v_isSharedCheck_4454_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_val_4407_);
lean_dec(v_a_4393_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4454_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
switch(lean_obj_tag(v_val_4407_))
{
case 0:
{
uint8_t v_b_4411_; 
lean_del_object(v___x_4409_);
lean_dec_ref(v_y_4391_);
lean_dec_ref(v_x_4390_);
v_b_4411_ = lean_ctor_get_uint8(v_val_4407_, 0);
lean_dec_ref(v_val_4407_);
if (v_b_4411_ == 0)
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_4398_ = v___x_4412_;
goto v___jp_4397_;
}
else
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_4398_ = v___x_4413_;
goto v___jp_4397_;
}
}
case 1:
{
lean_object* v_p_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4434_; 
lean_del_object(v___x_4395_);
v_p_4414_ = lean_ctor_get(v_val_4407_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_val_4407_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4416_ = v_val_4407_;
v_isShared_4417_ = v_isSharedCheck_4434_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_p_4414_);
lean_dec(v_val_4407_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4434_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
v___x_4418_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__2, &l_Nat_reduceBeqDiff___redArg___closed__2_once, _init_l_Nat_reduceBeqDiff___redArg___closed__2);
v___x_4419_ = lean_unsigned_to_nat(3u);
v___x_4420_ = lean_mk_empty_array_with_capacity(v___x_4419_);
v___x_4421_ = lean_array_push(v___x_4420_, v_x_4390_);
v___x_4422_ = lean_array_push(v___x_4421_, v_y_4391_);
v___x_4423_ = lean_array_push(v___x_4422_, v_p_4414_);
v___x_4424_ = l_Lean_mkAppN(v___x_4418_, v___x_4423_);
lean_dec_ref(v___x_4423_);
v___x_4425_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4424_);
v___x_4427_ = v___x_4409_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4424_);
v___x_4427_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4428_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4428_, 0, v___x_4425_);
lean_ctor_set(v___x_4428_, 1, v___x_4427_);
lean_ctor_set_uint8(v___x_4428_, sizeof(void*)*2, v___x_4386_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4428_);
v___x_4430_ = v___x_4416_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
}
}
}
default: 
{
lean_object* v_x_4435_; lean_object* v_y_4436_; lean_object* v_p_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4449_; 
lean_del_object(v___x_4395_);
v_x_4435_ = lean_ctor_get(v_val_4407_, 0);
lean_inc_ref_n(v_x_4435_, 2);
v_y_4436_ = lean_ctor_get(v_val_4407_, 1);
lean_inc_ref_n(v_y_4436_, 2);
v_p_4437_ = lean_ctor_get(v_val_4407_, 2);
lean_inc_ref(v_p_4437_);
lean_dec_ref(v_val_4407_);
v___x_4438_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__5, &l_Nat_reduceBeqDiff___redArg___closed__5_once, _init_l_Nat_reduceBeqDiff___redArg___closed__5);
v___x_4439_ = lean_unsigned_to_nat(5u);
v___x_4440_ = lean_mk_empty_array_with_capacity(v___x_4439_);
v___x_4441_ = lean_array_push(v___x_4440_, v_x_4390_);
v___x_4442_ = lean_array_push(v___x_4441_, v_y_4391_);
v___x_4443_ = lean_array_push(v___x_4442_, v_x_4435_);
v___x_4444_ = lean_array_push(v___x_4443_, v_y_4436_);
v___x_4445_ = lean_array_push(v___x_4444_, v_p_4437_);
v___x_4446_ = l_Lean_mkAppN(v___x_4438_, v___x_4445_);
lean_dec_ref(v___x_4445_);
v___x_4447_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(v_x_4435_, v_y_4436_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4446_);
v___x_4449_ = v___x_4409_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4446_);
v___x_4449_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4450_, 0, v___x_4447_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
lean_ctor_set_uint8(v___x_4450_, sizeof(void*)*2, v___x_4386_);
v___x_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
return v___x_4452_;
}
}
}
}
}
v___jp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4399_ = lean_box(0);
lean_inc_ref(v___y_4398_);
v___x_4400_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4400_, 0, v___y_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
lean_ctor_set_uint8(v___x_4400_, sizeof(void*)*2, v___x_4386_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4401_);
v___x_4403_ = v___x_4395_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec_ref(v_y_4391_);
lean_dec_ref(v_x_4390_);
v_a_4456_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4392_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4392_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object* v_e_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Nat_reduceBeqDiff___redArg(v_e_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec_ref(v_e_4464_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* v_e_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Nat_reduceBeqDiff___redArg(v_e_4471_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* v_e_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Nat_reduceBeqDiff(v_e_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_e_4481_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_4498_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4499_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4496_, v___x_4497_, v___x_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20____boxed(lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_();
return v_res_4501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4506_ = 1;
v___x_4507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_);
v___x_4508_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4505_, v___x_4506_, v___x_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22____boxed(lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4512_; uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4513_ = 1;
v___x_4514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_);
v___x_4515_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4512_, v___x_4513_, v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24____boxed(lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
return v_res_4517_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = lean_box(0);
v___x_4524_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__1));
v___x_4525_ = l_Lean_mkConst(v___x_4524_, v___x_4523_);
return v___x_4525_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = lean_box(0);
v___x_4532_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__4));
v___x_4533_ = l_Lean_mkConst(v___x_4532_, v___x_4531_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object* v_e_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_4541_ = lean_unsigned_to_nat(4u);
v___x_4542_ = l_Lean_Expr_isAppOfArity(v_e_4534_, v___x_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v_x_4546_; lean_object* v_y_4547_; lean_object* v___x_4548_; 
v___x_4545_ = l_Lean_Expr_appFn_x21(v_e_4534_);
v_x_4546_ = l_Lean_Expr_appArg_x21(v___x_4545_);
lean_dec_ref(v___x_4545_);
v_y_4547_ = l_Lean_Expr_appArg_x21(v_e_4534_);
lean_inc_ref(v_y_4547_);
lean_inc_ref(v_x_4546_);
v___x_4548_ = l_Nat_reduceNatEqExpr___redArg(v_x_4546_, v_y_4547_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4612_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4612_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4612_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___y_4554_; 
if (lean_obj_tag(v_a_4549_) == 0)
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
lean_del_object(v___x_4551_);
lean_dec_ref(v_y_4547_);
lean_dec_ref(v_x_4546_);
v___x_4563_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
else
{
lean_object* v_val_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4611_; 
v_val_4565_ = lean_ctor_get(v_a_4549_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_a_4549_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4567_ = v_a_4549_;
v_isShared_4568_ = v_isSharedCheck_4611_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_val_4565_);
lean_dec(v_a_4549_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4611_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
switch(lean_obj_tag(v_val_4565_))
{
case 0:
{
uint8_t v_b_4569_; 
lean_del_object(v___x_4567_);
lean_dec_ref(v_y_4547_);
lean_dec_ref(v_x_4546_);
v_b_4569_ = lean_ctor_get_uint8(v_val_4565_, 0);
lean_dec_ref(v_val_4565_);
if (v_b_4569_ == 0)
{
if (v___x_4542_ == 0)
{
goto v___jp_4561_;
}
else
{
lean_object* v___x_4570_; 
v___x_4570_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_4554_ = v___x_4570_;
goto v___jp_4553_;
}
}
else
{
goto v___jp_4561_;
}
}
case 1:
{
lean_object* v_p_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4551_);
v_p_4571_ = lean_ctor_get(v_val_4565_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v_val_4565_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4573_ = v_val_4565_;
v_isShared_4574_ = v_isSharedCheck_4591_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_p_4571_);
lean_dec(v_val_4565_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4591_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
v___x_4575_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__2, &l_Nat_reduceBneDiff___redArg___closed__2_once, _init_l_Nat_reduceBneDiff___redArg___closed__2);
v___x_4576_ = lean_unsigned_to_nat(3u);
v___x_4577_ = lean_mk_empty_array_with_capacity(v___x_4576_);
v___x_4578_ = lean_array_push(v___x_4577_, v_x_4546_);
v___x_4579_ = lean_array_push(v___x_4578_, v_y_4547_);
v___x_4580_ = lean_array_push(v___x_4579_, v_p_4571_);
v___x_4581_ = l_Lean_mkAppN(v___x_4575_, v___x_4580_);
lean_dec_ref(v___x_4580_);
v___x_4582_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4581_);
v___x_4584_ = v___x_4567_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4581_);
v___x_4584_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4585_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4585_, 0, v___x_4582_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
lean_ctor_set_uint8(v___x_4585_, sizeof(void*)*2, v___x_4542_);
if (v_isShared_4574_ == 0)
{
lean_ctor_set_tag(v___x_4573_, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4585_);
v___x_4587_ = v___x_4573_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
}
default: 
{
lean_object* v_x_4592_; lean_object* v_y_4593_; lean_object* v_p_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
lean_del_object(v___x_4551_);
v_x_4592_ = lean_ctor_get(v_val_4565_, 0);
lean_inc_ref_n(v_x_4592_, 2);
v_y_4593_ = lean_ctor_get(v_val_4565_, 1);
lean_inc_ref_n(v_y_4593_, 2);
v_p_4594_ = lean_ctor_get(v_val_4565_, 2);
lean_inc_ref(v_p_4594_);
lean_dec_ref(v_val_4565_);
v___x_4595_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__5, &l_Nat_reduceBneDiff___redArg___closed__5_once, _init_l_Nat_reduceBneDiff___redArg___closed__5);
v___x_4596_ = lean_unsigned_to_nat(5u);
v___x_4597_ = lean_mk_empty_array_with_capacity(v___x_4596_);
v___x_4598_ = lean_array_push(v___x_4597_, v_x_4546_);
v___x_4599_ = lean_array_push(v___x_4598_, v_y_4547_);
v___x_4600_ = lean_array_push(v___x_4599_, v_x_4592_);
v___x_4601_ = lean_array_push(v___x_4600_, v_y_4593_);
v___x_4602_ = lean_array_push(v___x_4601_, v_p_4594_);
v___x_4603_ = l_Lean_mkAppN(v___x_4595_, v___x_4602_);
lean_dec_ref(v___x_4602_);
v___x_4604_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(v_x_4592_, v_y_4593_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4603_);
v___x_4606_ = v___x_4567_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4603_);
v___x_4606_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4607_, 0, v___x_4604_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
lean_ctor_set_uint8(v___x_4607_, sizeof(void*)*2, v___x_4542_);
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
return v___x_4609_;
}
}
}
}
}
v___jp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
v___x_4555_ = lean_box(0);
lean_inc_ref(v___y_4554_);
v___x_4556_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4556_, 0, v___y_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*2, v___x_4542_);
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4557_);
v___x_4559_ = v___x_4551_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
v___jp_4561_:
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_4554_ = v___x_4562_;
goto v___jp_4553_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_dec_ref(v_y_4547_);
lean_dec_ref(v_x_4546_);
v_a_4613_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4548_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4548_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object* v_e_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Nat_reduceBneDiff___redArg(v_e_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec_ref(v_e_4621_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* v_e_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Nat_reduceBneDiff___redArg(v_e_4628_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* v_e_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Nat_reduceBneDiff(v_e_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec_ref(v_e_4638_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_4655_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4656_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4653_, v___x_4654_, v___x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20____boxed(lean_object* v_a_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_();
return v_res_4658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4663_ = 1;
v___x_4664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_);
v___x_4665_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4662_, v___x_4663_, v___x_4664_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22____boxed(lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4669_; uint8_t v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4670_ = 1;
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_);
v___x_4672_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4669_, v___x_4670_, v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24____boxed(lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg(lean_object* v_nm_4705_, lean_object* v_arity_4706_, uint8_t v_isLT_4707_, lean_object* v_e_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_){
_start:
{
lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; uint8_t v___x_4741_; 
v___x_4741_ = l_Lean_Expr_isAppOfArity(v_e_4708_, v_nm_4705_, v_arity_4706_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_dec_ref(v_e_4708_);
v___x_4742_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
return v___x_4743_;
}
else
{
lean_object* v___x_4744_; lean_object* v_x_4745_; lean_object* v_y_4746_; lean_object* v___y_4748_; 
v___x_4744_ = l_Lean_Expr_appFn_x21(v_e_4708_);
v_x_4745_ = l_Lean_Expr_appArg_x21(v___x_4744_);
lean_dec_ref(v___x_4744_);
v_y_4746_ = l_Lean_Expr_appArg_x21(v_e_4708_);
if (v_isLT_4707_ == 0)
{
lean_object* v___x_4922_; 
v___x_4922_ = lean_unsigned_to_nat(0u);
v___y_4748_ = v___x_4922_;
goto v___jp_4747_;
}
else
{
lean_object* v___x_4923_; 
v___x_4923_ = lean_unsigned_to_nat(1u);
v___y_4748_ = v___x_4923_;
goto v___jp_4747_;
}
v___jp_4747_:
{
lean_object* v___x_4749_; 
lean_inc_ref(v_x_4745_);
v___x_4749_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_4745_, v___y_4748_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4913_; 
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4752_ = v___x_4749_;
v_isShared_4753_ = v_isSharedCheck_4913_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4749_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4913_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
if (lean_obj_tag(v_a_4750_) == 1)
{
lean_object* v_val_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_del_object(v___x_4752_);
v_val_4754_ = lean_ctor_get(v_a_4750_, 0);
lean_inc(v_val_4754_);
lean_dec_ref(v_a_4750_);
v___x_4755_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_y_4746_);
v___x_4756_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_4746_, v___x_4755_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4900_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4900_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4900_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
if (lean_obj_tag(v_a_4757_) == 1)
{
lean_del_object(v___x_4759_);
if (lean_obj_tag(v_val_4754_) == 0)
{
lean_object* v_val_4761_; 
lean_dec_ref(v_y_4746_);
v_val_4761_ = lean_ctor_get(v_a_4757_, 0);
lean_inc(v_val_4761_);
lean_dec_ref(v_a_4757_);
if (lean_obj_tag(v_val_4761_) == 0)
{
lean_object* v_n_4762_; lean_object* v_n_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; 
lean_dec_ref(v_x_4745_);
v_n_4762_ = lean_ctor_get(v_val_4754_, 0);
lean_inc(v_n_4762_);
lean_dec_ref(v_val_4754_);
v_n_4763_ = lean_ctor_get(v_val_4761_, 0);
lean_inc(v_n_4763_);
lean_dec_ref(v_val_4761_);
v___x_4764_ = lean_nat_dec_le(v_n_4762_, v_n_4763_);
lean_dec(v_n_4763_);
lean_dec(v_n_4762_);
v___x_4765_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_4708_, v___x_4764_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
return v___x_4765_;
}
else
{
lean_object* v_n_4766_; lean_object* v_e_4767_; lean_object* v_o_4768_; lean_object* v_n_4769_; uint8_t v___x_4770_; 
lean_dec_ref(v_e_4708_);
v_n_4766_ = lean_ctor_get(v_val_4754_, 0);
lean_inc(v_n_4766_);
lean_dec_ref(v_val_4754_);
v_e_4767_ = lean_ctor_get(v_val_4761_, 0);
lean_inc_ref(v_e_4767_);
v_o_4768_ = lean_ctor_get(v_val_4761_, 1);
lean_inc_ref(v_o_4768_);
v_n_4769_ = lean_ctor_get(v_val_4761_, 2);
lean_inc(v_n_4769_);
lean_dec_ref(v_val_4761_);
v___x_4770_ = lean_nat_dec_le(v_n_4766_, v_n_4769_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_inc_ref(v_x_4745_);
lean_inc_ref(v_o_4768_);
v___x_4771_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4768_, v_x_4745_);
v___x_4772_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4771_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref(v___x_4772_);
v___x_4774_ = lean_nat_sub(v_n_4766_, v_n_4769_);
lean_dec(v_n_4769_);
lean_dec(v_n_4766_);
v___x_4775_ = l_Lean_mkNatLit(v___x_4774_);
lean_inc_ref(v_e_4767_);
v___x_4776_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_4775_, v_e_4767_);
v___x_4777_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__3));
v___x_4778_ = lean_unsigned_to_nat(4u);
v___x_4779_ = lean_mk_empty_array_with_capacity(v___x_4778_);
v___x_4780_ = lean_array_push(v___x_4779_, v_x_4745_);
v___x_4781_ = lean_array_push(v___x_4780_, v_e_4767_);
v___x_4782_ = lean_array_push(v___x_4781_, v_o_4768_);
v___x_4783_ = lean_array_push(v___x_4782_, v_a_4773_);
v___x_4784_ = l_Nat_applySimprocConst___redArg(v___x_4776_, v___x_4777_, v___x_4783_, v_a_4712_);
lean_dec_ref(v___x_4783_);
return v___x_4784_;
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec(v_n_4769_);
lean_dec_ref(v_o_4768_);
lean_dec_ref(v_e_4767_);
lean_dec(v_n_4766_);
lean_dec_ref(v_x_4745_);
v_a_4785_ = lean_ctor_get(v___x_4772_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4772_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4772_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_dec(v_n_4769_);
lean_dec(v_n_4766_);
lean_inc_ref(v_o_4768_);
lean_inc_ref(v_x_4745_);
v___x_4793_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_x_4745_, v_o_4768_);
v___x_4794_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4793_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4795_);
lean_dec_ref(v___x_4794_);
v___x_4796_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_4797_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__5));
v___x_4798_ = lean_unsigned_to_nat(4u);
v___x_4799_ = lean_mk_empty_array_with_capacity(v___x_4798_);
v___x_4800_ = lean_array_push(v___x_4799_, v_x_4745_);
v___x_4801_ = lean_array_push(v___x_4800_, v_e_4767_);
v___x_4802_ = lean_array_push(v___x_4801_, v_o_4768_);
v___x_4803_ = lean_array_push(v___x_4802_, v_a_4795_);
v___x_4804_ = l_Nat_applySimprocConst___redArg(v___x_4796_, v___x_4797_, v___x_4803_, v_a_4712_);
lean_dec_ref(v___x_4803_);
return v___x_4804_;
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec_ref(v_o_4768_);
lean_dec_ref(v_e_4767_);
lean_dec_ref(v_x_4745_);
v_a_4805_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4794_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4794_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
}
else
{
lean_object* v_val_4813_; 
lean_dec_ref(v_x_4745_);
lean_dec_ref(v_e_4708_);
v_val_4813_ = lean_ctor_get(v_a_4757_, 0);
lean_inc(v_val_4813_);
lean_dec_ref(v_a_4757_);
if (lean_obj_tag(v_val_4813_) == 0)
{
lean_object* v_e_4814_; lean_object* v_o_4815_; lean_object* v_n_4816_; lean_object* v_n_4817_; uint8_t v___x_4818_; 
v_e_4814_ = lean_ctor_get(v_val_4754_, 0);
lean_inc_ref(v_e_4814_);
v_o_4815_ = lean_ctor_get(v_val_4754_, 1);
lean_inc_ref(v_o_4815_);
v_n_4816_ = lean_ctor_get(v_val_4754_, 2);
lean_inc(v_n_4816_);
lean_dec_ref(v_val_4754_);
v_n_4817_ = lean_ctor_get(v_val_4813_, 0);
lean_inc(v_n_4817_);
lean_dec_ref(v_val_4813_);
v___x_4818_ = lean_nat_dec_le(v_n_4816_, v_n_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
lean_dec(v_n_4817_);
lean_dec(v_n_4816_);
lean_inc_ref(v_o_4815_);
lean_inc_ref(v_y_4746_);
v___x_4819_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_4746_, v_o_4815_);
v___x_4820_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4819_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
lean_dec_ref(v___x_4820_);
v___x_4822_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_4823_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__7));
v___x_4824_ = lean_unsigned_to_nat(4u);
v___x_4825_ = lean_mk_empty_array_with_capacity(v___x_4824_);
v___x_4826_ = lean_array_push(v___x_4825_, v_e_4814_);
v___x_4827_ = lean_array_push(v___x_4826_, v_o_4815_);
v___x_4828_ = lean_array_push(v___x_4827_, v_y_4746_);
v___x_4829_ = lean_array_push(v___x_4828_, v_a_4821_);
v___x_4830_ = l_Nat_applySimprocConst___redArg(v___x_4822_, v___x_4823_, v___x_4829_, v_a_4712_);
lean_dec_ref(v___x_4829_);
return v___x_4830_;
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
lean_dec_ref(v_o_4815_);
lean_dec_ref(v_e_4814_);
lean_dec_ref(v_y_4746_);
v_a_4831_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4820_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4820_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
lean_inc_ref(v_y_4746_);
lean_inc_ref(v_o_4815_);
v___x_4839_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4815_, v_y_4746_);
v___x_4840_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4839_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref(v___x_4840_);
v___x_4842_ = lean_nat_sub(v_n_4817_, v_n_4816_);
lean_dec(v_n_4816_);
lean_dec(v_n_4817_);
v___x_4843_ = l_Lean_mkNatLit(v___x_4842_);
lean_inc_ref(v_e_4814_);
v___x_4844_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_e_4814_, v___x_4843_);
v___x_4845_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__9));
v___x_4846_ = lean_unsigned_to_nat(4u);
v___x_4847_ = lean_mk_empty_array_with_capacity(v___x_4846_);
v___x_4848_ = lean_array_push(v___x_4847_, v_e_4814_);
v___x_4849_ = lean_array_push(v___x_4848_, v_o_4815_);
v___x_4850_ = lean_array_push(v___x_4849_, v_y_4746_);
v___x_4851_ = lean_array_push(v___x_4850_, v_a_4841_);
v___x_4852_ = l_Nat_applySimprocConst___redArg(v___x_4844_, v___x_4845_, v___x_4851_, v_a_4712_);
lean_dec_ref(v___x_4851_);
return v___x_4852_;
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_n_4817_);
lean_dec(v_n_4816_);
lean_dec_ref(v_o_4815_);
lean_dec_ref(v_e_4814_);
lean_dec_ref(v_y_4746_);
v_a_4853_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4840_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4840_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
}
else
{
lean_object* v_e_4861_; lean_object* v_o_4862_; lean_object* v_n_4863_; lean_object* v_e_4864_; lean_object* v_o_4865_; lean_object* v_n_4866_; uint8_t v___x_4867_; 
lean_dec_ref(v_y_4746_);
v_e_4861_ = lean_ctor_get(v_val_4754_, 0);
lean_inc_ref(v_e_4861_);
v_o_4862_ = lean_ctor_get(v_val_4754_, 1);
lean_inc_ref(v_o_4862_);
v_n_4863_ = lean_ctor_get(v_val_4754_, 2);
lean_inc(v_n_4863_);
lean_dec_ref(v_val_4754_);
v_e_4864_ = lean_ctor_get(v_val_4813_, 0);
lean_inc_ref(v_e_4864_);
v_o_4865_ = lean_ctor_get(v_val_4813_, 1);
lean_inc_ref(v_o_4865_);
v_n_4866_ = lean_ctor_get(v_val_4813_, 2);
lean_inc(v_n_4866_);
lean_dec_ref(v_val_4813_);
v___x_4867_ = lean_nat_dec_le(v_n_4863_, v_n_4866_);
if (v___x_4867_ == 0)
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_inc_ref(v_o_4862_);
lean_inc_ref(v_o_4865_);
v___x_4868_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4865_, v_o_4862_);
v___x_4869_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4868_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref(v___x_4869_);
v___x_4871_ = lean_nat_sub(v_n_4863_, v_n_4866_);
lean_dec(v_n_4866_);
lean_dec(v_n_4863_);
v___x_4872_ = l_Lean_mkNatLit(v___x_4871_);
lean_inc_ref(v_e_4861_);
v___x_4873_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4861_, v___x_4872_);
lean_inc_ref(v_e_4864_);
v___x_4874_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_4873_, v_e_4864_);
v___x_4875_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__11));
v___x_4876_ = lean_unsigned_to_nat(5u);
v___x_4877_ = lean_mk_empty_array_with_capacity(v___x_4876_);
v___x_4878_ = lean_array_push(v___x_4877_, v_e_4861_);
v___x_4879_ = lean_array_push(v___x_4878_, v_e_4864_);
v___x_4880_ = lean_array_push(v___x_4879_, v_o_4862_);
v___x_4881_ = lean_array_push(v___x_4880_, v_o_4865_);
v___x_4882_ = lean_array_push(v___x_4881_, v_a_4870_);
v___x_4883_ = l_Nat_applySimprocConst___redArg(v___x_4874_, v___x_4875_, v___x_4882_, v_a_4712_);
lean_dec_ref(v___x_4882_);
return v___x_4883_;
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec(v_n_4866_);
lean_dec_ref(v_o_4865_);
lean_dec_ref(v_e_4864_);
lean_dec(v_n_4863_);
lean_dec_ref(v_o_4862_);
lean_dec_ref(v_e_4861_);
v_a_4884_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4869_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4869_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
uint8_t v___x_4892_; 
v___x_4892_ = lean_nat_dec_eq(v_n_4863_, v_n_4866_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_nat_sub(v_n_4866_, v_n_4863_);
lean_dec(v_n_4863_);
lean_dec(v_n_4866_);
v___x_4894_ = l_Lean_mkNatLit(v___x_4893_);
lean_inc_ref(v_e_4864_);
v___x_4895_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4864_, v___x_4894_);
v___y_4715_ = v_e_4864_;
v___y_4716_ = v_e_4861_;
v___y_4717_ = v_o_4862_;
v___y_4718_ = v_o_4865_;
v___y_4719_ = v___x_4895_;
goto v___jp_4714_;
}
else
{
lean_dec(v_n_4866_);
lean_dec(v_n_4863_);
lean_inc_ref(v_e_4864_);
v___y_4715_ = v_e_4864_;
v___y_4716_ = v_e_4861_;
v___y_4717_ = v_o_4862_;
v___y_4718_ = v_o_4865_;
v___y_4719_ = v_e_4864_;
goto v___jp_4714_;
}
}
}
}
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
lean_dec(v_a_4757_);
lean_dec(v_val_4754_);
lean_dec_ref(v_y_4746_);
lean_dec_ref(v_x_4745_);
lean_dec_ref(v_e_4708_);
v___x_4896_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4896_);
v___x_4898_ = v___x_4759_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
lean_dec(v_val_4754_);
lean_dec_ref(v_y_4746_);
lean_dec_ref(v_x_4745_);
lean_dec_ref(v_e_4708_);
v_a_4901_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4756_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4756_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
else
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
lean_dec(v_a_4750_);
lean_dec_ref(v_y_4746_);
lean_dec_ref(v_x_4745_);
lean_dec_ref(v_e_4708_);
v___x_4909_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v___x_4909_);
v___x_4911_ = v___x_4752_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
lean_dec_ref(v_y_4746_);
lean_dec_ref(v_x_4745_);
lean_dec_ref(v_e_4708_);
v_a_4914_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4749_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4749_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
v___jp_4714_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_inc_ref(v___y_4718_);
lean_inc_ref(v___y_4717_);
v___x_4720_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4717_, v___y_4718_);
v___x_4721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4720_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref(v___x_4721_);
lean_inc_ref(v___y_4716_);
v___x_4723_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4716_, v___y_4719_);
v___x_4724_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__1));
v___x_4725_ = lean_unsigned_to_nat(5u);
v___x_4726_ = lean_mk_empty_array_with_capacity(v___x_4725_);
v___x_4727_ = lean_array_push(v___x_4726_, v___y_4716_);
v___x_4728_ = lean_array_push(v___x_4727_, v___y_4715_);
v___x_4729_ = lean_array_push(v___x_4728_, v___y_4717_);
v___x_4730_ = lean_array_push(v___x_4729_, v___y_4718_);
v___x_4731_ = lean_array_push(v___x_4730_, v_a_4722_);
v___x_4732_ = l_Nat_applySimprocConst___redArg(v___x_4723_, v___x_4724_, v___x_4731_, v_a_4712_);
lean_dec_ref(v___x_4731_);
return v___x_4732_;
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec_ref(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec_ref(v___y_4715_);
v_a_4733_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4721_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4721_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg___boxed(lean_object* v_nm_4924_, lean_object* v_arity_4925_, lean_object* v_isLT_4926_, lean_object* v_e_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
uint8_t v_isLT_boxed_4933_; lean_object* v_res_4934_; 
v_isLT_boxed_4933_ = lean_unbox(v_isLT_4926_);
v_res_4934_ = l_Nat_reduceLTLE___redArg(v_nm_4924_, v_arity_4925_, v_isLT_boxed_4933_, v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_nm_4924_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object* v_nm_4935_, lean_object* v_arity_4936_, uint8_t v_isLT_4937_, lean_object* v_e_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v___x_4947_; 
v___x_4947_ = l_Nat_reduceLTLE___redArg(v_nm_4935_, v_arity_4936_, v_isLT_4937_, v_e_4938_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object* v_nm_4948_, lean_object* v_arity_4949_, lean_object* v_isLT_4950_, lean_object* v_e_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
uint8_t v_isLT_boxed_4960_; lean_object* v_res_4961_; 
v_isLT_boxed_4960_ = lean_unbox(v_isLT_4950_);
v_res_4961_ = l_Nat_reduceLTLE(v_nm_4948_, v_arity_4949_, v_isLT_boxed_4960_, v_e_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec(v_nm_4948_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object* v_e_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; uint8_t v___x_4970_; lean_object* v___x_4971_; 
v___x_4968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_4969_ = lean_unsigned_to_nat(4u);
v___x_4970_ = 0;
v___x_4971_ = l_Nat_reduceLTLE___redArg(v___x_4968_, v___x_4969_, v___x_4970_, v_e_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object* v_e_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Nat_reduceLeDiff___redArg(v_e_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_);
lean_dec(v_a_4976_);
lean_dec_ref(v_a_4975_);
lean_dec(v_a_4974_);
lean_dec_ref(v_a_4973_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* v_e_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4988_; 
v___x_4988_ = l_Nat_reduceLeDiff___redArg(v_e_4979_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* v_e_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Nat_reduceLeDiff(v_e_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5019_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5020_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5017_, v___x_5018_, v___x_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20____boxed(lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_();
return v_res_5022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5023_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5023_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_5026_; uint8_t v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5027_ = 1;
v___x_5028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_);
v___x_5029_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5026_, v___x_5027_, v___x_5028_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22____boxed(lean_object* v_a_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_5033_; uint8_t v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5034_ = 1;
v___x_5035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_);
v___x_5036_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5033_, v___x_5034_, v___x_5035_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24____boxed(lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object* v_e_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5069_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_5070_ = lean_unsigned_to_nat(6u);
v___x_5071_ = l_Lean_Expr_isAppOfArity(v_e_5063_, v___x_5069_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
return v___x_5073_;
}
else
{
lean_object* v___x_5074_; lean_object* v_p_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5074_ = l_Lean_Expr_appFn_x21(v_e_5063_);
v_p_5075_ = l_Lean_Expr_appArg_x21(v___x_5074_);
lean_dec_ref(v___x_5074_);
v___x_5076_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_5075_);
v___x_5077_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_p_5075_, v___x_5076_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5265_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5265_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5265_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
if (lean_obj_tag(v_a_5078_) == 1)
{
lean_object* v_val_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
lean_del_object(v___x_5080_);
v_val_5082_ = lean_ctor_get(v_a_5078_, 0);
lean_inc(v_val_5082_);
lean_dec_ref(v_a_5078_);
v___x_5083_ = l_Lean_Expr_appArg_x21(v_e_5063_);
lean_inc_ref(v___x_5083_);
v___x_5084_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v___x_5083_, v___x_5076_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5252_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5087_ = v___x_5084_;
v_isShared_5088_ = v_isSharedCheck_5252_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5084_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5252_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
if (lean_obj_tag(v_a_5085_) == 1)
{
lean_del_object(v___x_5087_);
if (lean_obj_tag(v_val_5082_) == 0)
{
lean_object* v_val_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5139_; 
lean_dec_ref(v___x_5083_);
v_val_5089_ = lean_ctor_get(v_a_5085_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v_a_5085_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5091_ = v_a_5085_;
v_isShared_5092_ = v_isSharedCheck_5139_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_val_5089_);
lean_dec(v_a_5085_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5139_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
if (lean_obj_tag(v_val_5089_) == 0)
{
lean_object* v_n_5093_; lean_object* v_n_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5124_; 
lean_dec_ref(v_p_5075_);
v_n_5093_ = lean_ctor_get(v_val_5082_, 0);
lean_inc(v_n_5093_);
lean_dec_ref(v_val_5082_);
v_n_5094_ = lean_ctor_get(v_val_5089_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_val_5089_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5096_ = v_val_5089_;
v_isShared_5097_ = v_isSharedCheck_5124_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_n_5094_);
lean_dec(v_val_5089_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5124_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5098_ = lean_nat_sub(v_n_5093_, v_n_5094_);
lean_dec(v_n_5094_);
lean_dec(v_n_5093_);
v___x_5099_ = l_Lean_mkNatLit(v___x_5098_);
lean_inc_ref(v___x_5099_);
v___x_5100_ = l_Lean_Meta_mkEqRefl(v___x_5099_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5115_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5115_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5115_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v_a_5101_);
v___x_5106_ = v___x_5091_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; lean_object* v___x_5109_; 
v___x_5107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5107_, 0, v___x_5099_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
lean_ctor_set_uint8(v___x_5107_, sizeof(void*)*2, v___x_5071_);
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v___x_5107_);
v___x_5109_ = v___x_5096_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5111_; 
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 0, v___x_5109_);
v___x_5111_ = v___x_5103_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5109_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec_ref(v___x_5099_);
lean_del_object(v___x_5096_);
lean_del_object(v___x_5091_);
v_a_5116_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5100_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5100_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
else
{
lean_object* v_n_5125_; lean_object* v_e_5126_; lean_object* v_o_5127_; lean_object* v_n_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
lean_del_object(v___x_5091_);
v_n_5125_ = lean_ctor_get(v_val_5082_, 0);
lean_inc(v_n_5125_);
lean_dec_ref(v_val_5082_);
v_e_5126_ = lean_ctor_get(v_val_5089_, 0);
lean_inc_ref_n(v_e_5126_, 2);
v_o_5127_ = lean_ctor_get(v_val_5089_, 1);
lean_inc_ref(v_o_5127_);
v_n_5128_ = lean_ctor_get(v_val_5089_, 2);
lean_inc(v_n_5128_);
lean_dec_ref(v_val_5089_);
v___x_5129_ = lean_nat_sub(v_n_5125_, v_n_5128_);
lean_dec(v_n_5128_);
lean_dec(v_n_5125_);
v___x_5130_ = l_Lean_mkNatLit(v___x_5129_);
v___x_5131_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5130_, v_e_5126_);
v___x_5132_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__1));
v___x_5133_ = lean_unsigned_to_nat(3u);
v___x_5134_ = lean_mk_empty_array_with_capacity(v___x_5133_);
v___x_5135_ = lean_array_push(v___x_5134_, v_p_5075_);
v___x_5136_ = lean_array_push(v___x_5135_, v_e_5126_);
v___x_5137_ = lean_array_push(v___x_5136_, v_o_5127_);
v___x_5138_ = l_Nat_applySimprocConst___redArg(v___x_5131_, v___x_5132_, v___x_5137_, v_a_5067_);
lean_dec_ref(v___x_5137_);
return v___x_5138_;
}
}
}
else
{
lean_object* v_val_5140_; lean_object* v_e_5141_; lean_object* v_o_5142_; lean_object* v_n_5143_; lean_object* v___y_5145_; 
lean_dec_ref(v_p_5075_);
v_val_5140_ = lean_ctor_get(v_a_5085_, 0);
lean_inc(v_val_5140_);
lean_dec_ref(v_a_5085_);
v_e_5141_ = lean_ctor_get(v_val_5082_, 0);
lean_inc_ref(v_e_5141_);
v_o_5142_ = lean_ctor_get(v_val_5082_, 1);
lean_inc_ref(v_o_5142_);
v_n_5143_ = lean_ctor_get(v_val_5082_, 2);
lean_inc(v_n_5143_);
lean_dec_ref(v_val_5082_);
if (lean_obj_tag(v_val_5140_) == 0)
{
lean_object* v_n_5165_; uint8_t v___x_5166_; 
v_n_5165_ = lean_ctor_get(v_val_5140_, 0);
lean_inc(v_n_5165_);
lean_dec_ref(v_val_5140_);
v___x_5166_ = lean_nat_dec_le(v_n_5143_, v_n_5165_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_inc_ref(v_o_5142_);
lean_inc_ref(v___x_5083_);
v___x_5167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_5083_, v_o_5142_);
v___x_5168_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5167_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref(v___x_5168_);
v___x_5170_ = lean_nat_sub(v_n_5143_, v_n_5165_);
lean_dec(v_n_5165_);
lean_dec(v_n_5143_);
v___x_5171_ = l_Lean_mkNatLit(v___x_5170_);
lean_inc_ref(v_e_5141_);
v___x_5172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5141_, v___x_5171_);
v___x_5173_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__5));
v___x_5174_ = lean_unsigned_to_nat(4u);
v___x_5175_ = lean_mk_empty_array_with_capacity(v___x_5174_);
v___x_5176_ = lean_array_push(v___x_5175_, v_o_5142_);
v___x_5177_ = lean_array_push(v___x_5176_, v___x_5083_);
v___x_5178_ = lean_array_push(v___x_5177_, v_a_5169_);
v___x_5179_ = lean_array_push(v___x_5178_, v_e_5141_);
v___x_5180_ = l_Nat_applySimprocConst___redArg(v___x_5172_, v___x_5173_, v___x_5179_, v_a_5067_);
lean_dec_ref(v___x_5179_);
return v___x_5180_;
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
lean_dec(v_n_5165_);
lean_dec(v_n_5143_);
lean_dec_ref(v_o_5142_);
lean_dec_ref(v_e_5141_);
lean_dec_ref(v___x_5083_);
v_a_5181_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5183_ = v___x_5168_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5168_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
else
{
uint8_t v___x_5189_; 
v___x_5189_ = lean_nat_dec_eq(v_n_5143_, v_n_5165_);
if (v___x_5189_ == 0)
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5190_ = lean_nat_sub(v_n_5165_, v_n_5143_);
lean_dec(v_n_5143_);
lean_dec(v_n_5165_);
v___x_5191_ = l_Lean_mkNatLit(v___x_5190_);
lean_inc_ref(v_e_5141_);
v___x_5192_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5141_, v___x_5191_);
v___y_5145_ = v___x_5192_;
goto v___jp_5144_;
}
else
{
lean_dec(v_n_5165_);
lean_dec(v_n_5143_);
lean_inc_ref(v_e_5141_);
v___y_5145_ = v_e_5141_;
goto v___jp_5144_;
}
}
}
else
{
lean_object* v_e_5193_; lean_object* v_o_5194_; lean_object* v_n_5195_; lean_object* v___y_5197_; uint8_t v___x_5219_; 
lean_dec_ref(v___x_5083_);
v_e_5193_ = lean_ctor_get(v_val_5140_, 0);
lean_inc_ref(v_e_5193_);
v_o_5194_ = lean_ctor_get(v_val_5140_, 1);
lean_inc_ref(v_o_5194_);
v_n_5195_ = lean_ctor_get(v_val_5140_, 2);
lean_inc(v_n_5195_);
lean_dec_ref(v_val_5140_);
v___x_5219_ = lean_nat_dec_le(v_n_5143_, v_n_5195_);
if (v___x_5219_ == 0)
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_inc_ref(v_o_5142_);
lean_inc_ref(v_o_5194_);
v___x_5220_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5194_, v_o_5142_);
v___x_5221_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5220_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref(v___x_5221_);
v___x_5223_ = lean_nat_sub(v_n_5143_, v_n_5195_);
lean_dec(v_n_5195_);
lean_dec(v_n_5143_);
v___x_5224_ = l_Lean_mkNatLit(v___x_5223_);
lean_inc_ref(v_e_5141_);
v___x_5225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5141_, v___x_5224_);
lean_inc_ref(v_e_5193_);
v___x_5226_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5225_, v_e_5193_);
v___x_5227_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__9));
v___x_5228_ = lean_unsigned_to_nat(5u);
v___x_5229_ = lean_mk_empty_array_with_capacity(v___x_5228_);
v___x_5230_ = lean_array_push(v___x_5229_, v_e_5141_);
v___x_5231_ = lean_array_push(v___x_5230_, v_e_5193_);
v___x_5232_ = lean_array_push(v___x_5231_, v_o_5142_);
v___x_5233_ = lean_array_push(v___x_5232_, v_o_5194_);
v___x_5234_ = lean_array_push(v___x_5233_, v_a_5222_);
v___x_5235_ = l_Nat_applySimprocConst___redArg(v___x_5226_, v___x_5227_, v___x_5234_, v_a_5067_);
lean_dec_ref(v___x_5234_);
return v___x_5235_;
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec(v_n_5195_);
lean_dec_ref(v_o_5194_);
lean_dec_ref(v_e_5193_);
lean_dec(v_n_5143_);
lean_dec_ref(v_o_5142_);
lean_dec_ref(v_e_5141_);
v_a_5236_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5221_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5221_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
else
{
uint8_t v___x_5244_; 
v___x_5244_ = lean_nat_dec_eq(v_n_5143_, v_n_5195_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5245_ = lean_nat_sub(v_n_5195_, v_n_5143_);
lean_dec(v_n_5143_);
lean_dec(v_n_5195_);
v___x_5246_ = l_Lean_mkNatLit(v___x_5245_);
lean_inc_ref(v_e_5193_);
v___x_5247_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5193_, v___x_5246_);
v___y_5197_ = v___x_5247_;
goto v___jp_5196_;
}
else
{
lean_dec(v_n_5195_);
lean_dec(v_n_5143_);
lean_inc_ref(v_e_5193_);
v___y_5197_ = v_e_5193_;
goto v___jp_5196_;
}
}
v___jp_5196_:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; 
lean_inc_ref(v_o_5194_);
lean_inc_ref(v_o_5142_);
v___x_5198_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5142_, v_o_5194_);
v___x_5199_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5198_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
lean_dec_ref(v___x_5199_);
lean_inc_ref(v_e_5141_);
v___x_5201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5141_, v___y_5197_);
v___x_5202_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__7));
v___x_5203_ = lean_unsigned_to_nat(5u);
v___x_5204_ = lean_mk_empty_array_with_capacity(v___x_5203_);
v___x_5205_ = lean_array_push(v___x_5204_, v_e_5141_);
v___x_5206_ = lean_array_push(v___x_5205_, v_e_5193_);
v___x_5207_ = lean_array_push(v___x_5206_, v_o_5142_);
v___x_5208_ = lean_array_push(v___x_5207_, v_o_5194_);
v___x_5209_ = lean_array_push(v___x_5208_, v_a_5200_);
v___x_5210_ = l_Nat_applySimprocConst___redArg(v___x_5201_, v___x_5202_, v___x_5209_, v_a_5067_);
lean_dec_ref(v___x_5209_);
return v___x_5210_;
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_o_5194_);
lean_dec_ref(v_e_5193_);
lean_dec_ref(v_o_5142_);
lean_dec_ref(v_e_5141_);
v_a_5211_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5199_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5199_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
v___jp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
lean_inc_ref(v___x_5083_);
lean_inc_ref(v_o_5142_);
v___x_5146_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5142_, v___x_5083_);
v___x_5147_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5146_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref(v___x_5147_);
v___x_5149_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__3));
v___x_5150_ = lean_unsigned_to_nat(4u);
v___x_5151_ = lean_mk_empty_array_with_capacity(v___x_5150_);
v___x_5152_ = lean_array_push(v___x_5151_, v_e_5141_);
v___x_5153_ = lean_array_push(v___x_5152_, v_o_5142_);
v___x_5154_ = lean_array_push(v___x_5153_, v___x_5083_);
v___x_5155_ = lean_array_push(v___x_5154_, v_a_5148_);
v___x_5156_ = l_Nat_applySimprocConst___redArg(v___y_5145_, v___x_5149_, v___x_5155_, v_a_5067_);
lean_dec_ref(v___x_5155_);
return v___x_5156_;
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v___y_5145_);
lean_dec_ref(v_o_5142_);
lean_dec_ref(v_e_5141_);
lean_dec_ref(v___x_5083_);
v_a_5157_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5147_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5147_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
else
{
lean_object* v___x_5248_; lean_object* v___x_5250_; 
lean_dec(v_a_5085_);
lean_dec_ref(v___x_5083_);
lean_dec(v_val_5082_);
lean_dec_ref(v_p_5075_);
v___x_5248_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5248_);
v___x_5250_ = v___x_5087_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
else
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5260_; 
lean_dec_ref(v___x_5083_);
lean_dec(v_val_5082_);
lean_dec_ref(v_p_5075_);
v_a_5253_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5255_ = v___x_5084_;
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5084_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5258_; 
if (v_isShared_5256_ == 0)
{
v___x_5258_ = v___x_5255_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5253_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
}
else
{
lean_object* v___x_5261_; lean_object* v___x_5263_; 
lean_dec(v_a_5078_);
lean_dec_ref(v_p_5075_);
v___x_5261_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 0, v___x_5261_);
v___x_5263_ = v___x_5080_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5261_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v_p_5075_);
v_a_5266_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5077_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5077_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object* v_e_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l_Nat_reduceSubDiff___redArg(v_e_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
lean_dec(v_a_5278_);
lean_dec_ref(v_a_5277_);
lean_dec(v_a_5276_);
lean_dec_ref(v_a_5275_);
lean_dec_ref(v_e_5274_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* v_e_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l_Nat_reduceSubDiff___redArg(v_e_5281_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* v_e_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Nat_reduceSubDiff(v_e_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5297_);
lean_dec(v_a_5296_);
lean_dec_ref(v_a_5295_);
lean_dec(v_a_5294_);
lean_dec_ref(v_a_5293_);
lean_dec(v_a_5292_);
lean_dec_ref(v_e_5291_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_5308_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5309_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5306_, v___x_5307_, v___x_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19____boxed(lean_object* v_a_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_();
return v_res_5311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5312_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5315_; uint8_t v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5316_ = 1;
v___x_5317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_);
v___x_5318_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5315_, v___x_5316_, v___x_5317_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21____boxed(lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5322_; uint8_t v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5323_ = 1;
v___x_5324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_);
v___x_5325_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5322_, v___x_5323_, v___x_5324_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23____boxed(lean_object* v_a_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
return v_res_5327_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5337_ = lean_box(0);
v___x_5338_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__4));
v___x_5339_ = l_Lean_mkConst(v___x_5338_, v___x_5337_);
return v___x_5339_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5344_ = lean_box(0);
v___x_5345_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__7));
v___x_5346_ = l_Lean_mkConst(v___x_5345_, v___x_5344_);
return v___x_5346_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = lean_box(0);
v___x_5352_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__10));
v___x_5353_ = l_Lean_mkConst(v___x_5352_, v___x_5351_);
return v___x_5353_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object* v_e_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5354_, v_a_5356_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5481_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5363_ = v___x_5360_;
v_isShared_5364_ = v_isSharedCheck_5481_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5360_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5481_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5370_ = l_Lean_Expr_cleanupAnnotations(v_a_5361_);
v___x_5371_ = l_Lean_Expr_isApp(v___x_5370_);
if (v___x_5371_ == 0)
{
lean_dec_ref(v___x_5370_);
goto v___jp_5365_;
}
else
{
lean_object* v_arg_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v_arg_5372_ = lean_ctor_get(v___x_5370_, 1);
lean_inc_ref(v_arg_5372_);
v___x_5373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5370_);
v___x_5374_ = l_Lean_Expr_isApp(v___x_5373_);
if (v___x_5374_ == 0)
{
lean_dec_ref(v___x_5373_);
lean_dec_ref(v_arg_5372_);
goto v___jp_5365_;
}
else
{
lean_object* v_arg_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_arg_5375_ = lean_ctor_get(v___x_5373_, 1);
lean_inc_ref(v_arg_5375_);
v___x_5376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5373_);
v___x_5377_ = l_Lean_Expr_isApp(v___x_5376_);
if (v___x_5377_ == 0)
{
lean_dec_ref(v___x_5376_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
goto v___jp_5365_;
}
else
{
lean_object* v_arg_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_arg_5378_ = lean_ctor_get(v___x_5376_, 1);
lean_inc_ref(v_arg_5378_);
v___x_5379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5376_);
v___x_5380_ = l_Lean_Expr_isApp(v___x_5379_);
if (v___x_5380_ == 0)
{
lean_dec_ref(v___x_5379_);
lean_dec_ref(v_arg_5378_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
goto v___jp_5365_;
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; uint8_t v___x_5383_; 
v___x_5381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5379_);
v___x_5382_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__2));
v___x_5383_ = l_Lean_Expr_isConstOf(v___x_5381_, v___x_5382_);
lean_dec_ref(v___x_5381_);
if (v___x_5383_ == 0)
{
lean_dec_ref(v_arg_5378_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
goto v___jp_5365_;
}
else
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
lean_del_object(v___x_5363_);
v___x_5384_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__5, &l_Nat_reduceDvd___redArg___closed__5_once, _init_l_Nat_reduceDvd___redArg___closed__5);
v___x_5385_ = l_Lean_Meta_matchesInstance(v_arg_5378_, v___x_5384_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5385_) == 0)
{
lean_object* v_a_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5472_; 
v_a_5386_ = lean_ctor_get(v___x_5385_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5385_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5388_ = v___x_5385_;
v_isShared_5389_ = v_isSharedCheck_5472_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_a_5386_);
lean_dec(v___x_5385_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5472_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
uint8_t v___x_5390_; 
v___x_5390_ = lean_unbox(v_a_5386_);
lean_dec(v_a_5386_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; lean_object* v___x_5393_; 
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v___x_5391_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 0, v___x_5391_);
v___x_5393_ = v___x_5388_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5391_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
else
{
lean_object* v___x_5395_; 
lean_del_object(v___x_5388_);
v___x_5395_ = l_Lean_Meta_getNatValue_x3f(v_arg_5375_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5463_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5398_ = v___x_5395_;
v_isShared_5399_ = v_isSharedCheck_5463_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5395_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5463_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
if (lean_obj_tag(v_a_5396_) == 1)
{
lean_object* v_val_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5458_; 
lean_del_object(v___x_5398_);
v_val_5400_ = lean_ctor_get(v_a_5396_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v_a_5396_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5402_ = v_a_5396_;
v_isShared_5403_ = v_isSharedCheck_5458_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_val_5400_);
lean_dec(v_a_5396_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5458_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_Lean_Meta_getNatValue_x3f(v_arg_5372_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5449_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5407_ = v___x_5404_;
v_isShared_5408_ = v_isSharedCheck_5449_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5404_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5449_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
if (lean_obj_tag(v_a_5405_) == 1)
{
lean_object* v_val_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5444_; 
v_val_5409_ = lean_ctor_get(v_a_5405_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_a_5405_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5411_ = v_a_5405_;
v_isShared_5412_ = v_isSharedCheck_5444_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_val_5409_);
lean_dec(v_a_5405_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5444_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; 
v___x_5413_ = lean_nat_mod(v_val_5409_, v_val_5400_);
lean_dec(v_val_5400_);
lean_dec(v_val_5409_);
v___x_5414_ = lean_unsigned_to_nat(0u);
v___x_5415_ = lean_nat_dec_eq(v___x_5413_, v___x_5414_);
lean_dec(v___x_5413_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v___x_5416_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_5417_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__8, &l_Nat_reduceDvd___redArg___closed__8_once, _init_l_Nat_reduceDvd___redArg___closed__8);
v___x_5418_ = l_Lean_eagerReflBoolTrue;
v___x_5419_ = l_Lean_mkApp3(v___x_5417_, v_arg_5375_, v_arg_5372_, v___x_5418_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5419_);
v___x_5421_ = v___x_5411_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5422_; lean_object* v___x_5424_; 
v___x_5422_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5422_, 0, v___x_5416_);
lean_ctor_set(v___x_5422_, 1, v___x_5421_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*2, v___x_5383_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set_tag(v___x_5402_, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5422_);
v___x_5424_ = v___x_5402_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5422_);
v___x_5424_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
lean_object* v___x_5426_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 0, v___x_5424_);
v___x_5426_ = v___x_5407_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
else
{
lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5435_; 
v___x_5430_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_5431_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__11, &l_Nat_reduceDvd___redArg___closed__11_once, _init_l_Nat_reduceDvd___redArg___closed__11);
v___x_5432_ = l_Lean_eagerReflBoolTrue;
v___x_5433_ = l_Lean_mkApp3(v___x_5431_, v_arg_5375_, v_arg_5372_, v___x_5432_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5433_);
v___x_5435_ = v___x_5411_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
lean_object* v___x_5436_; lean_object* v___x_5438_; 
v___x_5436_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5436_, 0, v___x_5430_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
lean_ctor_set_uint8(v___x_5436_, sizeof(void*)*2, v___x_5383_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set_tag(v___x_5402_, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5436_);
v___x_5438_ = v___x_5402_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5436_);
v___x_5438_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
lean_object* v___x_5440_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 0, v___x_5438_);
v___x_5440_ = v___x_5407_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
}
else
{
lean_object* v___x_5445_; lean_object* v___x_5447_; 
lean_dec(v_a_5405_);
lean_del_object(v___x_5402_);
lean_dec(v_val_5400_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v___x_5445_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 0, v___x_5445_);
v___x_5447_ = v___x_5407_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_del_object(v___x_5402_);
lean_dec(v_val_5400_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v_a_5450_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5404_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5404_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
}
else
{
lean_object* v___x_5459_; lean_object* v___x_5461_; 
lean_dec(v_a_5396_);
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v___x_5459_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 0, v___x_5459_);
v___x_5461_ = v___x_5398_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5459_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v_a_5464_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5395_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5395_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_dec_ref(v_arg_5375_);
lean_dec_ref(v_arg_5372_);
v_a_5473_ = lean_ctor_get(v___x_5385_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5385_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v___x_5385_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5385_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_a_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
}
}
}
}
v___jp_5365_:
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
v___x_5366_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 0, v___x_5366_);
v___x_5368_ = v___x_5363_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
v_a_5482_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5360_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5360_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg___boxed(lean_object* v_e_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Nat_reduceDvd___redArg(v_e_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object* v_e_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_){
_start:
{
lean_object* v___x_5506_; 
v___x_5506_ = l_Nat_reduceDvd___redArg(v_e_5497_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object* v_e_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v_res_5516_; 
v_res_5516_ = l_Nat_reduceDvd(v_e_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_);
lean_dec(v_a_5514_);
lean_dec_ref(v_a_5513_);
lean_dec(v_a_5512_);
lean_dec_ref(v_a_5511_);
lean_dec(v_a_5510_);
lean_dec_ref(v_a_5509_);
lean_dec(v_a_5508_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5537_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5538_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5535_, v___x_5536_, v___x_5537_);
return v___x_5538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19____boxed(lean_object* v_a_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_();
return v_res_5540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
return v___x_5542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5544_; uint8_t v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5545_ = 1;
v___x_5546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_);
v___x_5547_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5544_, v___x_5545_, v___x_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21____boxed(lean_object* v_a_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5551_; uint8_t v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5552_ = 1;
v___x_5553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_);
v___x_5554_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5551_, v___x_5552_, v___x_5553_);
return v___x_5554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23____boxed(lean_object* v_a_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
return v_res_5556_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
}
#ifdef __cplusplus
}
#endif
