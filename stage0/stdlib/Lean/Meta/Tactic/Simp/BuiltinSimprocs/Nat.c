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
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
extern lean_object* l_Lean_Nat_mkInstAdd;
extern lean_object* l_Lean_Nat_mkInstHAdd;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
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
static lean_once_cell_t l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_;
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19____boxed(lean_object*);
static lean_once_cell_t l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_;
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_;
LEAN_EXPORT lean_object* l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_;
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_once_cell_t l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_;
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23____boxed(lean_object*);
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
static lean_object* _init_l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_closure((void*)(l_Nat_reduceSucc___boxed), 9, 0);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_725_ = 1;
v___x_726_ = lean_obj_once(&l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_, &l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once, _init_l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_);
v___x_727_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_724_, v___x_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15____boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSucc_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_13_));
v___x_732_ = 1;
v___x_733_ = lean_obj_once(&l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_, &l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15__once, _init_l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_);
v___x_734_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_731_, v___x_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17____boxed(lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_845_ = lean_box(0);
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_848_ = lean_unsigned_to_nat(7u);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_850_ = lean_array_push(v___x_849_, v___x_847_);
v___x_851_ = lean_array_push(v___x_850_, v___x_846_);
v___x_852_ = lean_array_push(v___x_851_, v___x_846_);
v___x_853_ = lean_array_push(v___x_852_, v___x_846_);
v___x_854_ = lean_array_push(v___x_853_, v___x_845_);
v___x_855_ = lean_array_push(v___x_854_, v___x_845_);
v___x_856_ = lean_array_push(v___x_855_, v___x_845_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_);
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
static lean_object* _init_l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_closure((void*)(l_Nat_reduceAdd___boxed), 9, 0);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_868_ = 1;
v___x_869_ = lean_obj_once(&l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_, &l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once, _init_l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_);
v___x_870_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_867_, v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21____boxed(lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_875_ = 1;
v___x_876_ = lean_obj_once(&l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_, &l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21__once, _init_l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_);
v___x_877_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_874_, v___x_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23____boxed(lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_986_ = lean_unsigned_to_nat(7u);
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_986_);
v___x_988_ = lean_array_push(v___x_987_, v___x_985_);
v___x_989_ = lean_array_push(v___x_988_, v___x_984_);
v___x_990_ = lean_array_push(v___x_989_, v___x_984_);
v___x_991_ = lean_array_push(v___x_990_, v___x_984_);
v___x_992_ = lean_array_push(v___x_991_, v___x_983_);
v___x_993_ = lean_array_push(v___x_992_, v___x_983_);
v___x_994_ = lean_array_push(v___x_993_, v___x_983_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_);
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
static lean_object* _init_l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_closure((void*)(l_Nat_reduceMul___boxed), 9, 0);
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_1006_ = 1;
v___x_1007_ = lean_obj_once(&l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_, &l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once, _init_l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_);
v___x_1008_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1005_, v___x_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21____boxed(lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_));
v___x_1013_ = 1;
v___x_1014_ = lean_obj_once(&l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_, &l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21__once, _init_l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_);
v___x_1015_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1012_, v___x_1013_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23____boxed(lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1124_ = lean_unsigned_to_nat(7u);
v___x_1125_ = lean_mk_empty_array_with_capacity(v___x_1124_);
v___x_1126_ = lean_array_push(v___x_1125_, v___x_1123_);
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1122_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1122_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1122_);
v___x_1130_ = lean_array_push(v___x_1129_, v___x_1121_);
v___x_1131_ = lean_array_push(v___x_1130_, v___x_1121_);
v___x_1132_ = lean_array_push(v___x_1131_, v___x_1121_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_);
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
static lean_object* _init_l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_alloc_closure((void*)(l_Nat_reduceSub___boxed), 9, 0);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1144_ = 1;
v___x_1145_ = lean_obj_once(&l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_, &l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once, _init_l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_);
v___x_1146_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1143_, v___x_1144_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21____boxed(lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_));
v___x_1151_ = 1;
v___x_1152_ = lean_obj_once(&l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_, &l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21__once, _init_l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_);
v___x_1153_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1150_, v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23____boxed(lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1262_ = lean_unsigned_to_nat(7u);
v___x_1263_ = lean_mk_empty_array_with_capacity(v___x_1262_);
v___x_1264_ = lean_array_push(v___x_1263_, v___x_1261_);
v___x_1265_ = lean_array_push(v___x_1264_, v___x_1260_);
v___x_1266_ = lean_array_push(v___x_1265_, v___x_1260_);
v___x_1267_ = lean_array_push(v___x_1266_, v___x_1260_);
v___x_1268_ = lean_array_push(v___x_1267_, v___x_1259_);
v___x_1269_ = lean_array_push(v___x_1268_, v___x_1259_);
v___x_1270_ = lean_array_push(v___x_1269_, v___x_1259_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_);
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
static lean_object* _init_l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Nat_reduceDiv___boxed), 9, 0);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1282_ = 1;
v___x_1283_ = lean_obj_once(&l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_, &l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once, _init_l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_);
v___x_1284_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21____boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_));
v___x_1289_ = 1;
v___x_1290_ = lean_obj_once(&l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_, &l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21__once, _init_l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_);
v___x_1291_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23____boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1400_ = lean_unsigned_to_nat(7u);
v___x_1401_ = lean_mk_empty_array_with_capacity(v___x_1400_);
v___x_1402_ = lean_array_push(v___x_1401_, v___x_1399_);
v___x_1403_ = lean_array_push(v___x_1402_, v___x_1398_);
v___x_1404_ = lean_array_push(v___x_1403_, v___x_1398_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1398_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1397_);
v___x_1407_ = lean_array_push(v___x_1406_, v___x_1397_);
v___x_1408_ = lean_array_push(v___x_1407_, v___x_1397_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_);
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
static lean_object* _init_l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_closure((void*)(l_Nat_reduceMod___boxed), 9, 0);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1420_ = 1;
v___x_1421_ = lean_obj_once(&l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_, &l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once, _init_l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_);
v___x_1422_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1419_, v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21____boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_));
v___x_1427_ = 1;
v___x_1428_ = lean_obj_once(&l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_, &l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21__once, _init_l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_);
v___x_1429_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1426_, v___x_1427_, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23____boxed(lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
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
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1535_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1535_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1535_;
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
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1522_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1522_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1522_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_val_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1517_; 
lean_del_object(v___x_1473_);
v_val_1475_ = lean_ctor_get(v_a_1471_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1477_ = v_a_1471_;
v_isShared_1478_ = v_isSharedCheck_1517_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_val_1475_);
lean_dec(v_a_1471_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1517_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_Simp_getConfig___redArg(v_a_1438_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; uint8_t v_warnExponents_1481_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v_warnExponents_1481_ = lean_ctor_get_uint8(v_a_1480_, sizeof(void*)*3 + 25);
lean_dec(v_a_1480_);
lean_inc(v_val_1475_);
v___x_1482_ = l_Lean_checkExponent(v_val_1475_, v_warnExponents_1481_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1500_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1500_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1500_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_unbox(v_a_1483_);
lean_dec(v_a_1483_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_del_object(v___x_1477_);
lean_dec(v_val_1475_);
lean_dec(v_val_1469_);
v___x_1488_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1488_);
v___x_1490_ = v___x_1485_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_nat_pow(v_val_1469_, v_val_1475_);
lean_dec(v_val_1475_);
lean_dec(v_val_1469_);
v___x_1493_ = l_Lean_mkNatLit(v___x_1492_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1495_);
v___x_1497_ = v___x_1485_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1477_);
lean_dec(v_val_1475_);
lean_dec(v_val_1469_);
v_a_1501_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1482_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1482_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_del_object(v___x_1477_);
lean_dec(v_val_1475_);
lean_dec(v_val_1469_);
v_a_1509_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1479_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1479_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v_a_1471_);
lean_dec(v_val_1469_);
v___x_1518_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1518_);
v___x_1520_ = v___x_1473_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_val_1469_);
v_a_1523_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1470_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1470_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_a_1465_);
lean_dec_ref(v_arg_1449_);
v___x_1531_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1531_);
v___x_1533_ = v___x_1467_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_arg_1449_);
v_a_1536_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1464_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1464_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
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
LEAN_EXPORT lean_object* l_Nat_reducePow___redArg___boxed(lean_object* v_e_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Nat_reducePow___redArg(v_e_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec_ref(v_a_1545_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow(lean_object* v_e_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Nat_reducePow___redArg(v_e_1552_, v_a_1554_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___boxed(lean_object* v_e_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Nat_reducePow(v_e_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
return v_res_1571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1582_ = lean_unsigned_to_nat(7u);
v___x_1583_ = lean_mk_empty_array_with_capacity(v___x_1582_);
v___x_1584_ = lean_array_push(v___x_1583_, v___x_1581_);
v___x_1585_ = lean_array_push(v___x_1584_, v___x_1580_);
v___x_1586_ = lean_array_push(v___x_1585_, v___x_1579_);
v___x_1587_ = lean_array_push(v___x_1586_, v___x_1580_);
v___x_1588_ = lean_array_push(v___x_1587_, v___x_1579_);
v___x_1589_ = lean_array_push(v___x_1588_, v___x_1579_);
v___x_1590_ = lean_array_push(v___x_1589_, v___x_1579_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_);
v___x_1594_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1595_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1592_, v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19____boxed(lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
return v_res_1597_;
}
}
static lean_object* _init_l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_alloc_closure((void*)(l_Nat_reducePow___boxed), 9, 0);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1602_ = 1;
v___x_1603_ = lean_obj_once(&l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_, &l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once, _init_l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_);
v___x_1604_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1601_, v___x_1602_, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21____boxed(lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_));
v___x_1609_ = 1;
v___x_1610_ = lean_obj_once(&l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_, &l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21__once, _init_l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_);
v___x_1611_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1608_, v___x_1609_, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23____boxed(lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg(lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = ((lean_object*)(l_Nat_reduceAnd___redArg___closed__2));
v___x_1626_ = lean_unsigned_to_nat(6u);
v___x_1627_ = l_Lean_Expr_isAppOfArity(v_e_1619_, v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = l_Lean_Expr_appFn_x21(v_e_1619_);
v___x_1631_ = l_Lean_Expr_appArg_x21(v___x_1630_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = l_Lean_Meta_getNatValue_x3f(v___x_1631_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1674_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1674_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1674_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
if (lean_obj_tag(v_a_1633_) == 1)
{
lean_object* v_val_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_del_object(v___x_1635_);
v_val_1637_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_val_1637_);
lean_dec_ref(v_a_1633_);
v___x_1638_ = l_Lean_Expr_appArg_x21(v_e_1619_);
v___x_1639_ = l_Lean_Meta_getNatValue_x3f(v___x_1638_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v___x_1638_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1661_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1661_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1661_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
if (lean_obj_tag(v_a_1640_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1656_; 
v_val_1644_ = lean_ctor_get(v_a_1640_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1646_ = v_a_1640_;
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v_a_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = lean_nat_land(v_val_1637_, v_val_1644_);
lean_dec(v_val_1644_);
lean_dec(v_val_1637_);
v___x_1649_ = l_Lean_mkNatLit(v___x_1648_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1651_);
v___x_1653_ = v___x_1642_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v_a_1640_);
lean_dec(v_val_1637_);
v___x_1657_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1657_);
v___x_1659_ = v___x_1642_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_val_1637_);
v_a_1662_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1639_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1639_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_dec(v_a_1633_);
v___x_1670_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1670_);
v___x_1672_ = v___x_1635_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1632_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1632_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___redArg___boxed(lean_object* v_e_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Nat_reduceAnd___redArg(v_e_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec_ref(v_e_1683_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd(lean_object* v_e_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Nat_reduceAnd___redArg(v_e_1690_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___boxed(lean_object* v_e_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Nat_reduceAnd(v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_e_1700_);
return v_res_1709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1720_ = lean_unsigned_to_nat(7u);
v___x_1721_ = lean_mk_empty_array_with_capacity(v___x_1720_);
v___x_1722_ = lean_array_push(v___x_1721_, v___x_1719_);
v___x_1723_ = lean_array_push(v___x_1722_, v___x_1718_);
v___x_1724_ = lean_array_push(v___x_1723_, v___x_1718_);
v___x_1725_ = lean_array_push(v___x_1724_, v___x_1718_);
v___x_1726_ = lean_array_push(v___x_1725_, v___x_1717_);
v___x_1727_ = lean_array_push(v___x_1726_, v___x_1717_);
v___x_1728_ = lean_array_push(v___x_1727_, v___x_1717_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_);
v___x_1732_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1733_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1730_, v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19____boxed(lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
return v_res_1735_;
}
}
static lean_object* _init_l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_alloc_closure((void*)(l_Nat_reduceAnd___boxed), 9, 0);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1740_ = 1;
v___x_1741_ = lean_obj_once(&l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_, &l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once, _init_l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_);
v___x_1742_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1739_, v___x_1740_, v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21____boxed(lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_));
v___x_1747_ = 1;
v___x_1748_ = lean_obj_once(&l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_, &l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21__once, _init_l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_);
v___x_1749_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1746_, v___x_1747_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23____boxed(lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg(lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = ((lean_object*)(l_Nat_reduceXor___redArg___closed__2));
v___x_1764_ = lean_unsigned_to_nat(6u);
v___x_1765_ = l_Lean_Expr_isAppOfArity(v_e_1757_, v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l_Lean_Expr_appFn_x21(v_e_1757_);
v___x_1769_ = l_Lean_Expr_appArg_x21(v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_Meta_getNatValue_x3f(v___x_1769_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v___x_1769_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1812_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1812_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1812_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
if (lean_obj_tag(v_a_1771_) == 1)
{
lean_object* v_val_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1773_);
v_val_1775_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_val_1775_);
lean_dec_ref(v_a_1771_);
v___x_1776_ = l_Lean_Expr_appArg_x21(v_e_1757_);
v___x_1777_ = l_Lean_Meta_getNatValue_x3f(v___x_1776_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1799_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
if (lean_obj_tag(v_a_1778_) == 1)
{
lean_object* v_val_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1794_; 
v_val_1782_ = lean_ctor_get(v_a_1778_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1784_ = v_a_1778_;
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_val_1782_);
lean_dec(v_a_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1786_ = lean_nat_lxor(v_val_1775_, v_val_1782_);
lean_dec(v_val_1782_);
lean_dec(v_val_1775_);
v___x_1787_ = l_Lean_mkNatLit(v___x_1786_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1789_);
v___x_1791_ = v___x_1780_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec(v_a_1778_);
lean_dec(v_val_1775_);
v___x_1795_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1795_);
v___x_1797_ = v___x_1780_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_val_1775_);
v_a_1800_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1777_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1777_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_dec(v_a_1771_);
v___x_1808_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1808_);
v___x_1810_ = v___x_1773_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1770_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1770_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___redArg___boxed(lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Nat_reduceXor___redArg(v_e_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec_ref(v_e_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor(lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Nat_reduceXor___redArg(v_e_1828_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___boxed(lean_object* v_e_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Nat_reduceXor(v_e_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_e_1838_);
return v_res_1847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1858_ = lean_unsigned_to_nat(7u);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___x_1858_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1857_);
v___x_1861_ = lean_array_push(v___x_1860_, v___x_1856_);
v___x_1862_ = lean_array_push(v___x_1861_, v___x_1856_);
v___x_1863_ = lean_array_push(v___x_1862_, v___x_1856_);
v___x_1864_ = lean_array_push(v___x_1863_, v___x_1855_);
v___x_1865_ = lean_array_push(v___x_1864_, v___x_1855_);
v___x_1866_ = lean_array_push(v___x_1865_, v___x_1855_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_);
v___x_1870_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1871_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1868_, v___x_1869_, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19____boxed(lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
return v_res_1873_;
}
}
static lean_object* _init_l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_alloc_closure((void*)(l_Nat_reduceXor___boxed), 9, 0);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1878_ = 1;
v___x_1879_ = lean_obj_once(&l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_, &l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once, _init_l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_);
v___x_1880_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1877_, v___x_1878_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21____boxed(lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_));
v___x_1885_ = 1;
v___x_1886_ = lean_obj_once(&l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_, &l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21__once, _init_l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_);
v___x_1887_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1884_, v___x_1885_, v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23____boxed(lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg(lean_object* v_e_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1901_ = ((lean_object*)(l_Nat_reduceOr___redArg___closed__2));
v___x_1902_ = lean_unsigned_to_nat(6u);
v___x_1903_ = l_Lean_Expr_isAppOfArity(v_e_1895_, v___x_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = l_Lean_Expr_appFn_x21(v_e_1895_);
v___x_1907_ = l_Lean_Expr_appArg_x21(v___x_1906_);
lean_dec_ref(v___x_1906_);
v___x_1908_ = l_Lean_Meta_getNatValue_x3f(v___x_1907_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec_ref(v___x_1907_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1950_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1950_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1950_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
if (lean_obj_tag(v_a_1909_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1911_);
v_val_1913_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v_a_1909_);
v___x_1914_ = l_Lean_Expr_appArg_x21(v_e_1895_);
v___x_1915_ = l_Lean_Meta_getNatValue_x3f(v___x_1914_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1937_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1937_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1937_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
if (lean_obj_tag(v_a_1916_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1932_; 
v_val_1920_ = lean_ctor_get(v_a_1916_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_a_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1922_ = v_a_1916_;
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v_a_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = lean_nat_lor(v_val_1913_, v_val_1920_);
lean_dec(v_val_1920_);
lean_dec(v_val_1913_);
v___x_1925_ = l_Lean_mkNatLit(v___x_1924_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1925_);
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1927_);
v___x_1929_ = v___x_1918_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec(v_a_1916_);
lean_dec(v_val_1913_);
v___x_1933_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1933_);
v___x_1935_ = v___x_1918_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_val_1913_);
v_a_1938_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1915_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1915_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec(v_a_1909_);
v___x_1946_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1946_);
v___x_1948_ = v___x_1911_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1908_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1908_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___redArg___boxed(lean_object* v_e_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Nat_reduceOr___redArg(v_e_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec_ref(v_e_1959_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr(lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Nat_reduceOr___redArg(v_e_1966_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___boxed(lean_object* v_e_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Nat_reduceOr(v_e_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_e_1976_);
return v_res_1985_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_1993_ = lean_box(0);
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_1996_ = lean_unsigned_to_nat(7u);
v___x_1997_ = lean_mk_empty_array_with_capacity(v___x_1996_);
v___x_1998_ = lean_array_push(v___x_1997_, v___x_1995_);
v___x_1999_ = lean_array_push(v___x_1998_, v___x_1994_);
v___x_2000_ = lean_array_push(v___x_1999_, v___x_1994_);
v___x_2001_ = lean_array_push(v___x_2000_, v___x_1994_);
v___x_2002_ = lean_array_push(v___x_2001_, v___x_1993_);
v___x_2003_ = lean_array_push(v___x_2002_, v___x_1993_);
v___x_2004_ = lean_array_push(v___x_2003_, v___x_1993_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_);
v___x_2008_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2009_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2006_, v___x_2007_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19____boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
return v_res_2011_;
}
}
static lean_object* _init_l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_alloc_closure((void*)(l_Nat_reduceOr___boxed), 9, 0);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_2016_ = 1;
v___x_2017_ = lean_obj_once(&l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_, &l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once, _init_l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_);
v___x_2018_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2015_, v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21____boxed(lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_));
v___x_2023_ = 1;
v___x_2024_ = lean_obj_once(&l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_, &l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21__once, _init_l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_);
v___x_2025_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2022_, v___x_2023_, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23____boxed(lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg(lean_object* v_e_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2039_ = ((lean_object*)(l_Nat_reduceShiftLeft___redArg___closed__2));
v___x_2040_ = lean_unsigned_to_nat(6u);
v___x_2041_ = l_Lean_Expr_isAppOfArity(v_e_2033_, v___x_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = l_Lean_Expr_appFn_x21(v_e_2033_);
v___x_2045_ = l_Lean_Expr_appArg_x21(v___x_2044_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = l_Lean_Meta_getNatValue_x3f(v___x_2045_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
lean_dec_ref(v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2088_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2088_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2088_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
if (lean_obj_tag(v_a_2047_) == 1)
{
lean_object* v_val_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2049_);
v_val_2051_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_val_2051_);
lean_dec_ref(v_a_2047_);
v___x_2052_ = l_Lean_Expr_appArg_x21(v_e_2033_);
v___x_2053_ = l_Lean_Meta_getNatValue_x3f(v___x_2052_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
lean_dec_ref(v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2075_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2075_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2075_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
if (lean_obj_tag(v_a_2054_) == 1)
{
lean_object* v_val_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2070_; 
v_val_2058_ = lean_ctor_get(v_a_2054_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2054_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2060_ = v_a_2054_;
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_val_2058_);
lean_dec(v_a_2054_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2062_ = lean_nat_shiftl(v_val_2051_, v_val_2058_);
lean_dec(v_val_2058_);
lean_dec(v_val_2051_);
v___x_2063_ = l_Lean_mkNatLit(v___x_2062_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2063_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2065_);
v___x_2067_ = v___x_2056_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec(v_a_2054_);
lean_dec(v_val_2051_);
v___x_2071_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2071_);
v___x_2073_ = v___x_2056_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_val_2051_);
v_a_2076_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2053_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2053_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_a_2047_);
v___x_2084_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2084_);
v___x_2086_ = v___x_2049_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2046_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2046_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___redArg___boxed(lean_object* v_e_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Nat_reduceShiftLeft___redArg(v_e_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec_ref(v_e_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft(lean_object* v_e_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Nat_reduceShiftLeft___redArg(v_e_2104_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___boxed(lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Nat_reduceShiftLeft(v_e_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_e_2114_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2146_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2147_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2144_, v___x_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19____boxed(lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_();
return v_res_2149_;
}
}
static lean_object* _init_l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_alloc_closure((void*)(l_Nat_reduceShiftLeft___boxed), 9, 0);
v___x_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2154_ = 1;
v___x_2155_ = lean_obj_once(&l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_, &l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once, _init_l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_);
v___x_2156_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2153_, v___x_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21____boxed(lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_));
v___x_2161_ = 1;
v___x_2162_ = lean_obj_once(&l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_, &l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21__once, _init_l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_);
v___x_2163_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2160_, v___x_2161_, v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23____boxed(lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg(lean_object* v_e_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2177_ = ((lean_object*)(l_Nat_reduceShiftRight___redArg___closed__2));
v___x_2178_ = lean_unsigned_to_nat(6u);
v___x_2179_ = l_Lean_Expr_isAppOfArity(v_e_2171_, v___x_2177_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = l_Lean_Expr_appFn_x21(v_e_2171_);
v___x_2183_ = l_Lean_Expr_appArg_x21(v___x_2182_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = l_Lean_Meta_getNatValue_x3f(v___x_2183_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec_ref(v___x_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2226_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2226_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2226_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
if (lean_obj_tag(v_a_2185_) == 1)
{
lean_object* v_val_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_del_object(v___x_2187_);
v_val_2189_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_val_2189_);
lean_dec_ref(v_a_2185_);
v___x_2190_ = l_Lean_Expr_appArg_x21(v_e_2171_);
v___x_2191_ = l_Lean_Meta_getNatValue_x3f(v___x_2190_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec_ref(v___x_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2213_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2213_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2213_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
if (lean_obj_tag(v_a_2192_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2208_; 
v_val_2196_ = lean_ctor_get(v_a_2192_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2192_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2198_ = v_a_2192_;
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v_a_2192_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_nat_shiftr(v_val_2189_, v_val_2196_);
lean_dec(v_val_2196_);
lean_dec(v_val_2189_);
v___x_2201_ = l_Lean_mkNatLit(v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2203_);
v___x_2205_ = v___x_2194_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_dec(v_a_2192_);
lean_dec(v_val_2189_);
v___x_2209_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2209_);
v___x_2211_ = v___x_2194_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_val_2189_);
v_a_2214_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2191_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2191_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec(v_a_2185_);
v___x_2222_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2222_);
v___x_2224_ = v___x_2187_;
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
v_a_2227_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2184_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2184_);
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
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___redArg___boxed(lean_object* v_e_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Nat_reduceShiftRight___redArg(v_e_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec_ref(v_e_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight(lean_object* v_e_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Nat_reduceShiftRight___redArg(v_e_2242_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___boxed(lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Nat_reduceShiftRight(v_e_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2284_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2285_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2282_, v___x_2283_, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19____boxed(lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_();
return v_res_2287_;
}
}
static lean_object* _init_l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_alloc_closure((void*)(l_Nat_reduceShiftRight___boxed), 9, 0);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2292_ = 1;
v___x_2293_ = lean_obj_once(&l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_, &l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once, _init_l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_);
v___x_2294_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2291_, v___x_2292_, v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21____boxed(lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_));
v___x_2299_ = 1;
v___x_2300_ = lean_obj_once(&l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_, &l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21__once, _init_l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_);
v___x_2301_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2298_, v___x_2299_, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23____boxed(lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg(lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = ((lean_object*)(l_Nat_reduceGcd___redArg___closed__1));
v___x_2315_ = lean_unsigned_to_nat(2u);
v___x_2316_ = l_Lean_Expr_isAppOfArity(v_e_2308_, v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = l_Lean_Expr_appFn_x21(v_e_2308_);
v___x_2320_ = l_Lean_Expr_appArg_x21(v___x_2319_);
lean_dec_ref(v___x_2319_);
v___x_2321_ = l_Lean_Meta_getNatValue_x3f(v___x_2320_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec_ref(v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2363_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2363_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2363_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
if (lean_obj_tag(v_a_2322_) == 1)
{
lean_object* v_val_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_del_object(v___x_2324_);
v_val_2326_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_val_2326_);
lean_dec_ref(v_a_2322_);
v___x_2327_ = l_Lean_Expr_appArg_x21(v_e_2308_);
v___x_2328_ = l_Lean_Meta_getNatValue_x3f(v___x_2327_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec_ref(v___x_2327_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2350_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2350_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2350_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
if (lean_obj_tag(v_a_2329_) == 1)
{
lean_object* v_val_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_val_2333_ = lean_ctor_get(v_a_2329_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2335_ = v_a_2329_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_val_2333_);
lean_dec(v_a_2329_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = lean_nat_gcd(v_val_2326_, v_val_2333_);
lean_dec(v_val_2333_);
lean_dec(v_val_2326_);
v___x_2338_ = l_Lean_mkNatLit(v___x_2337_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2338_);
v___x_2340_ = v___x_2335_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2340_);
v___x_2342_ = v___x_2331_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
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
lean_object* v___x_2346_; lean_object* v___x_2348_; 
lean_dec(v_a_2329_);
lean_dec(v_val_2326_);
v___x_2346_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2346_);
v___x_2348_ = v___x_2331_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_val_2326_);
v_a_2351_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2328_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2328_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_dec(v_a_2322_);
v___x_2359_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2359_);
v___x_2361_ = v___x_2324_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2321_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2321_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___redArg___boxed(lean_object* v_e_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Nat_reduceGcd___redArg(v_e_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec_ref(v_e_2372_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd(lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Nat_reduceGcd___redArg(v_e_2379_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___boxed(lean_object* v_e_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Nat_reduceGcd(v_e_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_e_2389_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2416_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2417_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2414_, v___x_2415_, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14____boxed(lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_();
return v_res_2419_;
}
}
static lean_object* _init_l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_alloc_closure((void*)(l_Nat_reduceGcd___boxed), 9, 0);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2424_ = 1;
v___x_2425_ = lean_obj_once(&l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_, &l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once, _init_l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_);
v___x_2426_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2423_, v___x_2424_, v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16____boxed(lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_));
v___x_2431_ = 1;
v___x_2432_ = lean_obj_once(&l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_, &l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16__once, _init_l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_);
v___x_2433_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2430_, v___x_2431_, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18____boxed(lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg(lean_object* v_e_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2447_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_2448_ = lean_unsigned_to_nat(4u);
v___x_2449_ = l_Lean_Expr_isAppOfArity(v_e_2441_, v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec_ref(v_e_2441_);
v___x_2450_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = l_Lean_Expr_appFn_x21(v_e_2441_);
v___x_2453_ = l_Lean_Expr_appArg_x21(v___x_2452_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = l_Lean_Meta_getNatValue_x3f(v___x_2453_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec_ref(v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2486_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2486_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2486_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
if (lean_obj_tag(v_a_2455_) == 1)
{
lean_object* v_val_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_del_object(v___x_2457_);
v_val_2459_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_a_2455_);
v___x_2460_ = l_Lean_Expr_appArg_x21(v_e_2441_);
v___x_2461_ = l_Lean_Meta_getNatValue_x3f(v___x_2460_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec_ref(v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2473_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
if (lean_obj_tag(v_a_2462_) == 1)
{
lean_object* v_val_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2464_);
v_val_2466_ = lean_ctor_get(v_a_2462_, 0);
lean_inc(v_val_2466_);
lean_dec_ref(v_a_2462_);
v___x_2467_ = lean_nat_dec_lt(v_val_2459_, v_val_2466_);
lean_dec(v_val_2466_);
lean_dec(v_val_2459_);
v___x_2468_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2441_, v___x_2467_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_dec(v_a_2462_);
lean_dec(v_val_2459_);
lean_dec_ref(v_e_2441_);
v___x_2469_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2469_);
v___x_2471_ = v___x_2464_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_val_2459_);
lean_dec_ref(v_e_2441_);
v_a_2474_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2461_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
lean_dec(v_a_2455_);
lean_dec_ref(v_e_2441_);
v___x_2482_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2482_);
v___x_2484_ = v___x_2457_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v_e_2441_);
v_a_2487_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2454_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2454_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___redArg___boxed(lean_object* v_e_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Nat_reduceLT___redArg(v_e_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT(lean_object* v_e_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Nat_reduceLT___redArg(v_e_2502_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___boxed(lean_object* v_e_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Nat_reduceLT(v_e_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2542_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2543_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2540_, v___x_2541_, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20____boxed(lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_();
return v_res_2545_;
}
}
static lean_object* _init_l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_alloc_closure((void*)(l_Nat_reduceLT___boxed), 9, 0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2550_ = 1;
v___x_2551_ = lean_obj_once(&l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_, &l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once, _init_l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_);
v___x_2552_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2549_, v___x_2550_, v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22____boxed(lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2557_ = 1;
v___x_2558_ = lean_obj_once(&l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_, &l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22__once, _init_l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_);
v___x_2559_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2556_, v___x_2557_, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24____boxed(lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg(lean_object* v_e_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = ((lean_object*)(l_Nat_reduceGT___redArg___closed__2));
v___x_2574_ = lean_unsigned_to_nat(4u);
v___x_2575_ = l_Lean_Expr_isAppOfArity(v_e_2567_, v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v_e_2567_);
v___x_2576_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = l_Lean_Expr_appFn_x21(v_e_2567_);
v___x_2579_ = l_Lean_Expr_appArg_x21(v___x_2578_);
lean_dec_ref(v___x_2578_);
v___x_2580_ = l_Lean_Meta_getNatValue_x3f(v___x_2579_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec_ref(v___x_2579_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2612_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2612_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2612_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
if (lean_obj_tag(v_a_2581_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_del_object(v___x_2583_);
v_val_2585_ = lean_ctor_get(v_a_2581_, 0);
lean_inc(v_val_2585_);
lean_dec_ref(v_a_2581_);
v___x_2586_ = l_Lean_Expr_appArg_x21(v_e_2567_);
v___x_2587_ = l_Lean_Meta_getNatValue_x3f(v___x_2586_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec_ref(v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2599_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
if (lean_obj_tag(v_a_2588_) == 1)
{
lean_object* v_val_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2590_);
v_val_2592_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_val_2592_);
lean_dec_ref(v_a_2588_);
v___x_2593_ = lean_nat_dec_lt(v_val_2592_, v_val_2585_);
lean_dec(v_val_2585_);
lean_dec(v_val_2592_);
v___x_2594_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_2567_, v___x_2593_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec(v_a_2588_);
lean_dec(v_val_2585_);
lean_dec_ref(v_e_2567_);
v___x_2595_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
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
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_val_2585_);
lean_dec_ref(v_e_2567_);
v_a_2600_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2587_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2587_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_a_2581_);
lean_dec_ref(v_e_2567_);
v___x_2608_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2608_);
v___x_2610_ = v___x_2583_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_e_2567_);
v_a_2613_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2580_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2580_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___redArg___boxed(lean_object* v_e_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Nat_reduceGT___redArg(v_e_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT(lean_object* v_e_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Nat_reduceGT___redArg(v_e_2628_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___boxed(lean_object* v_e_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Nat_reduceGT(v_e_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_));
v___x_2655_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2656_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2653_, v___x_2654_, v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20____boxed(lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_();
return v_res_2658_;
}
}
static lean_object* _init_l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_alloc_closure((void*)(l_Nat_reduceGT___boxed), 9, 0);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2663_ = 1;
v___x_2664_ = lean_obj_once(&l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_, &l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once, _init_l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_);
v___x_2665_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2662_, v___x_2663_, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22____boxed(lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_));
v___x_2670_ = 1;
v___x_2671_ = lean_obj_once(&l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_, &l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22__once, _init_l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_);
v___x_2672_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2669_, v___x_2670_, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24____boxed(lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg(lean_object* v_e_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_2687_ = lean_unsigned_to_nat(4u);
v___x_2688_ = l_Lean_Expr_isAppOfArity(v_e_2680_, v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = l_Lean_Expr_appFn_x21(v_e_2680_);
v___x_2692_ = l_Lean_Expr_appArg_x21(v___x_2691_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = l_Lean_Meta_getNatValue_x3f(v___x_2692_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v___x_2692_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2738_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2738_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2738_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
if (lean_obj_tag(v_a_2694_) == 1)
{
lean_object* v_val_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2733_; 
v_val_2698_ = lean_ctor_get(v_a_2694_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2700_ = v_a_2694_;
v_isShared_2701_ = v_isSharedCheck_2733_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_val_2698_);
lean_dec(v_a_2694_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2733_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = l_Lean_Expr_appArg_x21(v_e_2680_);
v___x_2703_ = l_Lean_Meta_getNatValue_x3f(v___x_2702_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v___x_2702_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2724_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2724_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2724_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___y_2709_; 
if (lean_obj_tag(v_a_2704_) == 1)
{
lean_object* v_val_2716_; uint8_t v___x_2717_; 
lean_del_object(v___x_2696_);
v_val_2716_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_val_2716_);
lean_dec_ref(v_a_2704_);
v___x_2717_ = lean_nat_dec_eq(v_val_2698_, v_val_2716_);
lean_dec(v_val_2716_);
lean_dec(v_val_2698_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_2709_ = v___x_2718_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_2709_ = v___x_2719_;
goto v___jp_2708_;
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_del_object(v___x_2706_);
lean_dec(v_a_2704_);
lean_del_object(v___x_2700_);
lean_dec(v_val_2698_);
v___x_2720_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2720_);
v___x_2722_ = v___x_2696_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
v___jp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 0);
lean_ctor_set(v___x_2700_, 0, v___y_2709_);
v___x_2711_ = v___x_2700_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___y_2709_);
v___x_2711_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2711_);
v___x_2713_ = v___x_2706_;
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
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_del_object(v___x_2700_);
lean_dec(v_val_2698_);
lean_del_object(v___x_2696_);
v_a_2725_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2703_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2703_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_dec(v_a_2694_);
v___x_2734_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2734_);
v___x_2736_ = v___x_2696_;
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
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_a_2739_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2693_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2693_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___redArg___boxed(lean_object* v_e_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Nat_reduceBEq___redArg(v_e_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec_ref(v_e_2747_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq(lean_object* v_e_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Nat_reduceBEq___redArg(v_e_2754_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___boxed(lean_object* v_e_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Nat_reduceBEq(v_e_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2764_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2794_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2795_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2792_, v___x_2793_, v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20____boxed(lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_();
return v_res_2797_;
}
}
static lean_object* _init_l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_alloc_closure((void*)(l_Nat_reduceBEq___boxed), 9, 0);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2802_ = 1;
v___x_2803_ = lean_obj_once(&l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_, &l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once, _init_l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_);
v___x_2804_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2801_, v___x_2802_, v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22____boxed(lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_2809_ = 1;
v___x_2810_ = lean_obj_once(&l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_, &l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22__once, _init_l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_);
v___x_2811_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2808_, v___x_2809_, v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24____boxed(lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg(lean_object* v_e_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2823_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_2824_ = lean_unsigned_to_nat(4u);
v___x_2825_ = l_Lean_Expr_isAppOfArity(v_e_2817_, v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = l_Lean_Expr_appFn_x21(v_e_2817_);
v___x_2829_ = l_Lean_Expr_appArg_x21(v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = l_Lean_Meta_getNatValue_x3f(v___x_2829_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2876_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2876_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2876_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
if (lean_obj_tag(v_a_2831_) == 1)
{
lean_object* v_val_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2871_; 
v_val_2835_ = lean_ctor_get(v_a_2831_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2837_ = v_a_2831_;
v_isShared_2838_ = v_isSharedCheck_2871_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_val_2835_);
lean_dec(v_a_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2871_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Lean_Expr_appArg_x21(v_e_2817_);
v___x_2840_ = l_Lean_Meta_getNatValue_x3f(v___x_2839_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2862_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___y_2846_; 
if (lean_obj_tag(v_a_2841_) == 1)
{
lean_object* v_val_2855_; uint8_t v___x_2856_; 
lean_del_object(v___x_2833_);
v_val_2855_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_val_2855_);
lean_dec_ref(v_a_2841_);
v___x_2856_ = lean_nat_dec_eq(v_val_2835_, v_val_2855_);
lean_dec(v_val_2855_);
lean_dec(v_val_2835_);
if (v___x_2856_ == 0)
{
if (v___x_2825_ == 0)
{
goto v___jp_2853_;
}
else
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_2846_ = v___x_2857_;
goto v___jp_2845_;
}
}
else
{
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_del_object(v___x_2843_);
lean_dec(v_a_2841_);
lean_del_object(v___x_2837_);
lean_dec(v_val_2835_);
v___x_2858_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2858_);
v___x_2860_ = v___x_2833_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
v___jp_2845_:
{
lean_object* v___x_2848_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 0);
lean_ctor_set(v___x_2837_, 0, v___y_2846_);
v___x_2848_ = v___x_2837_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___y_2846_);
v___x_2848_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2848_);
v___x_2850_ = v___x_2843_;
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
}
v___jp_2853_:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_2846_ = v___x_2854_;
goto v___jp_2845_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2837_);
lean_dec(v_val_2835_);
lean_del_object(v___x_2833_);
v_a_2863_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2840_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2840_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_dec(v_a_2831_);
v___x_2872_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2872_);
v___x_2874_ = v___x_2833_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v_a_2877_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2830_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2830_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___redArg___boxed(lean_object* v_e_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Nat_reduceBNe___redArg(v_e_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec_ref(v_e_2885_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe(lean_object* v_e_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Nat_reduceBNe___redArg(v_e_2892_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___boxed(lean_object* v_e_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Nat_reduceBNe(v_e_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_e_2902_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2932_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2933_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2930_, v___x_2931_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20____boxed(lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_();
return v_res_2935_;
}
}
static lean_object* _init_l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_alloc_closure((void*)(l_Nat_reduceBNe___boxed), 9, 0);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2940_ = 1;
v___x_2941_ = lean_obj_once(&l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_, &l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once, _init_l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_);
v___x_2942_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2939_, v___x_2940_, v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22____boxed(lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_2947_ = 1;
v___x_2948_ = lean_obj_once(&l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_, &l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22__once, _init_l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_);
v___x_2949_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2946_, v___x_2947_, v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24____boxed(lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg(lean_object* v_e_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___x_2960_; 
lean_inc_ref(v_e_2957_);
v___x_2960_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2981_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = l_Lean_Expr_cleanupAnnotations(v_a_2961_);
v___x_2971_ = l_Lean_Expr_isApp(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec_ref(v___x_2970_);
lean_dec_ref(v_e_2957_);
goto v___jp_2965_;
}
else
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2970_);
v___x_2973_ = l_Lean_Expr_isApp(v___x_2972_);
if (v___x_2973_ == 0)
{
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_e_2957_);
goto v___jp_2965_;
}
else
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2972_);
v___x_2975_ = l_Lean_Expr_isApp(v___x_2974_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v___x_2974_);
lean_dec_ref(v_e_2957_);
goto v___jp_2965_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2974_);
v___x_2977_ = ((lean_object*)(l_Nat_isValue___redArg___closed__2));
v___x_2978_ = l_Lean_Expr_isConstOf(v___x_2976_, v___x_2977_);
lean_dec_ref(v___x_2976_);
if (v___x_2978_ == 0)
{
lean_dec_ref(v_e_2957_);
goto v___jp_2965_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_del_object(v___x_2963_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_e_2957_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
}
}
v___jp_2965_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = ((lean_object*)(l_Nat_reduceUnary___redArg___closed__0));
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2966_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v_e_2957_);
v_a_2982_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2960_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2960_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___redArg___boxed(lean_object* v_e_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Nat_isValue___redArg(v_e_2990_, v_a_2991_);
lean_dec(v_a_2991_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue(lean_object* v_e_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Nat_isValue___redArg(v_e_2994_, v_a_2999_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___boxed(lean_object* v_e_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Nat_isValue(v_e_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3033_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3034_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3031_, v___x_3032_, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16____boxed(lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_();
return v_res_3036_;
}
}
static lean_object* _init_l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_alloc_closure((void*)(l_Nat_isValue___boxed), 9, 0);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_));
v___x_3041_ = 1;
v___x_3042_ = lean_obj_once(&l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_, &l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18__once, _init_l_Nat_isValue___regBuiltin_Nat_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_);
v___x_3043_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3040_, v___x_3041_, v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18____boxed(lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx(lean_object* v_x_3046_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_unsigned_to_nat(0u);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_unsigned_to_nat(1u);
return v___x_3048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx___boxed(lean_object* v_x_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorIdx(v_x_3049_);
lean_dec_ref(v_x_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(lean_object* v_t_3051_, lean_object* v_k_3052_){
_start:
{
if (lean_obj_tag(v_t_3051_) == 0)
{
lean_object* v_n_3053_; lean_object* v___x_3054_; 
v_n_3053_ = lean_ctor_get(v_t_3051_, 0);
lean_inc(v_n_3053_);
lean_dec_ref(v_t_3051_);
v___x_3054_ = lean_apply_1(v_k_3052_, v_n_3053_);
return v___x_3054_;
}
else
{
lean_object* v_e_3055_; lean_object* v_o_3056_; lean_object* v_n_3057_; lean_object* v___x_3058_; 
v_e_3055_ = lean_ctor_get(v_t_3051_, 0);
lean_inc_ref(v_e_3055_);
v_o_3056_ = lean_ctor_get(v_t_3051_, 1);
lean_inc_ref(v_o_3056_);
v_n_3057_ = lean_ctor_get(v_t_3051_, 2);
lean_inc(v_n_3057_);
lean_dec_ref(v_t_3051_);
v___x_3058_ = lean_apply_3(v_k_3052_, v_e_3055_, v_o_3056_, v_n_3057_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(lean_object* v_motive_3059_, lean_object* v_ctorIdx_3060_, lean_object* v_t_3061_, lean_object* v_h_3062_, lean_object* v_k_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3061_, v_k_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___boxed(lean_object* v_motive_3065_, lean_object* v_ctorIdx_3066_, lean_object* v_t_3067_, lean_object* v_h_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim(v_motive_3065_, v_ctorIdx_3066_, v_t_3067_, v_h_3068_, v_k_3069_);
lean_dec(v_ctorIdx_3066_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim___redArg(lean_object* v_t_3071_, lean_object* v_const_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3071_, v_const_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_const_elim(lean_object* v_motive_3074_, lean_object* v_t_3075_, lean_object* v_h_3076_, lean_object* v_const_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3075_, v_const_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim___redArg(lean_object* v_t_3079_, lean_object* v_offset_3080_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3079_, v_offset_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_offset_elim(lean_object* v_motive_3082_, lean_object* v_t_3083_, lean_object* v_h_3084_, lean_object* v_offset_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_ctorElim___redArg(v_t_3083_, v_offset_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3102_ = lean_unsigned_to_nat(6u);
v___x_3103_ = l_Lean_Expr_isAppOfArity(v_e_3095_, v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__2));
v___x_3105_ = lean_unsigned_to_nat(4u);
v___x_3106_ = l_Lean_Expr_isAppOfArity(v_e_3095_, v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___closed__3));
v___x_3108_ = lean_unsigned_to_nat(2u);
v___x_3109_ = l_Lean_Expr_isAppOfArity(v_e_3095_, v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3110_ = ((lean_object*)(l_Nat_reduceSucc___redArg___closed__2));
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = l_Lean_Expr_isAppOfArity(v_e_3095_, v___x_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_box(0);
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
else
{
lean_object* v_b_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_b_3115_ = l_Lean_Expr_appArg_x21(v_e_3095_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_b_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3111_);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = l_Lean_Expr_appArg_x21(v_e_3095_);
v___x_3120_ = l_Lean_Meta_getNatValue_x3f(v___x_3119_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec_ref(v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3143_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3143_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3143_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
if (lean_obj_tag(v_a_3121_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3138_; 
v_val_3125_ = lean_ctor_get(v_a_3121_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_a_3121_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3127_ = v_a_3121_;
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_val_3125_);
lean_dec(v_a_3121_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_b_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3129_ = l_Lean_Expr_appFn_x21(v_e_3095_);
v_b_3130_ = l_Lean_Expr_appArg_x21(v___x_3129_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_b_3130_);
lean_ctor_set(v___x_3131_, 1, v_val_3125_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3131_);
v___x_3133_ = v___x_3127_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3135_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3133_);
v___x_3135_ = v___x_3123_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
lean_dec(v_a_3121_);
v___x_3139_ = lean_box(0);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3139_);
v___x_3141_ = v___x_3123_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3120_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3120_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_inst_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3152_ = l_Lean_Expr_appFn_x21(v_e_3095_);
v___x_3153_ = l_Lean_Expr_appFn_x21(v___x_3152_);
v_inst_3154_ = l_Lean_Expr_appArg_x21(v___x_3153_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = l_Lean_Nat_mkInstAdd;
v___x_3156_ = l_Lean_Meta_matchesInstance(v_inst_3154_, v___x_3155_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3198_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3198_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3198_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_unbox(v_a_3157_);
lean_dec(v_a_3157_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_dec_ref(v___x_3152_);
v___x_3162_ = lean_box(0);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3162_);
v___x_3164_ = v___x_3159_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_del_object(v___x_3159_);
v___x_3166_ = l_Lean_Expr_appArg_x21(v_e_3095_);
v___x_3167_ = l_Lean_Meta_getNatValue_x3f(v___x_3166_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec_ref(v___x_3166_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3189_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3189_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
if (lean_obj_tag(v_a_3168_) == 1)
{
lean_object* v_val_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3184_; 
v_val_3172_ = lean_ctor_get(v_a_3168_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_a_3168_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3174_ = v_a_3168_;
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_val_3172_);
lean_dec(v_a_3168_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = l_Lean_Expr_appArg_x21(v___x_3152_);
lean_dec_ref(v___x_3152_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v_val_3172_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3177_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3179_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_dec(v_a_3168_);
lean_dec_ref(v___x_3152_);
v___x_3185_ = lean_box(0);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3185_);
v___x_3187_ = v___x_3170_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___x_3152_);
v_a_3190_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3167_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3167_);
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
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v___x_3152_);
v_a_3199_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3156_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3156_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_inst_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3207_ = l_Lean_Expr_appFn_x21(v_e_3095_);
v___x_3208_ = l_Lean_Expr_appFn_x21(v___x_3207_);
v_inst_3209_ = l_Lean_Expr_appArg_x21(v___x_3208_);
lean_dec_ref(v___x_3208_);
v___x_3210_ = l_Lean_Nat_mkInstHAdd;
v___x_3211_ = l_Lean_Meta_matchesInstance(v_inst_3209_, v___x_3210_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3253_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3253_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3253_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
lean_dec_ref(v___x_3207_);
v___x_3217_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3217_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_del_object(v___x_3214_);
v___x_3221_ = l_Lean_Expr_appArg_x21(v_e_3095_);
v___x_3222_ = l_Lean_Meta_getNatValue_x3f(v___x_3221_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec_ref(v___x_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3244_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3244_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3244_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
if (lean_obj_tag(v_a_3223_) == 1)
{
lean_object* v_val_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3239_; 
v_val_3227_ = lean_ctor_get(v_a_3223_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3229_ = v_a_3223_;
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_val_3227_);
lean_dec(v_a_3223_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3231_ = l_Lean_Expr_appArg_x21(v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_val_3227_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3232_);
v___x_3234_ = v___x_3229_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3236_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3234_);
v___x_3236_ = v___x_3225_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_dec(v_a_3223_);
lean_dec_ref(v___x_3207_);
v___x_3240_ = lean_box(0);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3240_);
v___x_3242_ = v___x_3225_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___x_3207_);
v_a_3245_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3222_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3222_);
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
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___x_3207_);
v_a_3254_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3211_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3211_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg___boxed(lean_object* v_e_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec_ref(v_e_3262_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(lean_object* v_e_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3269_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___boxed(lean_object* v_e_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset(v_e_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_e_3279_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(lean_object* v_e_3289_, lean_object* v_inc_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_e_3296_; lean_object* v___x_3297_; 
v_e_3296_ = l_Lean_Expr_consumeMData(v_e_3289_);
lean_dec_ref(v_e_3289_);
v___x_3297_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_asOffset___redArg(v_e_3296_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
if (lean_obj_tag(v_a_3298_) == 0)
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_nat_dec_eq(v_inc_3290_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3309_; 
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3310_);
v___x_3302_ = v___x_3297_;
v_isShared_3303_ = v_isSharedCheck_3309_;
goto v_resetjp_3301_;
}
else
{
lean_dec(v___x_3297_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3309_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_e_3296_);
lean_ctor_set(v___x_3304_, 1, v_inc_3290_);
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3305_);
v___x_3307_ = v___x_3302_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
else
{
lean_dec_ref(v_e_3296_);
lean_dec(v_inc_3290_);
return v___x_3297_;
}
}
else
{
lean_object* v_val_3311_; lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v___x_3314_; 
lean_dec_ref(v___x_3297_);
lean_dec_ref(v_e_3296_);
v_val_3311_ = lean_ctor_get(v_a_3298_, 0);
lean_inc(v_val_3311_);
lean_dec_ref(v_a_3298_);
v_fst_3312_ = lean_ctor_get(v_val_3311_, 0);
lean_inc(v_fst_3312_);
v_snd_3313_ = lean_ctor_get(v_val_3311_, 1);
lean_inc(v_snd_3313_);
lean_dec(v_val_3311_);
v___x_3314_ = lean_nat_add(v_inc_3290_, v_snd_3313_);
lean_dec(v_snd_3313_);
lean_dec(v_inc_3290_);
v_e_3289_ = v_fst_3312_;
v_inc_3290_ = v___x_3314_;
goto _start;
}
}
else
{
lean_dec_ref(v_e_3296_);
lean_dec(v_inc_3290_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg___boxed(lean_object* v_e_3316_, lean_object* v_inc_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3316_, v_inc_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(lean_object* v_e_3324_, lean_object* v_inc_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3324_, v_inc_3325_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___boxed(lean_object* v_e_3335_, lean_object* v_inc_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux(v_e_3335_, v_inc_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(lean_object* v_e_3346_, lean_object* v_inc_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Meta_getNatValue_x3f(v_e_3346_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3404_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3404_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3404_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
if (lean_obj_tag(v_a_3354_) == 0)
{
lean_object* v___x_3358_; 
lean_del_object(v___x_3356_);
v___x_3358_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExprAux___redArg(v_e_3346_, v_inc_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3382_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3382_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3382_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
if (lean_obj_tag(v_a_3359_) == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(0);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
lean_object* v_val_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3381_; 
v_val_3367_ = lean_ctor_get(v_a_3359_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3359_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3369_ = v_a_3359_;
v_isShared_3370_ = v_isSharedCheck_3381_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_val_3367_);
lean_dec(v_a_3359_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3381_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v_fst_3371_ = lean_ctor_get(v_val_3367_, 0);
lean_inc(v_fst_3371_);
v_snd_3372_ = lean_ctor_get(v_val_3367_, 1);
lean_inc(v_snd_3372_);
lean_dec(v_val_3367_);
lean_inc(v_snd_3372_);
v___x_3373_ = l_Lean_mkNatLit(v_snd_3372_);
v___x_3374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3374_, 0, v_fst_3371_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
lean_ctor_set(v___x_3374_, 2, v_snd_3372_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3374_);
v___x_3376_ = v___x_3369_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3376_);
v___x_3378_ = v___x_3361_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_a_3383_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3358_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3358_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_e_3346_);
v_val_3391_ = lean_ctor_get(v_a_3354_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_a_3354_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3393_ = v_a_3354_;
v_isShared_3394_ = v_isSharedCheck_3403_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_val_3391_);
lean_dec(v_a_3354_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3403_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3395_ = lean_nat_add(v_val_3391_, v_inc_3347_);
lean_dec(v_inc_3347_);
lean_dec(v_val_3391_);
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3396_);
v___x_3398_ = v___x_3393_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3398_);
v___x_3400_ = v___x_3356_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_inc_3347_);
lean_dec_ref(v_e_3346_);
v_a_3405_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3353_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3353_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg___boxed(lean_object* v_e_3413_, lean_object* v_inc_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3413_, v_inc_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(lean_object* v_e_3421_, lean_object* v_inc_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_e_3421_, v_inc_3422_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___boxed(lean_object* v_e_3432_, lean_object* v_inc_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f(v_e_3432_, v_inc_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
return v_res_3442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v_nat_3445_; 
v___x_3443_ = lean_box(0);
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_));
v_nat_3445_ = l_Lean_mkConst(v___x_3444_, v___x_3443_);
return v_nat_3445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__2));
v___x_3454_ = l_Lean_mkConst(v___x_3453_, v___x_3452_);
return v___x_3454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_box(0);
v___x_3459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__6));
v___x_3460_ = l_Lean_mkConst(v___x_3459_, v___x_3458_);
return v___x_3460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8(void){
_start:
{
lean_object* v___x_3461_; lean_object* v_nat_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__7);
v_nat_3462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3463_ = lean_unsigned_to_nat(2u);
v___x_3464_ = lean_mk_empty_array_with_capacity(v___x_3463_);
v___x_3465_ = lean_array_push(v___x_3464_, v_nat_3462_);
v___x_3466_ = lean_array_push(v___x_3465_, v___x_3461_);
return v___x_3466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v_instHAdd_3469_; 
v___x_3467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__8);
v___x_3468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__4);
v_instHAdd_3469_ = l_Lean_mkAppN(v___x_3468_, v___x_3467_);
return v_instHAdd_3469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3477_ = ((lean_object*)(l_Nat_reduceAdd___redArg___closed__2));
v___x_3478_ = l_Lean_mkConst(v___x_3477_, v___x_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13(void){
_start:
{
lean_object* v_nat_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_nat_3479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3480_ = lean_unsigned_to_nat(6u);
v___x_3481_ = lean_mk_empty_array_with_capacity(v___x_3480_);
v___x_3482_ = lean_array_push(v___x_3481_, v_nat_3479_);
return v___x_3482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14(void){
_start:
{
lean_object* v_nat_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_nat_3483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__13);
v___x_3485_ = lean_array_push(v___x_3484_, v_nat_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15(void){
_start:
{
lean_object* v_nat_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_nat_3486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__14);
v___x_3488_ = lean_array_push(v___x_3487_, v_nat_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16(void){
_start:
{
lean_object* v_instHAdd_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_instHAdd_3489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__9);
v___x_3490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3491_ = lean_array_push(v___x_3490_, v_instHAdd_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(lean_object* v_x_3492_, lean_object* v_y_3493_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__12);
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__16);
v___x_3496_ = lean_array_push(v___x_3495_, v_x_3492_);
v___x_3497_ = lean_array_push(v___x_3496_, v_y_3493_);
v___x_3498_ = l_Lean_mkAppN(v___x_3494_, v___x_3497_);
lean_dec_ref(v___x_3497_);
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v_instSub_3504_; 
v___x_3502_ = lean_box(0);
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__1));
v_instSub_3504_ = l_Lean_mkConst(v___x_3503_, v___x_3502_);
return v_instSub_3504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__4));
v___x_3510_ = l_Lean_mkConst(v___x_3509_, v___x_3508_);
return v___x_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6(void){
_start:
{
lean_object* v_instSub_3511_; lean_object* v_nat_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_instSub_3511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__2);
v_nat_3512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3513_ = lean_unsigned_to_nat(2u);
v___x_3514_ = lean_mk_empty_array_with_capacity(v___x_3513_);
v___x_3515_ = lean_array_push(v___x_3514_, v_nat_3512_);
v___x_3516_ = lean_array_push(v___x_3515_, v_instSub_3511_);
return v___x_3516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_instHSub_3519_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__6);
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__5);
v_instHSub_3519_ = l_Lean_mkAppN(v___x_3518_, v___x_3517_);
return v_instHSub_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__11));
v___x_3521_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_3522_ = l_Lean_mkConst(v___x_3521_, v___x_3520_);
return v___x_3522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9(void){
_start:
{
lean_object* v_instHSub_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_instHSub_3523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__7);
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__15);
v___x_3525_ = lean_array_push(v___x_3524_, v_instHSub_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(lean_object* v_x_3526_, lean_object* v_y_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__8);
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat___closed__9);
v___x_3530_ = lean_array_push(v___x_3529_, v_x_3526_);
v___x_3531_ = lean_array_push(v___x_3530_, v_y_3527_);
v___x_3532_ = l_Lean_mkAppN(v___x_3528_, v___x_3531_);
lean_dec_ref(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_box(0);
v___x_3537_ = l_Lean_Level_succ___override(v___x_3536_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__2);
v___x_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v___x_3538_);
return v___x_3540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__3);
v___x_3542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_3543_ = l_Lean_mkConst(v___x_3542_, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3545_ = lean_unsigned_to_nat(3u);
v___x_3546_ = lean_mk_empty_array_with_capacity(v___x_3545_);
v___x_3547_ = lean_array_push(v___x_3546_, v___x_3544_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(lean_object* v_x_3548_, lean_object* v_y_3549_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__4);
v___x_3551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__5);
v___x_3552_ = lean_array_push(v___x_3551_, v_x_3548_);
v___x_3553_ = lean_array_push(v___x_3552_, v_y_3549_);
v___x_3554_ = l_Lean_mkAppN(v___x_3550_, v___x_3553_);
lean_dec_ref(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__1));
v___x_3560_ = l_Lean_mkConst(v___x_3559_, v___x_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_box(0);
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__4));
v___x_3566_ = l_Lean_mkConst(v___x_3565_, v___x_3564_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__5);
v___x_3568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3569_ = lean_unsigned_to_nat(2u);
v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_3569_);
v___x_3571_ = lean_array_push(v___x_3570_, v___x_3568_);
v___x_3572_ = lean_array_push(v___x_3571_, v___x_3567_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__6);
v___x_3574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__2);
v___x_3575_ = l_Lean_mkAppN(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance(void){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance___closed__7);
return v___x_3576_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3578_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_3579_ = l_Lean_mkConst(v___x_3578_, v___x_3577_);
return v___x_3579_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__0);
v___x_3581_ = lean_unsigned_to_nat(4u);
v___x_3582_ = lean_mk_empty_array_with_capacity(v___x_3581_);
v___x_3583_ = lean_array_push(v___x_3582_, v___x_3580_);
return v___x_3583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance;
v___x_3585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3586_ = lean_array_push(v___x_3585_, v___x_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(lean_object* v_x_3587_, lean_object* v_y_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__0);
v___x_3590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3591_ = lean_array_push(v___x_3590_, v_x_3587_);
v___x_3592_ = lean_array_push(v___x_3591_, v_y_3588_);
v___x_3593_ = l_Lean_mkAppN(v___x_3589_, v___x_3592_);
lean_dec_ref(v___x_3592_);
return v___x_3593_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3595_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_3596_ = l_Lean_mkConst(v___x_3595_, v___x_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(lean_object* v_x_3597_, lean_object* v_y_3598_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat___closed__0);
v___x_3600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__2);
v___x_3601_ = lean_array_push(v___x_3600_, v_x_3597_);
v___x_3602_ = lean_array_push(v___x_3601_, v_y_3598_);
v___x_3603_ = l_Lean_mkAppN(v___x_3599_, v___x_3602_);
lean_dec_ref(v___x_3602_);
return v___x_3603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_3611_ = l_Lean_Expr_const___override(v___x_3610_, v___x_3609_);
return v___x_3611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = lean_box(0);
v___x_3616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__5));
v___x_3617_ = l_Lean_mkConst(v___x_3616_, v___x_3615_);
return v___x_3617_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__6);
v___x_3619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3620_ = lean_array_push(v___x_3619_, v___x_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(lean_object* v_x_3621_, lean_object* v_y_3622_){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__3);
v___x_3624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__7);
v___x_3625_ = lean_array_push(v___x_3624_, v_x_3621_);
v___x_3626_ = lean_array_push(v___x_3625_, v_y_3622_);
v___x_3627_ = l_Lean_mkAppN(v___x_3623_, v___x_3626_);
lean_dec_ref(v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGENat(lean_object* v_x_3628_, lean_object* v_y_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_y_3629_, v_x_3628_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat___closed__3));
v___x_3632_ = ((lean_object*)(l_Nat_reduceLT___redArg___closed__2));
v___x_3633_ = l_Lean_Expr_const___override(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = lean_box(0);
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__2));
v___x_3639_ = l_Lean_mkConst(v___x_3638_, v___x_3637_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__3);
v___x_3641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat___closed__1);
v___x_3642_ = lean_array_push(v___x_3641_, v___x_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(lean_object* v_x_3643_, lean_object* v_y_3644_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__0);
v___x_3646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat___closed__4);
v___x_3647_ = lean_array_push(v___x_3646_, v_x_3643_);
v___x_3648_ = lean_array_push(v___x_3647_, v_y_3644_);
v___x_3649_ = l_Lean_mkAppN(v___x_3645_, v___x_3648_);
lean_dec_ref(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkGTNat(lean_object* v_x_3650_, lean_object* v_y_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_3651_, v_x_3650_);
return v___x_3652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_box(0);
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__1));
v___x_3658_ = l_Lean_mkConst(v___x_3657_, v___x_3656_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(lean_object* v_p_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___x_3665_; 
lean_inc_ref(v_p_3659_);
v___x_3665_ = l_Lean_Meta_mkDecide(v_p_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v___x_3665_);
v___x_3667_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___x_3668_ = l_Lean_Meta_mkEqRefl(v___x_3667_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3684_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3684_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3684_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___closed__2);
v___x_3674_ = l_Lean_Expr_appArg_x21(v_a_3666_);
lean_dec(v_a_3666_);
v___x_3675_ = lean_unsigned_to_nat(3u);
v___x_3676_ = lean_mk_empty_array_with_capacity(v___x_3675_);
v___x_3677_ = lean_array_push(v___x_3676_, v_p_3659_);
v___x_3678_ = lean_array_push(v___x_3677_, v___x_3674_);
v___x_3679_ = lean_array_push(v___x_3678_, v_a_3669_);
v___x_3680_ = l_Lean_mkAppN(v___x_3673_, v___x_3679_);
lean_dec_ref(v___x_3679_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3680_);
v___x_3682_ = v___x_3671_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_dec(v_a_3666_);
lean_dec_ref(v_p_3659_);
return v___x_3668_;
}
}
else
{
lean_dec_ref(v_p_3659_);
return v___x_3665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue___boxed(lean_object* v_p_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v_p_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg(lean_object* v_expr_3692_, lean_object* v_nm_3693_, lean_object* v_args_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v_env_3698_; uint8_t v___x_3699_; uint8_t v___x_3700_; 
v___x_3697_ = lean_st_ref_get(v_a_3695_);
v_env_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc_ref(v_env_3698_);
lean_dec(v___x_3697_);
v___x_3699_ = 1;
lean_inc(v_nm_3693_);
v___x_3700_ = l_Lean_Environment_contains(v_env_3698_, v_nm_3693_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec(v_nm_3693_);
lean_dec_ref(v_expr_3692_);
v___x_3701_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3703_ = lean_box(0);
v___x_3704_ = l_Lean_mkConst(v_nm_3693_, v___x_3703_);
v___x_3705_ = l_Lean_mkAppN(v___x_3704_, v_args_3694_);
v___x_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3707_, 0, v_expr_3692_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
lean_ctor_set_uint8(v___x_3707_, sizeof(void*)*2, v___x_3699_);
v___x_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___redArg___boxed(lean_object* v_expr_3710_, lean_object* v_nm_3711_, lean_object* v_args_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Nat_applySimprocConst___redArg(v_expr_3710_, v_nm_3711_, v_args_3712_, v_a_3713_);
lean_dec(v_a_3713_);
lean_dec_ref(v_args_3712_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst(lean_object* v_expr_3716_, lean_object* v_nm_3717_, lean_object* v_args_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Nat_applySimprocConst___redArg(v_expr_3716_, v_nm_3717_, v_args_3718_, v_a_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Nat_applySimprocConst___boxed(lean_object* v_expr_3728_, lean_object* v_nm_3729_, lean_object* v_args_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Nat_applySimprocConst(v_expr_3728_, v_nm_3729_, v_args_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_args_3730_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx(lean_object* v_x_3740_){
_start:
{
switch(lean_obj_tag(v_x_3740_))
{
case 0:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_unsigned_to_nat(0u);
return v___x_3741_;
}
case 1:
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_unsigned_to_nat(1u);
return v___x_3742_;
}
default: 
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_unsigned_to_nat(2u);
return v___x_3743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorIdx___boxed(lean_object* v_x_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Nat_EqResult_ctorIdx(v_x_3744_);
lean_dec_ref(v_x_3744_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___redArg(lean_object* v_t_3746_, lean_object* v_k_3747_){
_start:
{
switch(lean_obj_tag(v_t_3746_))
{
case 0:
{
uint8_t v_b_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_b_3748_ = lean_ctor_get_uint8(v_t_3746_, 0);
lean_dec_ref(v_t_3746_);
v___x_3749_ = lean_box(v_b_3748_);
v___x_3750_ = lean_apply_1(v_k_3747_, v___x_3749_);
return v___x_3750_;
}
case 1:
{
lean_object* v_p_3751_; lean_object* v___x_3752_; 
v_p_3751_ = lean_ctor_get(v_t_3746_, 0);
lean_inc_ref(v_p_3751_);
lean_dec_ref(v_t_3746_);
v___x_3752_ = lean_apply_1(v_k_3747_, v_p_3751_);
return v___x_3752_;
}
default: 
{
lean_object* v_x_3753_; lean_object* v_y_3754_; lean_object* v_p_3755_; lean_object* v___x_3756_; 
v_x_3753_ = lean_ctor_get(v_t_3746_, 0);
lean_inc_ref(v_x_3753_);
v_y_3754_ = lean_ctor_get(v_t_3746_, 1);
lean_inc_ref(v_y_3754_);
v_p_3755_ = lean_ctor_get(v_t_3746_, 2);
lean_inc_ref(v_p_3755_);
lean_dec_ref(v_t_3746_);
v___x_3756_ = lean_apply_3(v_k_3747_, v_x_3753_, v_y_3754_, v_p_3755_);
return v___x_3756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim(lean_object* v_motive_3757_, lean_object* v_ctorIdx_3758_, lean_object* v_t_3759_, lean_object* v_h_3760_, lean_object* v_k_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Nat_EqResult_ctorElim___redArg(v_t_3759_, v_k_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_ctorElim___boxed(lean_object* v_motive_3763_, lean_object* v_ctorIdx_3764_, lean_object* v_t_3765_, lean_object* v_h_3766_, lean_object* v_k_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Nat_EqResult_ctorElim(v_motive_3763_, v_ctorIdx_3764_, v_t_3765_, v_h_3766_, v_k_3767_);
lean_dec(v_ctorIdx_3764_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim___redArg(lean_object* v_t_3769_, lean_object* v_decide_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Nat_EqResult_ctorElim___redArg(v_t_3769_, v_decide_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_decide_elim(lean_object* v_motive_3772_, lean_object* v_t_3773_, lean_object* v_h_3774_, lean_object* v_decide_3775_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Nat_EqResult_ctorElim___redArg(v_t_3773_, v_decide_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim___redArg(lean_object* v_t_3777_, lean_object* v_false_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Nat_EqResult_ctorElim___redArg(v_t_3777_, v_false_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_false_elim(lean_object* v_motive_3780_, lean_object* v_t_3781_, lean_object* v_h_3782_, lean_object* v_false_3783_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Nat_EqResult_ctorElim___redArg(v_t_3781_, v_false_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim___redArg(lean_object* v_t_3785_, lean_object* v_eq_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Nat_EqResult_ctorElim___redArg(v_t_3785_, v_eq_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Nat_EqResult_eq_elim(lean_object* v_motive_3788_, lean_object* v_t_3789_, lean_object* v_h_3790_, lean_object* v_eq_3791_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Nat_EqResult_ctorElim___redArg(v_t_3789_, v_eq_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg(lean_object* v_e_3793_, lean_object* v_lemmaName_3794_, lean_object* v_args_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v___x_3798_; lean_object* v_env_3799_; uint8_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3798_ = lean_st_ref_get(v_a_3796_);
v_env_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc_ref(v_env_3799_);
lean_dec(v___x_3798_);
v___x_3800_ = 1;
lean_inc(v_lemmaName_3794_);
v___x_3801_ = l_Lean_Environment_contains(v_env_3799_, v_lemmaName_3794_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_dec(v_lemmaName_3794_);
lean_dec_ref(v_e_3793_);
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = l_Lean_mkConst(v_lemmaName_3794_, v___x_3804_);
v___x_3806_ = l_Lean_mkAppN(v___x_3805_, v_args_3795_);
v___x_3807_ = lean_apply_1(v_e_3793_, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___redArg___boxed(lean_object* v_e_3810_, lean_object* v_lemmaName_3811_, lean_object* v_args_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Nat_applyEqLemma___redArg(v_e_3810_, v_lemmaName_3811_, v_args_3812_, v_a_3813_);
lean_dec(v_a_3813_);
lean_dec_ref(v_args_3812_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma(lean_object* v_e_3816_, lean_object* v_lemmaName_3817_, lean_object* v_args_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Nat_applyEqLemma___redArg(v_e_3816_, v_lemmaName_3817_, v_args_3818_, v_a_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Nat_applyEqLemma___boxed(lean_object* v_e_3828_, lean_object* v_lemmaName_3829_, lean_object* v_args_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Nat_applyEqLemma(v_e_3828_, v_lemmaName_3829_, v_args_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_args_3830_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__0(lean_object* v_p_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_p_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1(lean_object* v_n_3842_, lean_object* v_n_3843_, lean_object* v_e_3844_, lean_object* v_p_3845_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_nat_sub(v_n_3842_, v_n_3843_);
v___x_3847_ = l_Lean_mkNatLit(v___x_3846_);
v___x_3848_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3848_, 0, v_e_3844_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
lean_ctor_set(v___x_3848_, 2, v_p_3845_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__1___boxed(lean_object* v_n_3849_, lean_object* v_n_3850_, lean_object* v_e_3851_, lean_object* v_p_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Nat_reduceNatEqExpr___redArg___lam__1(v_n_3849_, v_n_3850_, v_e_3851_, v_p_3852_);
lean_dec(v_n_3850_);
lean_dec(v_n_3849_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__4(lean_object* v___x_3854_, lean_object* v_e_3855_, lean_object* v_p_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3854_);
lean_ctor_set(v___x_3857_, 1, v_e_3855_);
lean_ctor_set(v___x_3857_, 2, v_p_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___lam__2(lean_object* v_e_3858_, lean_object* v___y_3859_, lean_object* v_p_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3861_, 0, v_e_3858_);
lean_ctor_set(v___x_3861_, 1, v___y_3859_);
lean_ctor_set(v___x_3861_, 2, v_p_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg(lean_object* v_x_3894_, lean_object* v_y_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_x_3894_);
v___x_3902_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_3894_, v___x_3901_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_4094_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_4094_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_4094_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3907_; lean_object* v___x_3908_; 
lean_del_object(v___x_3905_);
v_val_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3907_);
lean_dec_ref(v_a_3903_);
lean_inc_ref(v_y_3895_);
v___x_3908_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_3895_, v___x_3901_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_4081_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_4081_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_4081_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
if (lean_obj_tag(v_a_3909_) == 1)
{
if (lean_obj_tag(v_val_3907_) == 0)
{
lean_object* v_val_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v_y_3895_);
v_val_3913_ = lean_ctor_get(v_a_3909_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_a_3909_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3915_ = v_a_3909_;
v_isShared_3916_ = v_isSharedCheck_3972_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_val_3913_);
lean_dec(v_a_3909_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3972_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
if (lean_obj_tag(v_val_3913_) == 0)
{
lean_object* v_n_3917_; lean_object* v_n_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec_ref(v_x_3894_);
v_n_3917_ = lean_ctor_get(v_val_3907_, 0);
lean_inc(v_n_3917_);
lean_dec_ref(v_val_3907_);
v_n_3918_ = lean_ctor_get(v_val_3913_, 0);
lean_inc(v_n_3918_);
lean_dec_ref(v_val_3913_);
v___x_3919_ = lean_nat_dec_eq(v_n_3917_, v_n_3918_);
lean_dec(v_n_3918_);
lean_dec(v_n_3917_);
v___x_3920_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3920_, 0, v___x_3919_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3920_);
v___x_3922_ = v___x_3915_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3924_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3922_);
v___x_3924_ = v___x_3911_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
else
{
lean_object* v_n_3927_; lean_object* v_e_3928_; lean_object* v_o_3929_; lean_object* v_n_3930_; uint8_t v___x_3931_; 
lean_del_object(v___x_3915_);
lean_del_object(v___x_3911_);
v_n_3927_ = lean_ctor_get(v_val_3907_, 0);
lean_inc(v_n_3927_);
lean_dec_ref(v_val_3907_);
v_e_3928_ = lean_ctor_get(v_val_3913_, 0);
lean_inc_ref(v_e_3928_);
v_o_3929_ = lean_ctor_get(v_val_3913_, 1);
lean_inc_ref(v_o_3929_);
v_n_3930_ = lean_ctor_get(v_val_3913_, 2);
lean_inc(v_n_3930_);
lean_dec_ref(v_val_3913_);
v___x_3931_ = lean_nat_dec_le(v_n_3930_, v_n_3927_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v_n_3930_);
lean_dec(v_n_3927_);
lean_inc_ref(v_o_3929_);
lean_inc_ref(v_x_3894_);
v___x_3932_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_x_3894_, v_o_3929_);
v___x_3933_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3932_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___f_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___f_3935_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__0));
v___x_3936_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__3));
v___x_3937_ = lean_unsigned_to_nat(4u);
v___x_3938_ = lean_mk_empty_array_with_capacity(v___x_3937_);
v___x_3939_ = lean_array_push(v___x_3938_, v_x_3894_);
v___x_3940_ = lean_array_push(v___x_3939_, v_e_3928_);
v___x_3941_ = lean_array_push(v___x_3940_, v_o_3929_);
v___x_3942_ = lean_array_push(v___x_3941_, v_a_3934_);
v___x_3943_ = l_Nat_applyEqLemma___redArg(v___f_3935_, v___x_3936_, v___x_3942_, v_a_3899_);
lean_dec_ref(v___x_3942_);
return v___x_3943_;
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v_o_3929_);
lean_dec_ref(v_e_3928_);
lean_dec_ref(v_x_3894_);
v_a_3944_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3933_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3933_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
lean_inc_ref(v_x_3894_);
lean_inc_ref(v_o_3929_);
v___x_3952_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_3929_, v_x_3894_);
v___x_3953_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3952_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3953_);
lean_inc_ref(v_e_3928_);
v___f_3955_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3955_, 0, v_n_3927_);
lean_closure_set(v___f_3955_, 1, v_n_3930_);
lean_closure_set(v___f_3955_, 2, v_e_3928_);
v___x_3956_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__5));
v___x_3957_ = lean_unsigned_to_nat(4u);
v___x_3958_ = lean_mk_empty_array_with_capacity(v___x_3957_);
v___x_3959_ = lean_array_push(v___x_3958_, v_x_3894_);
v___x_3960_ = lean_array_push(v___x_3959_, v_e_3928_);
v___x_3961_ = lean_array_push(v___x_3960_, v_o_3929_);
v___x_3962_ = lean_array_push(v___x_3961_, v_a_3954_);
v___x_3963_ = l_Nat_applyEqLemma___redArg(v___f_3955_, v___x_3956_, v___x_3962_, v_a_3899_);
lean_dec_ref(v___x_3962_);
return v___x_3963_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_n_3930_);
lean_dec_ref(v_o_3929_);
lean_dec_ref(v_e_3928_);
lean_dec(v_n_3927_);
lean_dec_ref(v_x_3894_);
v_a_3964_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3953_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3953_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_3973_; 
lean_del_object(v___x_3911_);
lean_dec_ref(v_x_3894_);
v_val_3973_ = lean_ctor_get(v_a_3909_, 0);
lean_inc(v_val_3973_);
lean_dec_ref(v_a_3909_);
if (lean_obj_tag(v_val_3973_) == 0)
{
lean_object* v_e_3974_; lean_object* v_o_3975_; lean_object* v_n_3976_; lean_object* v_n_3977_; uint8_t v___x_3978_; 
v_e_3974_ = lean_ctor_get(v_val_3907_, 0);
lean_inc_ref(v_e_3974_);
v_o_3975_ = lean_ctor_get(v_val_3907_, 1);
lean_inc_ref(v_o_3975_);
v_n_3976_ = lean_ctor_get(v_val_3907_, 2);
lean_inc(v_n_3976_);
lean_dec_ref(v_val_3907_);
v_n_3977_ = lean_ctor_get(v_val_3973_, 0);
lean_inc(v_n_3977_);
lean_dec_ref(v_val_3973_);
v___x_3978_ = lean_nat_dec_le(v_n_3976_, v_n_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_n_3977_);
lean_dec(v_n_3976_);
lean_inc_ref(v_o_3975_);
lean_inc_ref(v_y_3895_);
v___x_3979_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_3895_, v_o_3975_);
v___x_3980_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3979_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___f_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
v___f_3982_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__0));
v___x_3983_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__7));
v___x_3984_ = lean_unsigned_to_nat(4u);
v___x_3985_ = lean_mk_empty_array_with_capacity(v___x_3984_);
v___x_3986_ = lean_array_push(v___x_3985_, v_e_3974_);
v___x_3987_ = lean_array_push(v___x_3986_, v_o_3975_);
v___x_3988_ = lean_array_push(v___x_3987_, v_y_3895_);
v___x_3989_ = lean_array_push(v___x_3988_, v_a_3981_);
v___x_3990_ = l_Nat_applyEqLemma___redArg(v___f_3982_, v___x_3983_, v___x_3989_, v_a_3899_);
lean_dec_ref(v___x_3989_);
return v___x_3990_;
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v_o_3975_);
lean_dec_ref(v_e_3974_);
lean_dec_ref(v_y_3895_);
v_a_3991_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3980_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3980_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_inc_ref(v_y_3895_);
lean_inc_ref(v_o_3975_);
v___x_3999_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_3975_, v_y_3895_);
v___x_4000_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_3999_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___f_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
lean_inc_ref(v_e_3974_);
v___f_4002_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_4002_, 0, v_n_3977_);
lean_closure_set(v___f_4002_, 1, v_n_3976_);
lean_closure_set(v___f_4002_, 2, v_e_3974_);
v___x_4003_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__9));
v___x_4004_ = lean_unsigned_to_nat(4u);
v___x_4005_ = lean_mk_empty_array_with_capacity(v___x_4004_);
v___x_4006_ = lean_array_push(v___x_4005_, v_e_3974_);
v___x_4007_ = lean_array_push(v___x_4006_, v_o_3975_);
v___x_4008_ = lean_array_push(v___x_4007_, v_y_3895_);
v___x_4009_ = lean_array_push(v___x_4008_, v_a_4001_);
v___x_4010_ = l_Nat_applyEqLemma___redArg(v___f_4002_, v___x_4003_, v___x_4009_, v_a_3899_);
lean_dec_ref(v___x_4009_);
return v___x_4010_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_n_3977_);
lean_dec(v_n_3976_);
lean_dec_ref(v_o_3975_);
lean_dec_ref(v_e_3974_);
lean_dec_ref(v_y_3895_);
v_a_4011_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4000_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4000_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
else
{
lean_object* v_e_4019_; lean_object* v_o_4020_; lean_object* v_n_4021_; lean_object* v_e_4022_; lean_object* v_o_4023_; lean_object* v_n_4024_; lean_object* v___y_4026_; uint8_t v___x_4048_; 
lean_dec_ref(v_y_3895_);
v_e_4019_ = lean_ctor_get(v_val_3907_, 0);
lean_inc_ref(v_e_4019_);
v_o_4020_ = lean_ctor_get(v_val_3907_, 1);
lean_inc_ref(v_o_4020_);
v_n_4021_ = lean_ctor_get(v_val_3907_, 2);
lean_inc(v_n_4021_);
lean_dec_ref(v_val_3907_);
v_e_4022_ = lean_ctor_get(v_val_3973_, 0);
lean_inc_ref(v_e_4022_);
v_o_4023_ = lean_ctor_get(v_val_3973_, 1);
lean_inc_ref(v_o_4023_);
v_n_4024_ = lean_ctor_get(v_val_3973_, 2);
lean_inc(v_n_4024_);
lean_dec_ref(v_val_3973_);
v___x_4048_ = lean_nat_dec_le(v_n_4021_, v_n_4024_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
lean_inc_ref(v_o_4020_);
lean_inc_ref(v_o_4023_);
v___x_4049_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4023_, v_o_4020_);
v___x_4050_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4049_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___f_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = lean_nat_sub(v_n_4021_, v_n_4024_);
lean_dec(v_n_4024_);
lean_dec(v_n_4021_);
v___x_4053_ = l_Lean_mkNatLit(v___x_4052_);
lean_inc_ref(v_e_4019_);
v___x_4054_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4019_, v___x_4053_);
lean_inc_ref(v_e_4022_);
v___f_4055_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__4), 3, 2);
lean_closure_set(v___f_4055_, 0, v___x_4054_);
lean_closure_set(v___f_4055_, 1, v_e_4022_);
v___x_4056_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__13));
v___x_4057_ = lean_unsigned_to_nat(5u);
v___x_4058_ = lean_mk_empty_array_with_capacity(v___x_4057_);
v___x_4059_ = lean_array_push(v___x_4058_, v_e_4019_);
v___x_4060_ = lean_array_push(v___x_4059_, v_e_4022_);
v___x_4061_ = lean_array_push(v___x_4060_, v_o_4020_);
v___x_4062_ = lean_array_push(v___x_4061_, v_o_4023_);
v___x_4063_ = lean_array_push(v___x_4062_, v_a_4051_);
v___x_4064_ = l_Nat_applyEqLemma___redArg(v___f_4055_, v___x_4056_, v___x_4063_, v_a_3899_);
lean_dec_ref(v___x_4063_);
return v___x_4064_;
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_n_4024_);
lean_dec_ref(v_o_4023_);
lean_dec_ref(v_e_4022_);
lean_dec(v_n_4021_);
lean_dec_ref(v_o_4020_);
lean_dec_ref(v_e_4019_);
v_a_4065_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4050_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4050_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
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
uint8_t v___x_4073_; 
v___x_4073_ = lean_nat_dec_eq(v_n_4021_, v_n_4024_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = lean_nat_sub(v_n_4024_, v_n_4021_);
lean_dec(v_n_4021_);
lean_dec(v_n_4024_);
v___x_4075_ = l_Lean_mkNatLit(v___x_4074_);
lean_inc_ref(v_e_4022_);
v___x_4076_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4022_, v___x_4075_);
v___y_4026_ = v___x_4076_;
goto v___jp_4025_;
}
else
{
lean_dec(v_n_4024_);
lean_dec(v_n_4021_);
lean_inc_ref(v_e_4022_);
v___y_4026_ = v_e_4022_;
goto v___jp_4025_;
}
}
v___jp_4025_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
lean_inc_ref(v_o_4023_);
lean_inc_ref(v_o_4020_);
v___x_4027_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4020_, v_o_4023_);
v___x_4028_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4027_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___f_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
lean_inc_ref(v_e_4019_);
v___f_4030_ = lean_alloc_closure((void*)(l_Nat_reduceNatEqExpr___redArg___lam__2), 3, 2);
lean_closure_set(v___f_4030_, 0, v_e_4019_);
lean_closure_set(v___f_4030_, 1, v___y_4026_);
v___x_4031_ = ((lean_object*)(l_Nat_reduceNatEqExpr___redArg___closed__11));
v___x_4032_ = lean_unsigned_to_nat(5u);
v___x_4033_ = lean_mk_empty_array_with_capacity(v___x_4032_);
v___x_4034_ = lean_array_push(v___x_4033_, v_e_4019_);
v___x_4035_ = lean_array_push(v___x_4034_, v_e_4022_);
v___x_4036_ = lean_array_push(v___x_4035_, v_o_4020_);
v___x_4037_ = lean_array_push(v___x_4036_, v_o_4023_);
v___x_4038_ = lean_array_push(v___x_4037_, v_a_4029_);
v___x_4039_ = l_Nat_applyEqLemma___redArg(v___f_4030_, v___x_4031_, v___x_4038_, v_a_3899_);
lean_dec_ref(v___x_4038_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec_ref(v___y_4026_);
lean_dec_ref(v_o_4023_);
lean_dec_ref(v_e_4022_);
lean_dec_ref(v_o_4020_);
lean_dec_ref(v_e_4019_);
v_a_4040_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4028_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4028_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
lean_dec(v_a_3909_);
lean_dec(v_val_3907_);
lean_dec_ref(v_y_3895_);
lean_dec_ref(v_x_3894_);
v___x_4077_ = lean_box(0);
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_4077_);
v___x_4079_ = v___x_3911_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_val_3907_);
lean_dec_ref(v_y_3895_);
lean_dec_ref(v_x_3894_);
v_a_4082_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_3908_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_3908_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4092_; 
lean_dec(v_a_3903_);
lean_dec_ref(v_y_3895_);
lean_dec_ref(v_x_3894_);
v___x_4090_ = lean_box(0);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_4090_);
v___x_4092_ = v___x_3905_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec_ref(v_y_3895_);
lean_dec_ref(v_x_3894_);
v_a_4095_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_3902_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_3902_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___redArg___boxed(lean_object* v_x_4103_, lean_object* v_y_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Nat_reduceNatEqExpr___redArg(v_x_4103_, v_y_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr(lean_object* v_x_4111_, lean_object* v_y_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Nat_reduceNatEqExpr___redArg(v_x_4111_, v_y_4112_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceNatEqExpr___boxed(lean_object* v_x_4122_, lean_object* v_y_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Nat_reduceNatEqExpr(v_x_4122_, v_y_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
return v_res_4132_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = lean_box(0);
v___x_4137_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__1));
v___x_4138_ = l_Lean_mkConst(v___x_4137_, v___x_4136_);
return v___x_4138_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = lean_box(0);
v___x_4143_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__4));
v___x_4144_ = l_Lean_mkConst(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__8(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = lean_box(0);
v___x_4149_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__7));
v___x_4150_ = l_Lean_mkConst(v___x_4149_, v___x_4148_);
return v___x_4150_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___redArg___closed__11(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4154_ = lean_box(0);
v___x_4155_ = ((lean_object*)(l_Nat_reduceEqDiff___redArg___closed__10));
v___x_4156_ = l_Lean_mkConst(v___x_4155_, v___x_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg(lean_object* v_e_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat___closed__1));
v___x_4164_ = lean_unsigned_to_nat(3u);
v___x_4165_ = l_Lean_Expr_isAppOfArity(v_e_4157_, v___x_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec_ref(v_e_4157_);
v___x_4166_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
else
{
lean_object* v___x_4168_; lean_object* v_x_4169_; lean_object* v_y_4170_; lean_object* v___x_4171_; 
v___x_4168_ = l_Lean_Expr_appFn_x21(v_e_4157_);
v_x_4169_ = l_Lean_Expr_appArg_x21(v___x_4168_);
lean_dec_ref(v___x_4168_);
v_y_4170_ = l_Lean_Expr_appArg_x21(v_e_4157_);
v___x_4171_ = l_Nat_reduceNatEqExpr___redArg(v_x_4169_, v_y_4170_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4296_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4174_ = v___x_4171_;
v_isShared_4175_ = v_isSharedCheck_4296_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4296_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
if (lean_obj_tag(v_a_4172_) == 0)
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
lean_dec_ref(v_e_4157_);
v___x_4176_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4176_);
v___x_4178_ = v___x_4174_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
else
{
lean_object* v_val_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4295_; 
v_val_4180_ = lean_ctor_get(v_a_4172_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_a_4172_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4182_ = v_a_4172_;
v_isShared_4183_ = v_isSharedCheck_4295_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_val_4180_);
lean_dec(v_a_4172_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4295_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
switch(lean_obj_tag(v_val_4180_))
{
case 0:
{
uint8_t v_b_4184_; 
lean_del_object(v___x_4174_);
v_b_4184_ = lean_ctor_get_uint8(v_val_4180_, 0);
lean_dec_ref(v_val_4180_);
if (v_b_4184_ == 0)
{
lean_object* v___x_4185_; 
lean_inc_ref(v_e_4157_);
v___x_4185_ = l_Lean_Meta_mkDecide(v_e_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref(v___x_4185_);
v___x_4187_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___x_4188_ = l_Lean_Meta_mkEqRefl(v___x_4187_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4209_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4191_ = v___x_4188_;
v_isShared_4192_ = v_isSharedCheck_4209_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4209_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4193_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__2, &l_Nat_reduceEqDiff___redArg___closed__2_once, _init_l_Nat_reduceEqDiff___redArg___closed__2);
v___x_4194_ = l_Lean_Expr_appArg_x21(v_a_4186_);
lean_dec(v_a_4186_);
v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___x_4196_ = lean_array_push(v___x_4195_, v_e_4157_);
v___x_4197_ = lean_array_push(v___x_4196_, v___x_4194_);
v___x_4198_ = lean_array_push(v___x_4197_, v_a_4189_);
v___x_4199_ = l_Lean_mkAppN(v___x_4193_, v___x_4198_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4199_);
v___x_4202_ = v___x_4182_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4199_);
v___x_4202_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4203_, 0, v___x_4200_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*2, v___x_4165_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 0, v___x_4204_);
v___x_4206_ = v___x_4191_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4204_);
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
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec(v_a_4186_);
lean_del_object(v___x_4182_);
lean_dec_ref(v_e_4157_);
v_a_4210_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4188_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4188_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_del_object(v___x_4182_);
lean_dec_ref(v_e_4157_);
v_a_4218_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4185_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4185_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
lean_object* v___x_4226_; 
lean_inc_ref(v_e_4157_);
v___x_4226_ = l_Lean_Meta_mkDecide(v_e_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___x_4229_ = l_Lean_Meta_mkEqRefl(v___x_4228_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4250_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4250_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4250_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4234_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__8, &l_Nat_reduceEqDiff___redArg___closed__8_once, _init_l_Nat_reduceEqDiff___redArg___closed__8);
v___x_4235_ = l_Lean_Expr_appArg_x21(v_a_4227_);
lean_dec(v_a_4227_);
v___x_4236_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___x_4237_ = lean_array_push(v___x_4236_, v_e_4157_);
v___x_4238_ = lean_array_push(v___x_4237_, v___x_4235_);
v___x_4239_ = lean_array_push(v___x_4238_, v_a_4230_);
v___x_4240_ = l_Lean_mkAppN(v___x_4234_, v___x_4239_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4240_);
v___x_4243_ = v___x_4182_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4240_);
v___x_4243_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4244_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4244_, 0, v___x_4241_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
lean_ctor_set_uint8(v___x_4244_, sizeof(void*)*2, v___x_4165_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4245_);
v___x_4247_ = v___x_4232_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
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
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_a_4227_);
lean_del_object(v___x_4182_);
lean_dec_ref(v_e_4157_);
v_a_4251_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4229_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4229_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_del_object(v___x_4182_);
lean_dec_ref(v_e_4157_);
v_a_4259_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4226_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4226_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
case 1:
{
lean_object* v_p_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4282_; 
lean_dec_ref(v_e_4157_);
v_p_4267_ = lean_ctor_get(v_val_4180_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_val_4180_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4269_ = v_val_4180_;
v_isShared_4270_ = v_isSharedCheck_4282_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_p_4267_);
lean_dec(v_val_4180_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4282_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4271_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_p_4267_);
v___x_4273_ = v___x_4182_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_p_4267_);
v___x_4273_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4274_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4274_, 0, v___x_4271_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2, v___x_4165_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set_tag(v___x_4269_, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4274_);
v___x_4276_ = v___x_4269_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4278_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4276_);
v___x_4278_ = v___x_4174_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
default: 
{
lean_object* v_x_4283_; lean_object* v_y_4284_; lean_object* v_p_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
lean_dec_ref(v_e_4157_);
v_x_4283_ = lean_ctor_get(v_val_4180_, 0);
lean_inc_ref(v_x_4283_);
v_y_4284_ = lean_ctor_get(v_val_4180_, 1);
lean_inc_ref(v_y_4284_);
v_p_4285_ = lean_ctor_get(v_val_4180_, 2);
lean_inc_ref(v_p_4285_);
lean_dec_ref(v_val_4180_);
v___x_4286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkEqNat(v_x_4283_, v_y_4284_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_p_4285_);
v___x_4288_ = v___x_4182_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_p_4285_);
v___x_4288_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4289_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4289_, 0, v___x_4286_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
lean_ctor_set_uint8(v___x_4289_, sizeof(void*)*2, v___x_4165_);
v___x_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4290_);
v___x_4292_ = v___x_4174_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
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
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec_ref(v_e_4157_);
v_a_4297_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4171_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4171_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___redArg___boxed(lean_object* v_e_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Nat_reduceEqDiff___redArg(v_e_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_);
lean_dec(v_a_4309_);
lean_dec_ref(v_a_4308_);
lean_dec(v_a_4307_);
lean_dec_ref(v_a_4306_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff(lean_object* v_e_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Nat_reduceEqDiff___redArg(v_e_4312_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___boxed(lean_object* v_e_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Nat_reduceEqDiff(v_e_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4351_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4352_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4349_, v___x_4350_, v___x_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20____boxed(lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_();
return v_res_4354_;
}
}
static lean_object* _init_l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_alloc_closure((void*)(l_Nat_reduceEqDiff___boxed), 9, 0);
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4359_ = 1;
v___x_4360_ = lean_obj_once(&l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_, &l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once, _init_l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_);
v___x_4361_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4358_, v___x_4359_, v___x_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22____boxed(lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_));
v___x_4366_ = 1;
v___x_4367_ = lean_obj_once(&l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_, &l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22__once, _init_l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_);
v___x_4368_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4365_, v___x_4366_, v___x_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24____boxed(lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
return v_res_4370_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = lean_box(0);
v___x_4377_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__1));
v___x_4378_ = l_Lean_mkConst(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4384_ = lean_box(0);
v___x_4385_ = ((lean_object*)(l_Nat_reduceBeqDiff___redArg___closed__4));
v___x_4386_ = l_Lean_mkConst(v___x_4385_, v___x_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg(lean_object* v_e_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4393_ = ((lean_object*)(l_Nat_reduceBEq___redArg___closed__2));
v___x_4394_ = lean_unsigned_to_nat(4u);
v___x_4395_ = l_Lean_Expr_isAppOfArity(v_e_4387_, v___x_4393_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
return v___x_4397_;
}
else
{
lean_object* v___x_4398_; lean_object* v_x_4399_; lean_object* v_y_4400_; lean_object* v___x_4401_; 
v___x_4398_ = l_Lean_Expr_appFn_x21(v_e_4387_);
v_x_4399_ = l_Lean_Expr_appArg_x21(v___x_4398_);
lean_dec_ref(v___x_4398_);
v_y_4400_ = l_Lean_Expr_appArg_x21(v_e_4387_);
lean_inc_ref(v_y_4400_);
lean_inc_ref(v_x_4399_);
v___x_4401_ = l_Nat_reduceNatEqExpr___redArg(v_x_4399_, v_y_4400_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4464_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4464_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4464_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___y_4407_; 
if (lean_obj_tag(v_a_4402_) == 0)
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
lean_del_object(v___x_4404_);
lean_dec_ref(v_y_4400_);
lean_dec_ref(v_x_4399_);
v___x_4414_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
return v___x_4415_;
}
else
{
lean_object* v_val_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4463_; 
v_val_4416_ = lean_ctor_get(v_a_4402_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_a_4402_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4418_ = v_a_4402_;
v_isShared_4419_ = v_isSharedCheck_4463_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_val_4416_);
lean_dec(v_a_4402_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4463_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
switch(lean_obj_tag(v_val_4416_))
{
case 0:
{
uint8_t v_b_4420_; 
lean_del_object(v___x_4418_);
lean_dec_ref(v_y_4400_);
lean_dec_ref(v_x_4399_);
v_b_4420_ = lean_ctor_get_uint8(v_val_4416_, 0);
lean_dec_ref(v_val_4416_);
if (v_b_4420_ == 0)
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_4407_ = v___x_4421_;
goto v___jp_4406_;
}
else
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_4407_ = v___x_4422_;
goto v___jp_4406_;
}
}
case 1:
{
lean_object* v_p_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4443_; 
lean_del_object(v___x_4404_);
v_p_4423_ = lean_ctor_get(v_val_4416_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_val_4416_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4425_ = v_val_4416_;
v_isShared_4426_ = v_isSharedCheck_4443_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_p_4423_);
lean_dec(v_val_4416_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4443_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4427_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__2, &l_Nat_reduceBeqDiff___redArg___closed__2_once, _init_l_Nat_reduceBeqDiff___redArg___closed__2);
v___x_4428_ = lean_unsigned_to_nat(3u);
v___x_4429_ = lean_mk_empty_array_with_capacity(v___x_4428_);
v___x_4430_ = lean_array_push(v___x_4429_, v_x_4399_);
v___x_4431_ = lean_array_push(v___x_4430_, v_y_4400_);
v___x_4432_ = lean_array_push(v___x_4431_, v_p_4423_);
v___x_4433_ = l_Lean_mkAppN(v___x_4427_, v___x_4432_);
lean_dec_ref(v___x_4432_);
v___x_4434_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4433_);
v___x_4436_ = v___x_4418_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4433_);
v___x_4436_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4437_, 0, v___x_4434_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2, v___x_4395_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set_tag(v___x_4425_, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4437_);
v___x_4439_ = v___x_4425_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
}
}
}
default: 
{
lean_object* v_x_4444_; lean_object* v_y_4445_; lean_object* v_p_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_del_object(v___x_4404_);
v_x_4444_ = lean_ctor_get(v_val_4416_, 0);
lean_inc_ref(v_x_4444_);
v_y_4445_ = lean_ctor_get(v_val_4416_, 1);
lean_inc_ref(v_y_4445_);
v_p_4446_ = lean_ctor_get(v_val_4416_, 2);
lean_inc_ref(v_p_4446_);
lean_dec_ref(v_val_4416_);
v___x_4447_ = lean_obj_once(&l_Nat_reduceBeqDiff___redArg___closed__5, &l_Nat_reduceBeqDiff___redArg___closed__5_once, _init_l_Nat_reduceBeqDiff___redArg___closed__5);
v___x_4448_ = lean_unsigned_to_nat(5u);
v___x_4449_ = lean_mk_empty_array_with_capacity(v___x_4448_);
v___x_4450_ = lean_array_push(v___x_4449_, v_x_4399_);
v___x_4451_ = lean_array_push(v___x_4450_, v_y_4400_);
lean_inc_ref(v_x_4444_);
v___x_4452_ = lean_array_push(v___x_4451_, v_x_4444_);
lean_inc_ref(v_y_4445_);
v___x_4453_ = lean_array_push(v___x_4452_, v_y_4445_);
v___x_4454_ = lean_array_push(v___x_4453_, v_p_4446_);
v___x_4455_ = l_Lean_mkAppN(v___x_4447_, v___x_4454_);
lean_dec_ref(v___x_4454_);
v___x_4456_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNat(v_x_4444_, v_y_4445_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4455_);
v___x_4458_ = v___x_4418_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4455_);
v___x_4458_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4459_, 0, v___x_4456_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
lean_ctor_set_uint8(v___x_4459_, sizeof(void*)*2, v___x_4395_);
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
}
}
v___jp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4412_; 
v___x_4408_ = lean_box(0);
v___x_4409_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4409_, 0, v___y_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*2, v___x_4395_);
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 0, v___x_4410_);
v___x_4412_ = v___x_4404_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec_ref(v_y_4400_);
lean_dec_ref(v_x_4399_);
v_a_4465_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4401_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4401_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___redArg___boxed(lean_object* v_e_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Nat_reduceBeqDiff___redArg(v_e_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec_ref(v_e_4473_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff(lean_object* v_e_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Nat_reduceBeqDiff___redArg(v_e_4480_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___boxed(lean_object* v_e_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Nat_reduceBeqDiff(v_e_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
lean_dec(v_a_4491_);
lean_dec_ref(v_e_4490_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_));
v___x_4507_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4508_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4505_, v___x_4506_, v___x_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20____boxed(lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_();
return v_res_4510_;
}
}
static lean_object* _init_l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = lean_alloc_closure((void*)(l_Nat_reduceBeqDiff___boxed), 9, 0);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4515_ = 1;
v___x_4516_ = lean_obj_once(&l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_, &l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once, _init_l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_);
v___x_4517_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4514_, v___x_4515_, v___x_4516_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22____boxed(lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_));
v___x_4522_ = 1;
v___x_4523_ = lean_obj_once(&l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_, &l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22__once, _init_l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_);
v___x_4524_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4521_, v___x_4522_, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24____boxed(lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
return v_res_4526_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__2(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_box(0);
v___x_4533_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__1));
v___x_4534_ = l_Lean_mkConst(v___x_4533_, v___x_4532_);
return v___x_4534_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___redArg___closed__5(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_box(0);
v___x_4541_ = ((lean_object*)(l_Nat_reduceBneDiff___redArg___closed__4));
v___x_4542_ = l_Lean_mkConst(v___x_4541_, v___x_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg(lean_object* v_e_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4549_ = ((lean_object*)(l_Nat_reduceBNe___redArg___closed__1));
v___x_4550_ = lean_unsigned_to_nat(4u);
v___x_4551_ = l_Lean_Expr_isAppOfArity(v_e_4543_, v___x_4549_, v___x_4550_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; lean_object* v_x_4555_; lean_object* v_y_4556_; lean_object* v___x_4557_; 
v___x_4554_ = l_Lean_Expr_appFn_x21(v_e_4543_);
v_x_4555_ = l_Lean_Expr_appArg_x21(v___x_4554_);
lean_dec_ref(v___x_4554_);
v_y_4556_ = l_Lean_Expr_appArg_x21(v_e_4543_);
lean_inc_ref(v_y_4556_);
lean_inc_ref(v_x_4555_);
v___x_4557_ = l_Nat_reduceNatEqExpr___redArg(v_x_4555_, v_y_4556_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4621_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4560_ = v___x_4557_;
v_isShared_4561_ = v_isSharedCheck_4621_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4621_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___y_4563_; 
if (lean_obj_tag(v_a_4558_) == 0)
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_del_object(v___x_4560_);
lean_dec_ref(v_y_4556_);
lean_dec_ref(v_x_4555_);
v___x_4572_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
else
{
lean_object* v_val_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4620_; 
v_val_4574_ = lean_ctor_get(v_a_4558_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_a_4558_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4576_ = v_a_4558_;
v_isShared_4577_ = v_isSharedCheck_4620_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_val_4574_);
lean_dec(v_a_4558_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4620_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
switch(lean_obj_tag(v_val_4574_))
{
case 0:
{
uint8_t v_b_4578_; 
lean_del_object(v___x_4576_);
lean_dec_ref(v_y_4556_);
lean_dec_ref(v_x_4555_);
v_b_4578_ = lean_ctor_get_uint8(v_val_4574_, 0);
lean_dec_ref(v_val_4574_);
if (v_b_4578_ == 0)
{
if (v___x_4551_ == 0)
{
goto v___jp_4570_;
}
else
{
lean_object* v___x_4579_; 
v___x_4579_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
v___y_4563_ = v___x_4579_;
goto v___jp_4562_;
}
}
else
{
goto v___jp_4570_;
}
}
case 1:
{
lean_object* v_p_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4600_; 
lean_del_object(v___x_4560_);
v_p_4580_ = lean_ctor_get(v_val_4574_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_val_4574_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4582_ = v_val_4574_;
v_isShared_4583_ = v_isSharedCheck_4600_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_p_4580_);
lean_dec(v_val_4574_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4600_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4593_; 
v___x_4584_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__2, &l_Nat_reduceBneDiff___redArg___closed__2_once, _init_l_Nat_reduceBneDiff___redArg___closed__2);
v___x_4585_ = lean_unsigned_to_nat(3u);
v___x_4586_ = lean_mk_empty_array_with_capacity(v___x_4585_);
v___x_4587_ = lean_array_push(v___x_4586_, v_x_4555_);
v___x_4588_ = lean_array_push(v___x_4587_, v_y_4556_);
v___x_4589_ = lean_array_push(v___x_4588_, v_p_4580_);
v___x_4590_ = l_Lean_mkAppN(v___x_4584_, v___x_4589_);
lean_dec_ref(v___x_4589_);
v___x_4591_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__6, &l_Nat_reduceBoolPred___redArg___closed__6_once, _init_l_Nat_reduceBoolPred___redArg___closed__6);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4590_);
v___x_4593_ = v___x_4576_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4590_);
v___x_4593_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4594_, 0, v___x_4591_);
lean_ctor_set(v___x_4594_, 1, v___x_4593_);
lean_ctor_set_uint8(v___x_4594_, sizeof(void*)*2, v___x_4551_);
if (v_isShared_4583_ == 0)
{
lean_ctor_set_tag(v___x_4582_, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4594_);
v___x_4596_ = v___x_4582_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
}
}
default: 
{
lean_object* v_x_4601_; lean_object* v_y_4602_; lean_object* v_p_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
lean_del_object(v___x_4560_);
v_x_4601_ = lean_ctor_get(v_val_4574_, 0);
lean_inc_ref(v_x_4601_);
v_y_4602_ = lean_ctor_get(v_val_4574_, 1);
lean_inc_ref(v_y_4602_);
v_p_4603_ = lean_ctor_get(v_val_4574_, 2);
lean_inc_ref(v_p_4603_);
lean_dec_ref(v_val_4574_);
v___x_4604_ = lean_obj_once(&l_Nat_reduceBneDiff___redArg___closed__5, &l_Nat_reduceBneDiff___redArg___closed__5_once, _init_l_Nat_reduceBneDiff___redArg___closed__5);
v___x_4605_ = lean_unsigned_to_nat(5u);
v___x_4606_ = lean_mk_empty_array_with_capacity(v___x_4605_);
v___x_4607_ = lean_array_push(v___x_4606_, v_x_4555_);
v___x_4608_ = lean_array_push(v___x_4607_, v_y_4556_);
lean_inc_ref(v_x_4601_);
v___x_4609_ = lean_array_push(v___x_4608_, v_x_4601_);
lean_inc_ref(v_y_4602_);
v___x_4610_ = lean_array_push(v___x_4609_, v_y_4602_);
v___x_4611_ = lean_array_push(v___x_4610_, v_p_4603_);
v___x_4612_ = l_Lean_mkAppN(v___x_4604_, v___x_4611_);
lean_dec_ref(v___x_4611_);
v___x_4613_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBneNat(v_x_4601_, v_y_4602_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4612_);
v___x_4615_ = v___x_4576_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4612_);
v___x_4615_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4616_, 0, v___x_4613_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
lean_ctor_set_uint8(v___x_4616_, sizeof(void*)*2, v___x_4551_);
v___x_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
}
}
}
v___jp_4562_:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4564_ = lean_box(0);
v___x_4565_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4565_, 0, v___y_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*2, v___x_4551_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4566_);
v___x_4568_ = v___x_4560_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
v___jp_4570_:
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_obj_once(&l_Nat_reduceBoolPred___redArg___closed__3, &l_Nat_reduceBoolPred___redArg___closed__3_once, _init_l_Nat_reduceBoolPred___redArg___closed__3);
v___y_4563_ = v___x_4571_;
goto v___jp_4562_;
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec_ref(v_y_4556_);
lean_dec_ref(v_x_4555_);
v_a_4622_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4557_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4557_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___redArg___boxed(lean_object* v_e_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Nat_reduceBneDiff___redArg(v_e_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec_ref(v_e_4630_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff(lean_object* v_e_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Nat_reduceBneDiff___redArg(v_e_4637_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___boxed(lean_object* v_e_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Nat_reduceBneDiff(v_e_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_e_4647_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_));
v___x_4664_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4665_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4662_, v___x_4663_, v___x_4664_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20____boxed(lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_();
return v_res_4667_;
}
}
static lean_object* _init_l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = lean_alloc_closure((void*)(l_Nat_reduceBneDiff___boxed), 9, 0);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4672_ = 1;
v___x_4673_ = lean_obj_once(&l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_, &l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once, _init_l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_);
v___x_4674_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4671_, v___x_4672_, v___x_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22____boxed(lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_4678_; uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_));
v___x_4679_ = 1;
v___x_4680_ = lean_obj_once(&l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_, &l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22__once, _init_l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_);
v___x_4681_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4678_, v___x_4679_, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24____boxed(lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg(lean_object* v_nm_4714_, lean_object* v_arity_4715_, uint8_t v_isLT_4716_, lean_object* v_e_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; uint8_t v___x_4750_; 
v___x_4750_ = l_Lean_Expr_isAppOfArity(v_e_4717_, v_nm_4714_, v_arity_4715_);
if (v___x_4750_ == 0)
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_dec_ref(v_e_4717_);
v___x_4751_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
else
{
lean_object* v___x_4753_; lean_object* v_x_4754_; lean_object* v_y_4755_; lean_object* v___y_4757_; 
v___x_4753_ = l_Lean_Expr_appFn_x21(v_e_4717_);
v_x_4754_ = l_Lean_Expr_appArg_x21(v___x_4753_);
lean_dec_ref(v___x_4753_);
v_y_4755_ = l_Lean_Expr_appArg_x21(v_e_4717_);
if (v_isLT_4716_ == 0)
{
lean_object* v___x_4931_; 
v___x_4931_ = lean_unsigned_to_nat(0u);
v___y_4757_ = v___x_4931_;
goto v___jp_4756_;
}
else
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_unsigned_to_nat(1u);
v___y_4757_ = v___x_4932_;
goto v___jp_4756_;
}
v___jp_4756_:
{
lean_object* v___x_4758_; 
lean_inc_ref(v_x_4754_);
v___x_4758_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_x_4754_, v___y_4757_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4922_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4761_ = v___x_4758_;
v_isShared_4762_ = v_isSharedCheck_4922_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4922_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
if (lean_obj_tag(v_a_4759_) == 1)
{
lean_object* v_val_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
lean_del_object(v___x_4761_);
v_val_4763_ = lean_ctor_get(v_a_4759_, 0);
lean_inc(v_val_4763_);
lean_dec_ref(v_a_4759_);
v___x_4764_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_y_4755_);
v___x_4765_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_y_4755_, v___x_4764_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4909_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4768_ = v___x_4765_;
v_isShared_4769_ = v_isSharedCheck_4909_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4765_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4909_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
if (lean_obj_tag(v_a_4766_) == 1)
{
lean_del_object(v___x_4768_);
if (lean_obj_tag(v_val_4763_) == 0)
{
lean_object* v_val_4770_; 
lean_dec_ref(v_y_4755_);
v_val_4770_ = lean_ctor_get(v_a_4766_, 0);
lean_inc(v_val_4770_);
lean_dec_ref(v_a_4766_);
if (lean_obj_tag(v_val_4770_) == 0)
{
lean_object* v_n_4771_; lean_object* v_n_4772_; uint8_t v___x_4773_; lean_object* v___x_4774_; 
lean_dec_ref(v_x_4754_);
v_n_4771_ = lean_ctor_get(v_val_4763_, 0);
lean_inc(v_n_4771_);
lean_dec_ref(v_val_4763_);
v_n_4772_ = lean_ctor_get(v_val_4770_, 0);
lean_inc(v_n_4772_);
lean_dec_ref(v_val_4770_);
v___x_4773_ = lean_nat_dec_le(v_n_4771_, v_n_4772_);
lean_dec(v_n_4772_);
lean_dec(v_n_4771_);
v___x_4774_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_e_4717_, v___x_4773_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
return v___x_4774_;
}
else
{
lean_object* v_n_4775_; lean_object* v_e_4776_; lean_object* v_o_4777_; lean_object* v_n_4778_; uint8_t v___x_4779_; 
lean_dec_ref(v_e_4717_);
v_n_4775_ = lean_ctor_get(v_val_4763_, 0);
lean_inc(v_n_4775_);
lean_dec_ref(v_val_4763_);
v_e_4776_ = lean_ctor_get(v_val_4770_, 0);
lean_inc_ref(v_e_4776_);
v_o_4777_ = lean_ctor_get(v_val_4770_, 1);
lean_inc_ref(v_o_4777_);
v_n_4778_ = lean_ctor_get(v_val_4770_, 2);
lean_inc(v_n_4778_);
lean_dec_ref(v_val_4770_);
v___x_4779_ = lean_nat_dec_le(v_n_4775_, v_n_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
lean_inc_ref(v_x_4754_);
lean_inc_ref(v_o_4777_);
v___x_4780_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4777_, v_x_4754_);
v___x_4781_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4780_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref(v___x_4781_);
v___x_4783_ = lean_nat_sub(v_n_4775_, v_n_4778_);
lean_dec(v_n_4778_);
lean_dec(v_n_4775_);
v___x_4784_ = l_Lean_mkNatLit(v___x_4783_);
lean_inc_ref(v_e_4776_);
v___x_4785_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_4784_, v_e_4776_);
v___x_4786_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__3));
v___x_4787_ = lean_unsigned_to_nat(4u);
v___x_4788_ = lean_mk_empty_array_with_capacity(v___x_4787_);
v___x_4789_ = lean_array_push(v___x_4788_, v_x_4754_);
v___x_4790_ = lean_array_push(v___x_4789_, v_e_4776_);
v___x_4791_ = lean_array_push(v___x_4790_, v_o_4777_);
v___x_4792_ = lean_array_push(v___x_4791_, v_a_4782_);
v___x_4793_ = l_Nat_applySimprocConst___redArg(v___x_4785_, v___x_4786_, v___x_4792_, v_a_4721_);
lean_dec_ref(v___x_4792_);
return v___x_4793_;
}
else
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec(v_n_4778_);
lean_dec_ref(v_o_4777_);
lean_dec_ref(v_e_4776_);
lean_dec(v_n_4775_);
lean_dec_ref(v_x_4754_);
v_a_4794_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4781_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4781_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
lean_dec(v_n_4778_);
lean_dec(v_n_4775_);
lean_inc_ref(v_o_4777_);
lean_inc_ref(v_x_4754_);
v___x_4802_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_x_4754_, v_o_4777_);
v___x_4803_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4802_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v___x_4803_);
v___x_4805_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_4806_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__5));
v___x_4807_ = lean_unsigned_to_nat(4u);
v___x_4808_ = lean_mk_empty_array_with_capacity(v___x_4807_);
v___x_4809_ = lean_array_push(v___x_4808_, v_x_4754_);
v___x_4810_ = lean_array_push(v___x_4809_, v_e_4776_);
v___x_4811_ = lean_array_push(v___x_4810_, v_o_4777_);
v___x_4812_ = lean_array_push(v___x_4811_, v_a_4804_);
v___x_4813_ = l_Nat_applySimprocConst___redArg(v___x_4805_, v___x_4806_, v___x_4812_, v_a_4721_);
lean_dec_ref(v___x_4812_);
return v___x_4813_;
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec_ref(v_o_4777_);
lean_dec_ref(v_e_4776_);
lean_dec_ref(v_x_4754_);
v_a_4814_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4803_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4803_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
}
}
else
{
lean_object* v_val_4822_; 
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_e_4717_);
v_val_4822_ = lean_ctor_get(v_a_4766_, 0);
lean_inc(v_val_4822_);
lean_dec_ref(v_a_4766_);
if (lean_obj_tag(v_val_4822_) == 0)
{
lean_object* v_e_4823_; lean_object* v_o_4824_; lean_object* v_n_4825_; lean_object* v_n_4826_; uint8_t v___x_4827_; 
v_e_4823_ = lean_ctor_get(v_val_4763_, 0);
lean_inc_ref(v_e_4823_);
v_o_4824_ = lean_ctor_get(v_val_4763_, 1);
lean_inc_ref(v_o_4824_);
v_n_4825_ = lean_ctor_get(v_val_4763_, 2);
lean_inc(v_n_4825_);
lean_dec_ref(v_val_4763_);
v_n_4826_ = lean_ctor_get(v_val_4822_, 0);
lean_inc(v_n_4826_);
lean_dec_ref(v_val_4822_);
v___x_4827_ = lean_nat_dec_le(v_n_4825_, v_n_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_dec(v_n_4826_);
lean_dec(v_n_4825_);
lean_inc_ref(v_o_4824_);
lean_inc_ref(v_y_4755_);
v___x_4828_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLTNat(v_y_4755_, v_o_4824_);
v___x_4829_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4828_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref(v___x_4829_);
v___x_4831_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_4832_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__7));
v___x_4833_ = lean_unsigned_to_nat(4u);
v___x_4834_ = lean_mk_empty_array_with_capacity(v___x_4833_);
v___x_4835_ = lean_array_push(v___x_4834_, v_e_4823_);
v___x_4836_ = lean_array_push(v___x_4835_, v_o_4824_);
v___x_4837_ = lean_array_push(v___x_4836_, v_y_4755_);
v___x_4838_ = lean_array_push(v___x_4837_, v_a_4830_);
v___x_4839_ = l_Nat_applySimprocConst___redArg(v___x_4831_, v___x_4832_, v___x_4838_, v_a_4721_);
lean_dec_ref(v___x_4838_);
return v___x_4839_;
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec_ref(v_o_4824_);
lean_dec_ref(v_e_4823_);
lean_dec_ref(v_y_4755_);
v_a_4840_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4829_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4829_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_inc_ref(v_y_4755_);
lean_inc_ref(v_o_4824_);
v___x_4848_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4824_, v_y_4755_);
v___x_4849_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4848_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref(v___x_4849_);
v___x_4851_ = lean_nat_sub(v_n_4826_, v_n_4825_);
lean_dec(v_n_4825_);
lean_dec(v_n_4826_);
v___x_4852_ = l_Lean_mkNatLit(v___x_4851_);
lean_inc_ref(v_e_4823_);
v___x_4853_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_e_4823_, v___x_4852_);
v___x_4854_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__9));
v___x_4855_ = lean_unsigned_to_nat(4u);
v___x_4856_ = lean_mk_empty_array_with_capacity(v___x_4855_);
v___x_4857_ = lean_array_push(v___x_4856_, v_e_4823_);
v___x_4858_ = lean_array_push(v___x_4857_, v_o_4824_);
v___x_4859_ = lean_array_push(v___x_4858_, v_y_4755_);
v___x_4860_ = lean_array_push(v___x_4859_, v_a_4850_);
v___x_4861_ = l_Nat_applySimprocConst___redArg(v___x_4853_, v___x_4854_, v___x_4860_, v_a_4721_);
lean_dec_ref(v___x_4860_);
return v___x_4861_;
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_dec(v_n_4826_);
lean_dec(v_n_4825_);
lean_dec_ref(v_o_4824_);
lean_dec_ref(v_e_4823_);
lean_dec_ref(v_y_4755_);
v_a_4862_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4849_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4849_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
else
{
lean_object* v_e_4870_; lean_object* v_o_4871_; lean_object* v_n_4872_; lean_object* v_e_4873_; lean_object* v_o_4874_; lean_object* v_n_4875_; uint8_t v___x_4876_; 
lean_dec_ref(v_y_4755_);
v_e_4870_ = lean_ctor_get(v_val_4763_, 0);
lean_inc_ref(v_e_4870_);
v_o_4871_ = lean_ctor_get(v_val_4763_, 1);
lean_inc_ref(v_o_4871_);
v_n_4872_ = lean_ctor_get(v_val_4763_, 2);
lean_inc(v_n_4872_);
lean_dec_ref(v_val_4763_);
v_e_4873_ = lean_ctor_get(v_val_4822_, 0);
lean_inc_ref(v_e_4873_);
v_o_4874_ = lean_ctor_get(v_val_4822_, 1);
lean_inc_ref(v_o_4874_);
v_n_4875_ = lean_ctor_get(v_val_4822_, 2);
lean_inc(v_n_4875_);
lean_dec_ref(v_val_4822_);
v___x_4876_ = lean_nat_dec_le(v_n_4872_, v_n_4875_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_inc_ref(v_o_4871_);
lean_inc_ref(v_o_4874_);
v___x_4877_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_4874_, v_o_4871_);
v___x_4878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4877_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref(v___x_4878_);
v___x_4880_ = lean_nat_sub(v_n_4872_, v_n_4875_);
lean_dec(v_n_4875_);
lean_dec(v_n_4872_);
v___x_4881_ = l_Lean_mkNatLit(v___x_4880_);
lean_inc_ref(v_e_4870_);
v___x_4882_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4870_, v___x_4881_);
lean_inc_ref(v_e_4873_);
v___x_4883_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_4882_, v_e_4873_);
v___x_4884_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__11));
v___x_4885_ = lean_unsigned_to_nat(5u);
v___x_4886_ = lean_mk_empty_array_with_capacity(v___x_4885_);
v___x_4887_ = lean_array_push(v___x_4886_, v_e_4870_);
v___x_4888_ = lean_array_push(v___x_4887_, v_e_4873_);
v___x_4889_ = lean_array_push(v___x_4888_, v_o_4871_);
v___x_4890_ = lean_array_push(v___x_4889_, v_o_4874_);
v___x_4891_ = lean_array_push(v___x_4890_, v_a_4879_);
v___x_4892_ = l_Nat_applySimprocConst___redArg(v___x_4883_, v___x_4884_, v___x_4891_, v_a_4721_);
lean_dec_ref(v___x_4891_);
return v___x_4892_;
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec(v_n_4875_);
lean_dec_ref(v_o_4874_);
lean_dec_ref(v_e_4873_);
lean_dec(v_n_4872_);
lean_dec_ref(v_o_4871_);
lean_dec_ref(v_e_4870_);
v_a_4893_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4878_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4878_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
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
uint8_t v___x_4901_; 
v___x_4901_ = lean_nat_dec_eq(v_n_4872_, v_n_4875_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4902_ = lean_nat_sub(v_n_4875_, v_n_4872_);
lean_dec(v_n_4872_);
lean_dec(v_n_4875_);
v___x_4903_ = l_Lean_mkNatLit(v___x_4902_);
lean_inc_ref(v_e_4873_);
v___x_4904_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_4873_, v___x_4903_);
v___y_4724_ = v_e_4870_;
v___y_4725_ = v_o_4871_;
v___y_4726_ = v_o_4874_;
v___y_4727_ = v_e_4873_;
v___y_4728_ = v___x_4904_;
goto v___jp_4723_;
}
else
{
lean_dec(v_n_4875_);
lean_dec(v_n_4872_);
lean_inc_ref(v_e_4873_);
v___y_4724_ = v_e_4870_;
v___y_4725_ = v_o_4871_;
v___y_4726_ = v_o_4874_;
v___y_4727_ = v_e_4873_;
v___y_4728_ = v_e_4873_;
goto v___jp_4723_;
}
}
}
}
}
else
{
lean_object* v___x_4905_; lean_object* v___x_4907_; 
lean_dec(v_a_4766_);
lean_dec(v_val_4763_);
lean_dec_ref(v_y_4755_);
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_e_4717_);
v___x_4905_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 0, v___x_4905_);
v___x_4907_ = v___x_4768_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec(v_val_4763_);
lean_dec_ref(v_y_4755_);
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_e_4717_);
v_a_4910_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4765_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4765_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
lean_dec(v_a_4759_);
lean_dec_ref(v_y_4755_);
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_e_4717_);
v___x_4918_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 0, v___x_4918_);
v___x_4920_ = v___x_4761_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v_y_4755_);
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_e_4717_);
v_a_4923_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4758_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4758_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
}
v___jp_4723_:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
lean_inc_ref(v___y_4726_);
lean_inc_ref(v___y_4725_);
v___x_4729_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4725_, v___y_4726_);
v___x_4730_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_4729_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref(v___x_4730_);
lean_inc_ref(v___y_4724_);
v___x_4732_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___y_4724_, v___y_4728_);
v___x_4733_ = ((lean_object*)(l_Nat_reduceLTLE___redArg___closed__1));
v___x_4734_ = lean_unsigned_to_nat(5u);
v___x_4735_ = lean_mk_empty_array_with_capacity(v___x_4734_);
v___x_4736_ = lean_array_push(v___x_4735_, v___y_4724_);
v___x_4737_ = lean_array_push(v___x_4736_, v___y_4727_);
v___x_4738_ = lean_array_push(v___x_4737_, v___y_4725_);
v___x_4739_ = lean_array_push(v___x_4738_, v___y_4726_);
v___x_4740_ = lean_array_push(v___x_4739_, v_a_4731_);
v___x_4741_ = l_Nat_applySimprocConst___redArg(v___x_4732_, v___x_4733_, v___x_4740_, v_a_4721_);
lean_dec_ref(v___x_4740_);
return v___x_4741_;
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec_ref(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec_ref(v___y_4724_);
v_a_4742_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4730_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4730_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___redArg___boxed(lean_object* v_nm_4933_, lean_object* v_arity_4934_, lean_object* v_isLT_4935_, lean_object* v_e_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_){
_start:
{
uint8_t v_isLT_boxed_4942_; lean_object* v_res_4943_; 
v_isLT_boxed_4942_ = lean_unbox(v_isLT_4935_);
v_res_4943_ = l_Nat_reduceLTLE___redArg(v_nm_4933_, v_arity_4934_, v_isLT_boxed_4942_, v_e_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_nm_4933_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE(lean_object* v_nm_4944_, lean_object* v_arity_4945_, uint8_t v_isLT_4946_, lean_object* v_e_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Nat_reduceLTLE___redArg(v_nm_4944_, v_arity_4945_, v_isLT_4946_, v_e_4947_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLTLE___boxed(lean_object* v_nm_4957_, lean_object* v_arity_4958_, lean_object* v_isLT_4959_, lean_object* v_e_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
uint8_t v_isLT_boxed_4969_; lean_object* v_res_4970_; 
v_isLT_boxed_4969_ = lean_unbox(v_isLT_4959_);
v_res_4970_ = l_Nat_reduceLTLE(v_nm_4957_, v_arity_4958_, v_isLT_boxed_4969_, v_e_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec(v_nm_4957_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg(lean_object* v_e_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; lean_object* v___x_4980_; 
v___x_4977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat___closed__2));
v___x_4978_ = lean_unsigned_to_nat(4u);
v___x_4979_ = 0;
v___x_4980_ = l_Nat_reduceLTLE___redArg(v___x_4977_, v___x_4978_, v___x_4979_, v_e_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___redArg___boxed(lean_object* v_e_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Nat_reduceLeDiff___redArg(v_e_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
lean_dec(v_a_4985_);
lean_dec_ref(v_a_4984_);
lean_dec(v_a_4983_);
lean_dec_ref(v_a_4982_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff(lean_object* v_e_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Nat_reduceLeDiff___redArg(v_e_4988_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___boxed(lean_object* v_e_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Nat_reduceLeDiff(v_e_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5028_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5029_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5026_, v___x_5027_, v___x_5028_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20____boxed(lean_object* v_a_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_();
return v_res_5031_;
}
}
static lean_object* _init_l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = lean_alloc_closure((void*)(l_Nat_reduceLeDiff___boxed), 9, 0);
v___x_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_(){
_start:
{
lean_object* v___x_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5036_ = 1;
v___x_5037_ = lean_obj_once(&l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_, &l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once, _init_l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_);
v___x_5038_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5035_, v___x_5036_, v___x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22____boxed(lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_(){
_start:
{
lean_object* v___x_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_));
v___x_5043_ = 1;
v___x_5044_ = lean_obj_once(&l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_, &l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22__once, _init_l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_);
v___x_5045_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5042_, v___x_5043_, v___x_5044_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24____boxed(lean_object* v_a_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg(lean_object* v_e_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; 
v___x_5078_ = ((lean_object*)(l_Nat_reduceSub___redArg___closed__2));
v___x_5079_ = lean_unsigned_to_nat(6u);
v___x_5080_ = l_Lean_Expr_isAppOfArity(v_e_5072_, v___x_5078_, v___x_5079_);
if (v___x_5080_ == 0)
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5081_);
return v___x_5082_;
}
else
{
lean_object* v___x_5083_; lean_object* v_p_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5083_ = l_Lean_Expr_appFn_x21(v_e_5072_);
v_p_5084_ = l_Lean_Expr_appArg_x21(v___x_5083_);
lean_dec_ref(v___x_5083_);
v___x_5085_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_5084_);
v___x_5086_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v_p_5084_, v___x_5085_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5274_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5089_ = v___x_5086_;
v_isShared_5090_ = v_isSharedCheck_5274_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5086_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5274_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
if (lean_obj_tag(v_a_5087_) == 1)
{
lean_object* v_val_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_del_object(v___x_5089_);
v_val_5091_ = lean_ctor_get(v_a_5087_, 0);
lean_inc(v_val_5091_);
lean_dec_ref(v_a_5087_);
v___x_5092_ = l_Lean_Expr_appArg_x21(v_e_5072_);
lean_inc_ref(v___x_5092_);
v___x_5093_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_NatOffset_fromExpr_x3f___redArg(v___x_5092_, v___x_5085_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5261_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5096_ = v___x_5093_;
v_isShared_5097_ = v_isSharedCheck_5261_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5093_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5261_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
if (lean_obj_tag(v_a_5094_) == 1)
{
lean_del_object(v___x_5096_);
if (lean_obj_tag(v_val_5091_) == 0)
{
lean_object* v_val_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5148_; 
lean_dec_ref(v___x_5092_);
v_val_5098_ = lean_ctor_get(v_a_5094_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v_a_5094_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5100_ = v_a_5094_;
v_isShared_5101_ = v_isSharedCheck_5148_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_val_5098_);
lean_dec(v_a_5094_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5148_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
if (lean_obj_tag(v_val_5098_) == 0)
{
lean_object* v_n_5102_; lean_object* v_n_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5133_; 
lean_dec_ref(v_p_5084_);
v_n_5102_ = lean_ctor_get(v_val_5091_, 0);
lean_inc(v_n_5102_);
lean_dec_ref(v_val_5091_);
v_n_5103_ = lean_ctor_get(v_val_5098_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_val_5098_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5105_ = v_val_5098_;
v_isShared_5106_ = v_isSharedCheck_5133_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_n_5103_);
lean_dec(v_val_5098_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5133_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5107_ = lean_nat_sub(v_n_5102_, v_n_5103_);
lean_dec(v_n_5103_);
lean_dec(v_n_5102_);
v___x_5108_ = l_Lean_mkNatLit(v___x_5107_);
lean_inc_ref(v___x_5108_);
v___x_5109_ = l_Lean_Meta_mkEqRefl(v___x_5108_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5124_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5112_ = v___x_5109_;
v_isShared_5113_ = v_isSharedCheck_5124_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5109_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5124_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 0, v_a_5110_);
v___x_5115_ = v___x_5100_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
lean_object* v___x_5116_; lean_object* v___x_5118_; 
v___x_5116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5116_, 0, v___x_5108_);
lean_ctor_set(v___x_5116_, 1, v___x_5115_);
lean_ctor_set_uint8(v___x_5116_, sizeof(void*)*2, v___x_5080_);
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 0, v___x_5116_);
v___x_5118_ = v___x_5105_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5120_; 
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 0, v___x_5118_);
v___x_5120_ = v___x_5112_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_dec_ref(v___x_5108_);
lean_del_object(v___x_5105_);
lean_del_object(v___x_5100_);
v_a_5125_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5109_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5109_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
else
{
lean_object* v_n_5134_; lean_object* v_e_5135_; lean_object* v_o_5136_; lean_object* v_n_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
lean_del_object(v___x_5100_);
v_n_5134_ = lean_ctor_get(v_val_5091_, 0);
lean_inc(v_n_5134_);
lean_dec_ref(v_val_5091_);
v_e_5135_ = lean_ctor_get(v_val_5098_, 0);
lean_inc_ref(v_e_5135_);
v_o_5136_ = lean_ctor_get(v_val_5098_, 1);
lean_inc_ref(v_o_5136_);
v_n_5137_ = lean_ctor_get(v_val_5098_, 2);
lean_inc(v_n_5137_);
lean_dec_ref(v_val_5098_);
v___x_5138_ = lean_nat_sub(v_n_5134_, v_n_5137_);
lean_dec(v_n_5137_);
lean_dec(v_n_5134_);
v___x_5139_ = l_Lean_mkNatLit(v___x_5138_);
lean_inc_ref(v_e_5135_);
v___x_5140_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5139_, v_e_5135_);
v___x_5141_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__1));
v___x_5142_ = lean_unsigned_to_nat(3u);
v___x_5143_ = lean_mk_empty_array_with_capacity(v___x_5142_);
v___x_5144_ = lean_array_push(v___x_5143_, v_p_5084_);
v___x_5145_ = lean_array_push(v___x_5144_, v_e_5135_);
v___x_5146_ = lean_array_push(v___x_5145_, v_o_5136_);
v___x_5147_ = l_Nat_applySimprocConst___redArg(v___x_5140_, v___x_5141_, v___x_5146_, v_a_5076_);
lean_dec_ref(v___x_5146_);
return v___x_5147_;
}
}
}
else
{
lean_object* v_val_5149_; lean_object* v_e_5150_; lean_object* v_o_5151_; lean_object* v_n_5152_; lean_object* v___y_5154_; 
lean_dec_ref(v_p_5084_);
v_val_5149_ = lean_ctor_get(v_a_5094_, 0);
lean_inc(v_val_5149_);
lean_dec_ref(v_a_5094_);
v_e_5150_ = lean_ctor_get(v_val_5091_, 0);
lean_inc_ref(v_e_5150_);
v_o_5151_ = lean_ctor_get(v_val_5091_, 1);
lean_inc_ref(v_o_5151_);
v_n_5152_ = lean_ctor_get(v_val_5091_, 2);
lean_inc(v_n_5152_);
lean_dec_ref(v_val_5091_);
if (lean_obj_tag(v_val_5149_) == 0)
{
lean_object* v_n_5174_; uint8_t v___x_5175_; 
v_n_5174_ = lean_ctor_get(v_val_5149_, 0);
lean_inc(v_n_5174_);
lean_dec_ref(v_val_5149_);
v___x_5175_ = lean_nat_dec_le(v_n_5152_, v_n_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; 
lean_inc_ref(v_o_5151_);
lean_inc_ref(v___x_5092_);
v___x_5176_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v___x_5092_, v_o_5151_);
v___x_5177_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5176_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5178_);
lean_dec_ref(v___x_5177_);
v___x_5179_ = lean_nat_sub(v_n_5152_, v_n_5174_);
lean_dec(v_n_5174_);
lean_dec(v_n_5152_);
v___x_5180_ = l_Lean_mkNatLit(v___x_5179_);
lean_inc_ref(v_e_5150_);
v___x_5181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5150_, v___x_5180_);
v___x_5182_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__5));
v___x_5183_ = lean_unsigned_to_nat(4u);
v___x_5184_ = lean_mk_empty_array_with_capacity(v___x_5183_);
v___x_5185_ = lean_array_push(v___x_5184_, v_o_5151_);
v___x_5186_ = lean_array_push(v___x_5185_, v___x_5092_);
v___x_5187_ = lean_array_push(v___x_5186_, v_a_5178_);
v___x_5188_ = lean_array_push(v___x_5187_, v_e_5150_);
v___x_5189_ = l_Nat_applySimprocConst___redArg(v___x_5181_, v___x_5182_, v___x_5188_, v_a_5076_);
lean_dec_ref(v___x_5188_);
return v___x_5189_;
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_n_5174_);
lean_dec(v_n_5152_);
lean_dec_ref(v_o_5151_);
lean_dec_ref(v_e_5150_);
lean_dec_ref(v___x_5092_);
v_a_5190_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5177_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5177_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
else
{
uint8_t v___x_5198_; 
v___x_5198_ = lean_nat_dec_eq(v_n_5152_, v_n_5174_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = lean_nat_sub(v_n_5174_, v_n_5152_);
lean_dec(v_n_5152_);
lean_dec(v_n_5174_);
v___x_5200_ = l_Lean_mkNatLit(v___x_5199_);
lean_inc_ref(v_e_5150_);
v___x_5201_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5150_, v___x_5200_);
v___y_5154_ = v___x_5201_;
goto v___jp_5153_;
}
else
{
lean_dec(v_n_5174_);
lean_dec(v_n_5152_);
lean_inc_ref(v_e_5150_);
v___y_5154_ = v_e_5150_;
goto v___jp_5153_;
}
}
}
else
{
lean_object* v_e_5202_; lean_object* v_o_5203_; lean_object* v_n_5204_; lean_object* v___y_5206_; uint8_t v___x_5228_; 
lean_dec_ref(v___x_5092_);
v_e_5202_ = lean_ctor_get(v_val_5149_, 0);
lean_inc_ref(v_e_5202_);
v_o_5203_ = lean_ctor_get(v_val_5149_, 1);
lean_inc_ref(v_o_5203_);
v_n_5204_ = lean_ctor_get(v_val_5149_, 2);
lean_inc(v_n_5204_);
lean_dec_ref(v_val_5149_);
v___x_5228_ = lean_nat_dec_le(v_n_5152_, v_n_5204_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
lean_inc_ref(v_o_5151_);
lean_inc_ref(v_o_5203_);
v___x_5229_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5203_, v_o_5151_);
v___x_5230_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5229_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref(v___x_5230_);
v___x_5232_ = lean_nat_sub(v_n_5152_, v_n_5204_);
lean_dec(v_n_5204_);
lean_dec(v_n_5152_);
v___x_5233_ = l_Lean_mkNatLit(v___x_5232_);
lean_inc_ref(v_e_5150_);
v___x_5234_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5150_, v___x_5233_);
lean_inc_ref(v_e_5202_);
v___x_5235_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v___x_5234_, v_e_5202_);
v___x_5236_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__9));
v___x_5237_ = lean_unsigned_to_nat(5u);
v___x_5238_ = lean_mk_empty_array_with_capacity(v___x_5237_);
v___x_5239_ = lean_array_push(v___x_5238_, v_e_5150_);
v___x_5240_ = lean_array_push(v___x_5239_, v_e_5202_);
v___x_5241_ = lean_array_push(v___x_5240_, v_o_5151_);
v___x_5242_ = lean_array_push(v___x_5241_, v_o_5203_);
v___x_5243_ = lean_array_push(v___x_5242_, v_a_5231_);
v___x_5244_ = l_Nat_applySimprocConst___redArg(v___x_5235_, v___x_5236_, v___x_5243_, v_a_5076_);
lean_dec_ref(v___x_5243_);
return v___x_5244_;
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_dec(v_n_5204_);
lean_dec_ref(v_o_5203_);
lean_dec_ref(v_e_5202_);
lean_dec(v_n_5152_);
lean_dec_ref(v_o_5151_);
lean_dec_ref(v_e_5150_);
v_a_5245_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5230_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5230_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
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
uint8_t v___x_5253_; 
v___x_5253_ = lean_nat_dec_eq(v_n_5152_, v_n_5204_);
if (v___x_5253_ == 0)
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5254_ = lean_nat_sub(v_n_5204_, v_n_5152_);
lean_dec(v_n_5152_);
lean_dec(v_n_5204_);
v___x_5255_ = l_Lean_mkNatLit(v___x_5254_);
lean_inc_ref(v_e_5202_);
v___x_5256_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkAddNat(v_e_5202_, v___x_5255_);
v___y_5206_ = v___x_5256_;
goto v___jp_5205_;
}
else
{
lean_dec(v_n_5204_);
lean_dec(v_n_5152_);
lean_inc_ref(v_e_5202_);
v___y_5206_ = v_e_5202_;
goto v___jp_5205_;
}
}
v___jp_5205_:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_inc_ref(v_o_5203_);
lean_inc_ref(v_o_5151_);
v___x_5207_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5151_, v_o_5203_);
v___x_5208_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5207_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5208_);
lean_inc_ref(v_e_5150_);
v___x_5210_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkSubNat(v_e_5150_, v___y_5206_);
v___x_5211_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__7));
v___x_5212_ = lean_unsigned_to_nat(5u);
v___x_5213_ = lean_mk_empty_array_with_capacity(v___x_5212_);
v___x_5214_ = lean_array_push(v___x_5213_, v_e_5150_);
v___x_5215_ = lean_array_push(v___x_5214_, v_e_5202_);
v___x_5216_ = lean_array_push(v___x_5215_, v_o_5151_);
v___x_5217_ = lean_array_push(v___x_5216_, v_o_5203_);
v___x_5218_ = lean_array_push(v___x_5217_, v_a_5209_);
v___x_5219_ = l_Nat_applySimprocConst___redArg(v___x_5210_, v___x_5211_, v___x_5218_, v_a_5076_);
lean_dec_ref(v___x_5218_);
return v___x_5219_;
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_dec_ref(v___y_5206_);
lean_dec_ref(v_o_5203_);
lean_dec_ref(v_e_5202_);
lean_dec_ref(v_o_5151_);
lean_dec_ref(v_e_5150_);
v_a_5220_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5208_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5208_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
}
v___jp_5153_:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; 
lean_inc_ref(v___x_5092_);
lean_inc_ref(v_o_5151_);
v___x_5155_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkLENat(v_o_5151_, v___x_5092_);
v___x_5156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkOfDecideEqTrue(v___x_5155_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_a_5157_);
lean_dec_ref(v___x_5156_);
v___x_5158_ = ((lean_object*)(l_Nat_reduceSubDiff___redArg___closed__3));
v___x_5159_ = lean_unsigned_to_nat(4u);
v___x_5160_ = lean_mk_empty_array_with_capacity(v___x_5159_);
v___x_5161_ = lean_array_push(v___x_5160_, v_e_5150_);
v___x_5162_ = lean_array_push(v___x_5161_, v_o_5151_);
v___x_5163_ = lean_array_push(v___x_5162_, v___x_5092_);
v___x_5164_ = lean_array_push(v___x_5163_, v_a_5157_);
v___x_5165_ = l_Nat_applySimprocConst___redArg(v___y_5154_, v___x_5158_, v___x_5164_, v_a_5076_);
lean_dec_ref(v___x_5164_);
return v___x_5165_;
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5173_; 
lean_dec_ref(v___y_5154_);
lean_dec_ref(v_o_5151_);
lean_dec_ref(v_e_5150_);
lean_dec_ref(v___x_5092_);
v_a_5166_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5168_ = v___x_5156_;
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5156_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
}
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5259_; 
lean_dec(v_a_5094_);
lean_dec_ref(v___x_5092_);
lean_dec(v_val_5091_);
lean_dec_ref(v_p_5084_);
v___x_5257_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v___x_5257_);
v___x_5259_ = v___x_5096_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5257_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
else
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_dec_ref(v___x_5092_);
lean_dec(v_val_5091_);
lean_dec_ref(v_p_5084_);
v_a_5262_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5093_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5093_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
else
{
lean_object* v___x_5270_; lean_object* v___x_5272_; 
lean_dec(v_a_5087_);
lean_dec_ref(v_p_5084_);
v___x_5270_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5090_ == 0)
{
lean_ctor_set(v___x_5089_, 0, v___x_5270_);
v___x_5272_ = v___x_5089_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec_ref(v_p_5084_);
v_a_5275_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5086_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5086_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___redArg___boxed(lean_object* v_e_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Nat_reduceSubDiff___redArg(v_e_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_);
lean_dec(v_a_5287_);
lean_dec_ref(v_a_5286_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec_ref(v_e_5283_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff(lean_object* v_e_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Nat_reduceSubDiff___redArg(v_e_5290_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___boxed(lean_object* v_e_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Nat_reduceSubDiff(v_e_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_);
lean_dec(v_a_5307_);
lean_dec_ref(v_a_5306_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
lean_dec_ref(v_e_5300_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_, &l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19__once, _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_);
v___x_5317_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5318_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5315_, v___x_5316_, v___x_5317_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19____boxed(lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_();
return v_res_5320_;
}
}
static lean_object* _init_l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5321_ = lean_alloc_closure((void*)(l_Nat_reduceSubDiff___boxed), 9, 0);
v___x_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5325_ = 1;
v___x_5326_ = lean_obj_once(&l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_, &l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once, _init_l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_);
v___x_5327_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5324_, v___x_5325_, v___x_5326_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21____boxed(lean_object* v_a_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5331_; uint8_t v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_));
v___x_5332_ = 1;
v___x_5333_ = lean_obj_once(&l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_, &l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21__once, _init_l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_);
v___x_5334_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5331_, v___x_5332_, v___x_5333_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23____boxed(lean_object* v_a_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
return v_res_5336_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__5(void){
_start:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5346_ = lean_box(0);
v___x_5347_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__4));
v___x_5348_ = l_Lean_mkConst(v___x_5347_, v___x_5346_);
return v___x_5348_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__8(void){
_start:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5353_ = lean_box(0);
v___x_5354_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__7));
v___x_5355_ = l_Lean_mkConst(v___x_5354_, v___x_5353_);
return v___x_5355_;
}
}
static lean_object* _init_l_Nat_reduceDvd___redArg___closed__11(void){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5360_ = lean_box(0);
v___x_5361_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__10));
v___x_5362_ = l_Lean_mkConst(v___x_5361_, v___x_5360_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg(lean_object* v_e_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_){
_start:
{
lean_object* v___x_5369_; 
v___x_5369_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5363_, v_a_5365_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5490_; 
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5372_ = v___x_5369_;
v_isShared_5373_ = v_isSharedCheck_5490_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5369_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5490_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5379_; uint8_t v___x_5380_; 
v___x_5379_ = l_Lean_Expr_cleanupAnnotations(v_a_5370_);
v___x_5380_ = l_Lean_Expr_isApp(v___x_5379_);
if (v___x_5380_ == 0)
{
lean_dec_ref(v___x_5379_);
goto v___jp_5374_;
}
else
{
lean_object* v_arg_5381_; lean_object* v___x_5382_; uint8_t v___x_5383_; 
v_arg_5381_ = lean_ctor_get(v___x_5379_, 1);
lean_inc_ref(v_arg_5381_);
v___x_5382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5379_);
v___x_5383_ = l_Lean_Expr_isApp(v___x_5382_);
if (v___x_5383_ == 0)
{
lean_dec_ref(v___x_5382_);
lean_dec_ref(v_arg_5381_);
goto v___jp_5374_;
}
else
{
lean_object* v_arg_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v_arg_5384_ = lean_ctor_get(v___x_5382_, 1);
lean_inc_ref(v_arg_5384_);
v___x_5385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5382_);
v___x_5386_ = l_Lean_Expr_isApp(v___x_5385_);
if (v___x_5386_ == 0)
{
lean_dec_ref(v___x_5385_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
goto v___jp_5374_;
}
else
{
lean_object* v_arg_5387_; lean_object* v___x_5388_; uint8_t v___x_5389_; 
v_arg_5387_ = lean_ctor_get(v___x_5385_, 1);
lean_inc_ref(v_arg_5387_);
v___x_5388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5385_);
v___x_5389_ = l_Lean_Expr_isApp(v___x_5388_);
if (v___x_5389_ == 0)
{
lean_dec_ref(v___x_5388_);
lean_dec_ref(v_arg_5387_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
goto v___jp_5374_;
}
else
{
lean_object* v___x_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; 
v___x_5390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5388_);
v___x_5391_ = ((lean_object*)(l_Nat_reduceDvd___redArg___closed__2));
v___x_5392_ = l_Lean_Expr_isConstOf(v___x_5390_, v___x_5391_);
lean_dec_ref(v___x_5390_);
if (v___x_5392_ == 0)
{
lean_dec_ref(v_arg_5387_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
goto v___jp_5374_;
}
else
{
lean_object* v___x_5393_; lean_object* v___x_5394_; 
lean_del_object(v___x_5372_);
v___x_5393_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__5, &l_Nat_reduceDvd___redArg___closed__5_once, _init_l_Nat_reduceDvd___redArg___closed__5);
v___x_5394_ = l_Lean_Meta_matchesInstance(v_arg_5387_, v___x_5393_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5481_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5397_ = v___x_5394_;
v_isShared_5398_ = v_isSharedCheck_5481_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5394_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5481_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
uint8_t v___x_5399_; 
v___x_5399_ = lean_unbox(v_a_5395_);
lean_dec(v_a_5395_);
if (v___x_5399_ == 0)
{
lean_object* v___x_5400_; lean_object* v___x_5402_; 
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v___x_5400_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 0, v___x_5400_);
v___x_5402_ = v___x_5397_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5400_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
else
{
lean_object* v___x_5404_; 
lean_del_object(v___x_5397_);
v___x_5404_ = l_Lean_Meta_getNatValue_x3f(v_arg_5384_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5472_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5407_ = v___x_5404_;
v_isShared_5408_ = v_isSharedCheck_5472_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5404_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5472_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
if (lean_obj_tag(v_a_5405_) == 1)
{
lean_object* v_val_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5467_; 
lean_del_object(v___x_5407_);
v_val_5409_ = lean_ctor_get(v_a_5405_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v_a_5405_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5411_ = v_a_5405_;
v_isShared_5412_ = v_isSharedCheck_5467_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_val_5409_);
lean_dec(v_a_5405_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5467_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; 
v___x_5413_ = l_Lean_Meta_getNatValue_x3f(v_arg_5381_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5458_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5416_ = v___x_5413_;
v_isShared_5417_ = v_isSharedCheck_5458_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_a_5414_);
lean_dec(v___x_5413_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5458_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
if (lean_obj_tag(v_a_5414_) == 1)
{
lean_object* v_val_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5453_; 
v_val_5418_ = lean_ctor_get(v_a_5414_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v_a_5414_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5420_ = v_a_5414_;
v_isShared_5421_ = v_isSharedCheck_5453_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_val_5418_);
lean_dec(v_a_5414_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5453_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; uint8_t v___x_5424_; 
v___x_5422_ = lean_nat_mod(v_val_5418_, v_val_5409_);
lean_dec(v_val_5409_);
lean_dec(v_val_5418_);
v___x_5423_ = lean_unsigned_to_nat(0u);
v___x_5424_ = lean_nat_dec_eq(v___x_5422_, v___x_5423_);
lean_dec(v___x_5422_);
if (v___x_5424_ == 0)
{
lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5430_; 
v___x_5425_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__5, &l_Nat_reduceEqDiff___redArg___closed__5_once, _init_l_Nat_reduceEqDiff___redArg___closed__5);
v___x_5426_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__8, &l_Nat_reduceDvd___redArg___closed__8_once, _init_l_Nat_reduceDvd___redArg___closed__8);
v___x_5427_ = l_Lean_eagerReflBoolTrue;
v___x_5428_ = l_Lean_mkApp3(v___x_5426_, v_arg_5384_, v_arg_5381_, v___x_5427_);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 0, v___x_5428_);
v___x_5430_ = v___x_5420_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5428_);
v___x_5430_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5433_; 
v___x_5431_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5431_, 0, v___x_5425_);
lean_ctor_set(v___x_5431_, 1, v___x_5430_);
lean_ctor_set_uint8(v___x_5431_, sizeof(void*)*2, v___x_5392_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set_tag(v___x_5411_, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5431_);
v___x_5433_ = v___x_5411_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5431_);
v___x_5433_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5435_; 
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v___x_5433_);
v___x_5435_ = v___x_5416_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
else
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5444_; 
v___x_5439_ = lean_obj_once(&l_Nat_reduceEqDiff___redArg___closed__11, &l_Nat_reduceEqDiff___redArg___closed__11_once, _init_l_Nat_reduceEqDiff___redArg___closed__11);
v___x_5440_ = lean_obj_once(&l_Nat_reduceDvd___redArg___closed__11, &l_Nat_reduceDvd___redArg___closed__11_once, _init_l_Nat_reduceDvd___redArg___closed__11);
v___x_5441_ = l_Lean_eagerReflBoolTrue;
v___x_5442_ = l_Lean_mkApp3(v___x_5440_, v_arg_5384_, v_arg_5381_, v___x_5441_);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 0, v___x_5442_);
v___x_5444_ = v___x_5420_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v___x_5442_);
v___x_5444_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
lean_object* v___x_5445_; lean_object* v___x_5447_; 
v___x_5445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5445_, 0, v___x_5439_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
lean_ctor_set_uint8(v___x_5445_, sizeof(void*)*2, v___x_5392_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set_tag(v___x_5411_, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5445_);
v___x_5447_ = v___x_5411_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
lean_object* v___x_5449_; 
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v___x_5447_);
v___x_5449_ = v___x_5416_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
}
}
else
{
lean_object* v___x_5454_; lean_object* v___x_5456_; 
lean_dec(v_a_5414_);
lean_del_object(v___x_5411_);
lean_dec(v_val_5409_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v___x_5454_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v___x_5454_);
v___x_5456_ = v___x_5416_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5454_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_del_object(v___x_5411_);
lean_dec(v_val_5409_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v_a_5459_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5413_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5413_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
}
else
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
lean_dec(v_a_5405_);
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v___x_5468_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 0, v___x_5468_);
v___x_5470_ = v___x_5407_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v_a_5473_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v___x_5404_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5404_);
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
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec_ref(v_arg_5384_);
lean_dec_ref(v_arg_5381_);
v_a_5482_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5394_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5394_);
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
}
}
}
v___jp_5374_:
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
v___x_5375_ = ((lean_object*)(l_Nat_reduceBinPred___redArg___closed__0));
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 0, v___x_5375_);
v___x_5377_ = v___x_5372_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
v_a_5491_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5369_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5369_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___redArg___boxed(lean_object* v_e_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_){
_start:
{
lean_object* v_res_5505_; 
v_res_5505_ = l_Nat_reduceDvd___redArg(v_e_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
return v_res_5505_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd(lean_object* v_e_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_){
_start:
{
lean_object* v___x_5515_; 
v___x_5515_ = l_Nat_reduceDvd___redArg(v_e_5506_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_);
return v___x_5515_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___boxed(lean_object* v_e_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_){
_start:
{
lean_object* v_res_5525_; 
v_res_5525_ = l_Nat_reduceDvd(v_e_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_);
lean_dec(v_a_5523_);
lean_dec_ref(v_a_5522_);
lean_dec(v_a_5521_);
lean_dec_ref(v_a_5520_);
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
lean_dec(v_a_5517_);
return v_res_5525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5546_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5547_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5544_, v___x_5545_, v___x_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19____boxed(lean_object* v_a_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_();
return v_res_5549_;
}
}
static lean_object* _init_l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_(void){
_start:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = lean_alloc_closure((void*)(l_Nat_reduceDvd___boxed), 9, 0);
v___x_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5550_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_(){
_start:
{
lean_object* v___x_5553_; uint8_t v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5554_ = 1;
v___x_5555_ = lean_obj_once(&l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_, &l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once, _init_l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_);
v___x_5556_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5553_, v___x_5554_, v___x_5555_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21____boxed(lean_object* v_a_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_(){
_start:
{
lean_object* v___x_5560_; uint8_t v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_));
v___x_5561_ = 1;
v___x_5562_ = lean_obj_once(&l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_, &l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21__once, _init_l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_);
v___x_5563_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5560_, v___x_5561_, v___x_5562_);
return v___x_5563_;
}
}
LEAN_EXPORT lean_object* l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23____boxed(lean_object* v_a_5564_){
_start:
{
lean_object* v_res_5565_; 
v_res_5565_ = l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
return v_res_5565_;
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
res = l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceSucc___regBuiltin_Nat_reduceSucc_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2655965677____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAdd_declare__26_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceAdd___regBuiltin_Nat_reduceAdd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2624385985____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMul_declare__31_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceMul___regBuiltin_Nat_reduceMul_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2592700480____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSub_declare__36_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceSub___regBuiltin_Nat_reduceSub_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2812229159____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDiv_declare__41_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceDiv___regBuiltin_Nat_reduceDiv_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1932328560____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceMod_declare__46_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceMod___regBuiltin_Nat_reduceMod_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3686920086____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reducePow_declare__51_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reducePow___regBuiltin_Nat_reducePow_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_879423217____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceAnd_declare__56_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceAnd___regBuiltin_Nat_reduceAnd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1489869653____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceXor_declare__61_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceXor___regBuiltin_Nat_reduceXor_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1367164213____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceOr_declare__66_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceOr___regBuiltin_Nat_reduceOr_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1261338399____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftLeft_declare__71_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceShiftLeft___regBuiltin_Nat_reduceShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_4292340164____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceShiftRight_declare__76_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceShiftRight___regBuiltin_Nat_reduceShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3351081446____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGcd_declare__81_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceGcd___regBuiltin_Nat_reduceGcd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2337750513____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLT_declare__86_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceLT___regBuiltin_Nat_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_520351057____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceGT_declare__91_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceGT___regBuiltin_Nat_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_944496727____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBEq_declare__96_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBEq___regBuiltin_Nat_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_541140047____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBNe_declare__101_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBNe___regBuiltin_Nat_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_3571880001____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_isValue_declare__106_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_isValue___regBuiltin_Nat_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1221253431____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0__Nat_mkBEqNatInstance);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceEqDiff_declare__165_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceEqDiff___regBuiltin_Nat_reduceEqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1265281291____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBeqDiff_declare__170_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBeqDiff___regBuiltin_Nat_reduceBeqDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2636786403____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceBneDiff_declare__175_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceBneDiff___regBuiltin_Nat_reduceBneDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_1751779906____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceLeDiff_declare__183_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_20_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_22_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceLeDiff___regBuiltin_Nat_reduceLeDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2466209926____hygCtx___hyg_24_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceSubDiff_declare__188_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceSubDiff___regBuiltin_Nat_reduceSubDiff_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2719302818____hygCtx___hyg_23_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_0____regBuiltin_Nat_reduceDvd_declare__193_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_21_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Nat_reduceDvd___regBuiltin_Nat_reduceDvd_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat_2209126869____hygCtx___hyg_23_();
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
